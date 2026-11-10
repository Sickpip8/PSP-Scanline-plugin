#include <pspkernel.h>
#include <pspdisplay.h>
#include <pspctrl.h>
#include <psputils.h>
#include <systemctrl.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>

PSP_MODULE_INFO("ARK4_Scanlines", 0x1000, 1, 0);
PSP_MAIN_THREAD_ATTR(0);

/*
 * Scanline overlay for ARK-4.
 *
 * Controls (kernel-only NOTE button):
 *   tap NOTE            toggle on/off
 *   hold NOTE + UP      50% dark lines
 *   hold NOTE + DOWN    75% dark lines
 *
 * Design:
 *  - Primary path: inline-hook the display driver's "set frame buffer"
 *    functions (user and internal variants) and darken the buffer the game is
 *    about to display BEFORE it becomes visible. An inline hook (patching the
 *    function's first two instructions) catches kernel-mode callers such as
 *    POPS, which a syscall-table patch cannot.
 *  - Fallback path: if nothing is submitted per frame, a vblank thread polls
 *    the visible buffer instead (this path can lose a race with the LCD beam).
 *  - Both paths share per-row hashes of "the row as we left it", so a row is
 *    darkened once per redraw and never fades to black. The same hashes let
 *    us undo the effect on disable / opacity change / unload.
 *  - Reads of VRAM go through the cache (much faster than uncached reads);
 *    writes go through the uncached alias.
 *
 * Set DEBUG_LOG to 0 once everything works to stop writing the log file.
 */

#ifndef DEBUG_LOG
#define DEBUG_LOG   1
#endif
#ifndef DEBUG_MARKER
#define DEBUG_MARKER 1               /* tiny corner marker: green = hook path, red = polling path */
#endif
#define LOG_EVERY_US    2000000      /* log write interval */
#define POLL_US         1500         /* polling interval for the fallback path */
#define FULL_EVERY_US   16000        /* full pass at least this often when polling */
#define HOOK_ACTIVE_US  70000        /* hooks count as "feeding us" if called this recently */

#define SCREEN_W    480
#define SCREEN_H    272
#define ODD_ROWS    (SCREEN_H / 2)   /* rows 1,3,...,271 */
#define NUM_SLOTS   4                /* enough for triple buffering + 1 */
#define HASH_SEED   2166136261u

#define NID_SETFRAMEBUF          0x289D82FE  /* sceDisplay_Service / sceDisplay        */
#define NID_SETFRAMEBUF_INTERNAL 0x7ED59BC4  /* sceDisplay_Service / sceDisplay_driver */

#ifndef CACHED
#define CACHED(p)   ((uint32_t *)((uintptr_t)(p) & ~0x40000000u))
#endif
#ifndef UNCACHED
#define UNCACHED(p) ((uint32_t *)((uintptr_t)(p) | 0x40000000u))
#endif
#ifndef PHYS
/* Canonical key for an address: strips the uncached/user alias bits. */
#define PHYS(p) ((uintptr_t)(p) & 0x1FFFFFFFu)
#endif
#ifndef ADDR_OK
/* Only touch real VRAM / RAM; a bad pointer in kernel mode crashes the PSP. */
#define ADDR_OK(phys, bytes) \
    (((phys) >= 0x04000000u && (phys) + (bytes) <= 0x04200000u) || \
     ((phys) >= 0x08000000u && (phys) + (bytes) <= 0x0C000000u))
#endif

#define _lw(a)    (*(volatile uint32_t *)(uintptr_t)(a))
#define _sw(v, a) (*(volatile uint32_t *)(uintptr_t)(a) = (v))

static volatile int running        = 1;
static volatile int enabled        = 1;
static volatile int darkness_shift = 1;   /* 1 = 50% dark, 2 = 75% dark */

static SceUID thid_input  = -1;
static SceUID thid_render = -1;
static SceUID lock_sema   = -1;

/* statistics for the debug log */
static volatile unsigned calls_a, calls_b, fallback_calls, busy_skips;
static volatile unsigned last_addr, last_stride, last_fmt, last_us, max_us;
static volatile unsigned hook_count;

/* ------------------------------------------------------------------ */
/* Pixel format tables (per-pixel constants; 16-bit ones get replicated */
/* into both halves of a 32-bit word at use).                          */
/* Index [n] is for a shift of n bits (1 or 2).                        */
/* ------------------------------------------------------------------ */
typedef struct {
    int      bpp;        /* bytes per pixel                              */
    uint32_t alpha;      /* alpha bits, preserved untouched              */
    uint32_t dark[3];    /* mask applied after  >> n  (darken)           */
    uint32_t keep[3];    /* mask applied after  << n  (restore)          */
    uint32_t fill[3];    /* low bits set after  << n  (restore, rounds up) */
} FormatInfo;

static const FormatInfo formats[4] = {
    [PSP_DISPLAY_PIXEL_FORMAT_565]  = { 2, 0x0000,
        {0, 0x7BEF, 0x39E7}, {0, 0xF7DE, 0xE79C}, {0, 0x0821, 0x1863} },
    [PSP_DISPLAY_PIXEL_FORMAT_5551] = { 2, 0x8000,
        {0, 0x3DEF, 0x1CE7}, {0, 0x7BDE, 0x739C}, {0, 0x0421, 0x0C63} },
    [PSP_DISPLAY_PIXEL_FORMAT_4444] = { 2, 0xF000,
        {0, 0x0777, 0x0333}, {0, 0x0EEE, 0x0CCC}, {0, 0x0111, 0x0333} },
    [PSP_DISPLAY_PIXEL_FORMAT_8888] = { 4, 0xFF000000u,
        {0, 0x007F7F7Fu, 0x003F3F3Fu}, {0, 0x00FEFEFEu, 0x00FCFCFCu},
        {0, 0x00010101u, 0x00030303u} },
};

static inline uint32_t rep(const FormatInfo *f, uint32_t v)
{
    return (f->bpp == 2) ? (v | (v << 16)) : v;
}

static inline uint32_t hash_word(uint32_t h, uint32_t w)
{
    return (h ^ w) * 16777619u;
}

/* ------------------------------------------------------------------ */
/* Per-framebuffer state                                               */
/* ------------------------------------------------------------------ */
typedef struct {
    uintptr_t addr;              /* PHYS() address, 0 = slot unused       */
    int       format;
    int       stride_px;
    int       shift;             /* shift currently applied, 0 = none     */
    uint32_t  hash[ODD_ROWS];    /* hash of each odd row as we left it    */
} Slot;

static Slot slots[NUM_SLOTS];
static int  next_victim;
static uint32_t linebuf[SCREEN_W];   /* protected by lock_sema */

static void lock(void)
{
    if (lock_sema >= 0) sceKernelWaitSema(lock_sema, 1, NULL);
}

static void unlock(void)
{
    if (lock_sema >= 0) sceKernelSignalSema(lock_sema, 1);
}

static int current_want(void)
{
    int sh;
    if (!enabled)
        return 0;
    sh = darkness_shift;
    if (sh < 1) sh = 1;
    if (sh > 2) sh = 2;
    return sh;
}

static Slot *find_slot(uintptr_t addr, int format, int stride_px)
{
    int i;
    Slot *s;

    for (i = 0; i < NUM_SLOTS; i++) {
        if (slots[i].addr == addr && slots[i].format == format &&
            slots[i].stride_px == stride_px)
            return &slots[i];
    }
    s = &slots[next_victim];
    next_victim = (next_victim + 1) % NUM_SLOTS;
    memset(s, 0, sizeof(*s));
    s->addr      = addr;
    s->format    = format;
    s->stride_px = stride_px;
    return s;
}

/*
 * restore == 0: darken every odd row the game has (re)drawn since last time.
 * restore == 1: undo our darkening on rows that are still exactly as we left
 *               them (rows the game has redrawn are already correct).
 *
 * Cache handling: before reading a row we write back + invalidate its cache
 * lines (so we see what the GE/CPU really put in VRAM, and never discard a
 * dirty line), then read through the fast cached alias and write through the
 * uncached alias. After writing we invalidate again so no stale line of the
 * old pixels can later be written back over our result.
 */
static void convert_frame(Slot *s, int restore)
{
    const FormatInfo *f = &formats[s->format];
    const int words  = SCREEN_W * f->bpp / 4;
    const int stride = s->stride_px * f->bpp / 4;
    const int sh     = s->shift;
    const uint32_t alpha = rep(f, f->alpha);
    const uint32_t dark  = rep(f, f->dark[sh]);
    const uint32_t keep  = rep(f, f->keep[sh]);
    const uint32_t fill  = rep(f, f->fill[sh]);
    uint32_t *rbase = CACHED(s->addr);
    uint32_t *wbase = UNCACHED(s->addr);
    int i, x;

    for (i = 0; i < ODD_ROWS; i++) {
        const size_t off = (size_t)(2 * i + 1) * stride;
        const uint32_t *rrow = rbase + off;
        uint32_t *wrow = wbase + off;
        uint32_t h = HASH_SEED;
        int wrote = 0;

        sceKernelDcacheWritebackInvalidateRange((void *)rrow, words * 4);

        /* One read pass: copy to line buffer and hash it. */
        for (x = 0; x < words; x++) {
            uint32_t w = rrow[x];
            linebuf[x] = w;
            h = hash_word(h, w);
        }
        h |= 1;   /* never 0, so 0 can mean "not darkened by us" */

        if (restore) {
            if (h == s->hash[i]) {
                for (x = 0; x < words; x++) {
                    uint32_t w = linebuf[x];
                    wrow[x] = ((w << sh) & keep) | fill | (w & alpha);
                }
                wrote = 1;
            }
            s->hash[i] = 0;
        } else {
            if (h == s->hash[i])
                continue;   /* untouched since we darkened it */

            h = HASH_SEED;
            for (x = 0; x < words; x++) {
                uint32_t w = linebuf[x];
                uint32_t o = ((w >> sh) & dark) | (w & alpha);
                wrow[x] = o;
                h = hash_word(h, o);
            }
            s->hash[i] = h | 1;
            wrote = 1;
        }

        if (wrote)
            sceKernelDcacheWritebackInvalidateRange((void *)rrow, words * 4);
    }
}

static Slot *lookup_slot(uintptr_t addr, int format, int stride_px)
{
    int i;
    for (i = 0; i < NUM_SLOTS; i++) {
        if (slots[i].addr == addr && slots[i].format == format &&
            slots[i].stride_px == stride_px)
            return &slots[i];
    }
    return NULL;
}

static int valid_buffer(void *top, int stride, int fmt, uintptr_t *phys_out)
{
    uintptr_t phys;

    if (!top || fmt < 0 || fmt > 3 || stride < SCREEN_W || stride > 1024 ||
        ((uintptr_t)top & 3))
        return 0;
    phys = PHYS(top);
    if (!ADDR_OK(phys, (uintptr_t)stride * SCREEN_H * formats[fmt].bpp))
        return 0;
    *phys_out = phys;
    return 1;
}

static uint32_t row_hash(const Slot *s, int i)
{
    const FormatInfo *f = &formats[s->format];
    const int words  = SCREEN_W * f->bpp / 4;
    const int stride = s->stride_px * f->bpp / 4;
    const uint32_t *row = CACHED(s->addr) + (size_t)(2 * i + 1) * stride;
    uint32_t h = HASH_SEED;
    int x;

    sceKernelDcacheWritebackInvalidateRange((void *)row, words * 4);
    for (x = 0; x < words; x++)
        h = hash_word(h, row[x]);
    return h | 1;
}

/* Cheap check used by the polling path: has the game rewritten this buffer
   since we darkened it? Samples 5 rows instead of reading all 136. */
static int buffer_changed(void *top, int stride, int fmt, int want)
{
    uintptr_t phys;
    Slot *s;
    int k;

    if (!want || !valid_buffer(top, stride, fmt, &phys))
        return 0;
    s = lookup_slot(phys, fmt, stride);
    if (!s || s->shift != want)
        return 1;
    for (k = 0; k < 5; k++) {
        int i = k * 32;
        if (row_hash(s, i) != s->hash[i])
            return 1;
    }
    return 0;
}

#if DEBUG_MARKER
/* 8x4 dash in the top-left corner on even rows (which we never darken).
   src 1 = drawn from the hook (green), otherwise from polling (red). */
static void draw_marker(Slot *s, int src)
{
    static const uint32_t col[2][4] = {
        { 0x07E0, 0x83E0, 0xF0F0, 0xFF00FF00u },   /* green: 565, 5551, 4444, 8888 */
        { 0x001F, 0x801F, 0xF00F, 0xFF0000FFu },   /* red */
    };
    const FormatInfo *f = &formats[s->format];
    const int stride = s->stride_px * f->bpp / 4;
    const int nwords = (f->bpp == 4) ? 8 : 4;
    uint32_t c = col[src == 1 ? 0 : 1][s->format];
    int r, x;

    if (f->bpp == 2)
        c |= c << 16;
    for (r = 0; r < 8; r += 2) {
        uint32_t *crow = CACHED(s->addr) + (size_t)r * stride;
        uint32_t *wrow = UNCACHED(s->addr) + (size_t)r * stride;
        sceKernelDcacheWritebackInvalidateRange((void *)crow, nwords * 4);
        for (x = 0; x < nwords; x++)
            wrow[x] = c;
    }
}
#endif

/* Undo buffers darkened with a different setting (all of them if off).
   Caller holds the lock. */
static void undo_stale(int want)
{
    int i;
    for (i = 0; i < NUM_SLOTS; i++) {
        if (slots[i].addr && slots[i].shift && slots[i].shift != want) {
            convert_frame(&slots[i], 1);
            slots[i].shift = 0;
        }
    }
}

/* want: 0 = effect off, 1 or 2 = shift amount. src: 1 = hook, 2 = polling.
   Caller holds the lock. */
static void process_buffer(void *top, int stride, int fmt, int want, int src)
{
    uintptr_t phys;
    unsigned t0, dt;
    Slot *s;

    undo_stale(want);

    last_addr   = (unsigned)(uintptr_t)top;
    last_stride = (unsigned)stride;
    last_fmt    = (unsigned)fmt;

    if (!want || !valid_buffer(top, stride, fmt, &phys))
        return;

    s = find_slot(phys, fmt, stride);
    s->shift = want;

    t0 = sceKernelGetSystemTimeLow();
    convert_frame(s, 0);
    dt = sceKernelGetSystemTimeLow() - t0;
    last_us = dt;
    if (dt > max_us) max_us = dt;

#if DEBUG_MARKER
    draw_marker(s, src);
#endif
}

/* ------------------------------------------------------------------ */
/* Inline hooks (patch first two instructions, jump through trampoline) */
/* ------------------------------------------------------------------ */
typedef struct {
    uintptr_t addr;
    uint32_t  saved[2];
    uint32_t  tramp[3];
    int       status;   /* 0 none, 1 active, 2 not found, 3 unsafe prologue, 4 segment mismatch */
} Hook;

static Hook hook_a, hook_b;
static int (*orig_a)(void *top, int width, int fmt, int sync);
static int (*orig_b)(int pri, void *top, int width, int fmt, int sync);
static volatile int in_hook;

#define MAKE_J(t) (0x08000000u | ((uint32_t)((uintptr_t)(t) & 0x0FFFFFFCu) >> 2))

static void flush_caches(void)
{
    sceKernelDcacheWritebackInvalidateAll();
    sceKernelIcacheInvalidateAll();
}

/* Instructions that depend on the PC can't be moved into a trampoline. */
static int is_pc_dependent(uint32_t i)
{
    uint32_t op = i >> 26;
    if (op >= 0x01 && op <= 0x07) return 1;              /* regimm, j, jal, beq, bne, blez, bgtz */
    if (op >= 0x10 && op <= 0x13) return 1;              /* coprocessor / branches */
    if (op >= 0x14 && op <= 0x17) return 1;              /* branch-likely */
    if (op == 0 && ((i & 0x3F) == 0x08 || (i & 0x3F) == 0x09)) return 1;  /* jr, jalr */
    return 0;
}

static void install_hook(Hook *h, uintptr_t func, void *hook_fn)
{
    uint32_t i0, i1;

    if (!func) { h->status = 2; return; }

    h->addr = func;
    i0 = _lw(func);
    i1 = _lw(func + 4);
    h->saved[0] = i0;
    h->saved[1] = i1;

    if (is_pc_dependent(i0) || is_pc_dependent(i1)) { h->status = 3; return; }
    if ((((uintptr_t)hook_fn ^ func) & 0xF0000000u) ||
        (((uintptr_t)h->tramp ^ func) & 0xF0000000u)) { h->status = 4; return; }

    h->tramp[0] = i0;
    h->tramp[1] = MAKE_J(func + 8);
    h->tramp[2] = i1;            /* sits in the jump's delay slot */
    flush_caches();

    _sw(0, func + 4);
    _sw(MAKE_J(hook_fn), func);
    flush_caches();

    h->status = 1;
}

static void remove_hook(Hook *h)
{
    if (h->status != 1)
        return;
    _sw(h->saved[1], h->addr + 4);
    _sw(h->saved[0], h->addr);
    flush_caches();
    h->status = 0;
}

/* Runs on the caller's thread. Never blocks: if the render thread holds the
   lock we simply skip this frame. */
static void on_frame(void *top, int width, int fmt)
{
    hook_count++;
    if (lock_sema < 0 || sceKernelPollSema(lock_sema, 1) < 0) {
        busy_skips++;
        return;
    }
    process_buffer(top, width, fmt, current_want(), 1);
    sceKernelSignalSema(lock_sema, 1);
}

static int hooked_a(void *top, int width, int fmt, int sync)
{
    int ret, outer = !in_hook;

    if (outer) {
        in_hook = 1;
        calls_a++;
        if (running && top)
            on_frame(top, width, fmt);
    }
    ret = orig_a(top, width, fmt, sync);
    if (outer)
        in_hook = 0;
    return ret;
}

static int hooked_b(int pri, void *top, int width, int fmt, int sync)
{
    int ret, outer = !in_hook;

    if (outer) {
        in_hook = 1;
        calls_b++;
        if (running && top)
            on_frame(top, width, fmt);
    }
    ret = orig_b(pri, top, width, fmt, sync);
    if (outer)
        in_hook = 0;
    return ret;
}

/* ------------------------------------------------------------------ */
/* Debug log                                                           */
/* ------------------------------------------------------------------ */
#if DEBUG_LOG
static char logbuf[512];
static int  loglen;

static void lput(const char *s)
{
    while (*s && loglen < (int)sizeof(logbuf) - 1)
        logbuf[loglen++] = *s++;
}

static void lkv(const char *k, unsigned v, int hex)
{
    char t[12];
    int n = 0;

    lput(" "); lput(k); lput("=");
    if (hex) lput("0x");
    if (v == 0) t[n++] = '0';
    while (v) {
        unsigned d = hex ? (v & 15) : (v % 10);
        t[n++] = (char)(d < 10 ? '0' + d : 'a' + d - 10);
        v = hex ? (v >> 4) : (v / 10);
    }
    while (n) {
        char c[2];
        c[0] = t[--n]; c[1] = 0;
        lput(c);
    }
}

static void write_log(unsigned loops)
{
    static const char *paths[2] = { "ms0:/scanline_log.txt", "ef0:/scanline_log.txt" };
    SceUID fd = -1;
    int p;

    loglen = 0;
    lput("scanline log:");
    lkv("loops", loops, 0);
    lkv("statA", hook_a.status, 0);
    lkv("statB", hook_b.status, 0);
    lkv("callsA", calls_a, 0);
    lkv("callsB", calls_b, 0);
    lkv("fallback", fallback_calls, 0);
    lkv("busy", busy_skips, 0);
    lkv("addr", last_addr, 1);
    lkv("stride", last_stride, 0);
    lkv("fmt", last_fmt, 0);
    lkv("want", (unsigned)current_want(), 0);
    lkv("last_us", last_us, 0);
    lkv("max_us", max_us, 0);
    lkv("fnA", (unsigned)hook_a.addr, 1);
    lkv("fnA_i0", hook_a.saved[0], 1);
    lkv("fnA_i1", hook_a.saved[1], 1);
    lkv("fnB", (unsigned)hook_b.addr, 1);
    lkv("fnB_i0", hook_b.saved[0], 1);
    lkv("fnB_i1", hook_b.saved[1], 1);
    lput("\n");

    for (p = 0; p < 2 && fd < 0; p++)
        fd = sceIoOpen(paths[p], PSP_O_WRONLY | PSP_O_CREAT | PSP_O_TRUNC, 0777);
    if (fd >= 0) {
        sceIoWrite(fd, logbuf, loglen);
        sceIoClose(fd);
    }
}
#endif

/* ------------------------------------------------------------------ */
/* Threads                                                             */
/* ------------------------------------------------------------------ */
static int render_thread(SceSize args, void *argp)
{
    unsigned last_hooks = hook_count;
    unsigned last_hook_time = 0, last_full = 0, last_log = 0, loops = 0;

    while (running) {
        void *top = NULL;
        int stride = 0, fmt = 0, want, feeding;
        unsigned now;

        sceKernelDelayThread(POLL_US);
        if (!running)
            break;
        loops++;
        now = sceKernelGetSystemTimeLow();

        if (hook_count != last_hooks) {
            last_hooks = hook_count;
            last_hook_time = now;
        }
        feeding = (hook_a.status == 1 || hook_b.status == 1) &&
                  (unsigned)(now - last_hook_time) < HOOK_ACTIVE_US;
        want = current_want();

        lock();
        if (feeding) {
            /* Hooks are feeding us; just honour toggles / opacity changes,
               which also covers static screens where nothing is submitted. */
            undo_stale(want);
        } else {
            if (sceDisplayGetFrameBuf(&top, &stride, &fmt,
                                      PSP_DISPLAY_SETBUF_IMMEDIATE) < 0)
                top = NULL;

            /* Poll often and re-darken the moment the game rewrites the
               visible buffer; do a full pass at least once per frame. */
            if ((unsigned)(now - last_full) >= FULL_EVERY_US ||
                buffer_changed(top, stride, fmt, want)) {
                fallback_calls++;
                process_buffer(top, stride, fmt, want, 2);
                last_full = now;
            } else {
                undo_stale(want);
            }
        }
        unlock();

#if DEBUG_LOG
        if (loops == 1 || (unsigned)(now - last_log) >= LOG_EVERY_US) {
            last_log = now;
            write_log(loops);
        }
#endif
    }

    lock();
    undo_stale(0);   /* leave the screen clean on unload */
    unlock();
    return 0;
}

static int input_thread(SceSize args, void *argp)
{
    SceCtrlData pad;
    unsigned int prev = 0;
    int combo = 0;

    /* Deliberately no sceCtrlSetSamplingMode/Cycle here: those are global
       and would override the game's own input settings. */
    while (running) {
        unsigned int now, pressed;

        sceCtrlPeekBufferPositive(&pad, 1);
        now     = pad.Buttons;
        pressed = now & ~prev;

        if (now & PSP_CTRL_NOTE) {
            if (pressed & PSP_CTRL_UP) {
                darkness_shift = 1;
                combo = 1;
            } else if (pressed & PSP_CTRL_DOWN) {
                darkness_shift = 2;
                combo = 1;
            }
        } else if (prev & PSP_CTRL_NOTE) {
            /* NOTE released: plain tap toggles, NOTE+UP/DOWN does not. */
            if (!combo)
                enabled = !enabled;
            combo = 0;
        }

        prev = now;
        sceKernelDelayThread(20000);
    }
    return 0;
}

/* ------------------------------------------------------------------ */
/* Module entry points                                                 */
/* ------------------------------------------------------------------ */
int module_start(SceSize args, void *argp)
{
    uintptr_t fa, fb;

    lock_sema = sceKernelCreateSema("scanline_lock", 0, 1, 1, NULL);

    fa = (uintptr_t)sctrlHENFindFunction("sceDisplay_Service", "sceDisplay",
                                         NID_SETFRAMEBUF);
    fb = (uintptr_t)sctrlHENFindFunction("sceDisplay_Service", "sceDisplay_driver",
                                         NID_SETFRAMEBUF_INTERNAL);
    if (fb == fa)
        fb = 0;   /* same function under two names: hook it once */

    install_hook(&hook_a, fa, (void *)hooked_a);
    if (hook_a.status == 1)
        orig_a = (int (*)(void *, int, int, int))(void *)hook_a.tramp;

    install_hook(&hook_b, fb, (void *)hooked_b);
    if (hook_b.status == 1)
        orig_b = (int (*)(int, void *, int, int, int))(void *)hook_b.tramp;

    thid_render = sceKernelCreateThread("scanline_render", render_thread,
                                        0x10, 0x2000, 0, NULL);
    if (thid_render >= 0)
        sceKernelStartThread(thid_render, 0, NULL);

    thid_input = sceKernelCreateThread("scanline_input", input_thread,
                                       0x11, 0x1000, 0, NULL);
    if (thid_input >= 0)
        sceKernelStartThread(thid_input, 0, NULL);

    return 0;
}

int module_stop(SceSize args, void *argp)
{
    SceUInt timeout;

    running = 0;   /* hooks become pass-through from here on */

    /* Put the original instructions back before our code can go away. */
    remove_hook(&hook_a);
    remove_hook(&hook_b);

    /* Let each thread exit on its own (render restores the screen first),
       then force-terminate and delete in case it is still blocked. */
    if (thid_render >= 0) {
        timeout = 200000;
        sceKernelWaitThreadEnd(thid_render, &timeout);
        sceKernelTerminateDeleteThread(thid_render);
        thid_render = -1;
    }
    if (thid_input >= 0) {
        timeout = 100000;
        sceKernelWaitThreadEnd(thid_input, &timeout);
        sceKernelTerminateDeleteThread(thid_input);
        thid_input = -1;
    }
    if (lock_sema >= 0) {
        SceUID id = lock_sema;
        lock_sema = -1;
        sceKernelDeleteSema(id);
    }
    return 0;
}
