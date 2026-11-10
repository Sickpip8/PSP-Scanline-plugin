TARGET = scanline_ark4
OBJS = main.o exports.o systemctrl_stub.o
 
BUILD_PRX = 1
PRX_EXPORTS = exports.exp
PSP_FW_VERSION = 600
 
CFLAGS = -O2 -G0 -Wall
LIBS = -lpspdisplay -lpspctrl
 
PSPSDK = $(shell psp-config --pspsdk-path)
include $(PSPSDK)/lib/build_prx.mak
 

