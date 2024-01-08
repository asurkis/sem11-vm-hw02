CCFLAGS ?= -m32 -g -O2 -DNDEBUG

.PHONY: clean runtime.a

all: lama-impl

clean:
	$(MAKE) -C ../runtime clean
	rm -rf *.o lama-impl

lama-impl: byterun.o runtime
	$(CC) $(CCFLAGS) byterun.o ../runtime/runtime.a -o lama-impl

runtime:
	$(MAKE) -C ../runtime

%.o: %.c
	$(CC) $(CCFLAGS) -c $*.c
