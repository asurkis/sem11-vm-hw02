CCFLAGS ?= -m32 -g

.PHONY: clean runtime.a

all: lama-impl

clean:
	$(MAKE) -C ../runtime clean
	rm -rf *.o lama-impl

lama-impl: byterun.o runtime
	$(CC) $(CCFLAGS) byterun.o ../runtime/runtime.a ../runtime/virt_stack.o -o lama-impl

runtime:
	$(MAKE) -C ../runtime all virt_stack.o

%.o: %.c
	$(CC) $(CCFLAGS) -c $*.c
