CCFLAGS ?= -m32 -g

.PHONY: clean runtime.a

all: lama-impl

clean:
	$(MAKE) -C ../runtime clean
	rm -rf *.o lama-impl

lama-impl: byterun.o runtime.a
	$(CC) $(CCFLAGS) byterun.o ../runtime/runtime.a -o lama-impl

runtime.a:
	$(MAKE) -C ../runtime

%.o: %.c
	$(CC) $(CCFLAGS) -I../runtime -c $*.c
