DEBUG_FILES=stack-dump-before data-dump-before extra-roots-dump-before heap-dump-before stack-dump-after data-dump-after extra-roots-dump-after heap-dump-after
TESTS=$(sort $(filter-out test111, $(basename $(wildcard test*.lama))))

LAMAC ?= lamac
LAMA_IMPL=../src/lama-impl

.PHONY: check $(TESTS)


check: ctest111 $(TESTS)

$(TESTS): %: %.log
	# @echo "regression/$@"
	diff $@.log orig/$@.log

%.log: %.bc
	$(LAMA_IMPL) $< < $*.input > $@

%.bc: %.lama
	$(LAMAC) -b $<

ctest111:
	@echo "regression/test111"
	@LAMA=../runtime $(LAMAC) test111.lama && cat test111.input | ./test111 > test111.log && diff test111.log orig/test111.log

clean:
	$(RM) test*.log *.s *.sm *~ $(TESTS) *.i $(DEBUG_FILES) test111
	$(MAKE) clean -C expressions
	$(MAKE) clean -C deep-expressions
