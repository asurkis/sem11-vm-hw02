TESTS=$(sort $(basename $(wildcard *.lama)))

LAMAC ?= lamac
LAMA_IMPL=../src/lama-impl

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.bc
	@echo $@
	`which time` -f "$@\t%U" $(LAMA_IMPL) $<

%.bc: %.lama
	$(LAMAC) -b $<

clean:
	$(RM) test*.log *.s *~ $(TESTS) *.i
