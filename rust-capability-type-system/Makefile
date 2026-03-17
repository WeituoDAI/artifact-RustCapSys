COQMAKEFILE := Makefile.coq

all: $(COQMAKEFILE)
	@$(MAKE) -f $<

$(COQMAKEFILE): _CoqProject
	coq_makefile -f $< -o $@

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
	find . -name "*.aux" -delete
	find . -name "*.glob" -delete
	find . -name "*.vo" -delete
	rm -f .*.d *.d
	rm -f .lia.cache


.PHONY: all clean
