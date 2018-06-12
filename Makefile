.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile

all: invoke-coqmakefile

clean:
	$(MAKE) --no-print-directory -f CoqMakefile clean

.PHONY: invoke-coqmakefile clean all
