all: CoqMakefile
	make -f CoqMakefile

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean: CoqMakefile
	make -f CoqMakefile clean

.PHONY: all
