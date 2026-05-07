# Invoke via: eval $(opam env --switch=iris-dev) && make
# Or set OPAMSWITCH=iris-dev in your shell first.

all: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean:
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf

.PHONY: all clean
