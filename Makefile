all: Makefile.coq
	cd CertiGraph; make certigc
#	make -f Makefile.coq prims_files
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -f examples/*/glue.[chv]
	rm -f examples/*/prog.[ch]
	rm -f examples/*/prims.v

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
#	awk '{if ($$1=="$$(VDFILE):") print "$$(VDFILE): _CoqProject $$(filter-out $$(GENERATED_VFILES), $$(VFILES))"; else print $$0}' <Makefile.coq >xMakefile.coq
#	mv xMakefile.coq Makefile.coq

.PHONY: Makefile.coq all clean
