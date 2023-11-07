CCOMPILER=gcc

default: copy coq c

.PHONY: default clean coq c

copy:
	cp ../../certicoq/theories/Runtime/m.h ./
	cp ../../certicoq/theories/Runtime/config.h ./
	cp ../../certicoq/theories/Runtime/values.h ./
	cp ../../certicoq/theories/Runtime/gc_stack.c ./
	cp ../../certicoq/theories/Runtime/gc_stack.h ./

clean:
	rm -f ./m.h
	rm -f ./config.h
	rm -f ./values.h
	rm -f ./gc_stack.c
	rm -f ./gc_stack.h
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./*.*.o
	rm -f ./glue.*.*.c
	rm -f ./glue.*.*.h
	rm -f ./glue.c
	rm -f ./glue.h
	rm -f ./*.vo
	rm -f ./*.vok
	rm -f ./*.vos
	rm -f ./*.glob

COQFLAGS= -Q ../../library VeriFFI.library -Q ../../generator VeriFFI.generator -Q ../../verification VeriFFI.verification -Q ../../examples VeriFFI.examples -Q ../../CertiGraph CertiGraph



%.vo: %.v
	coqc $(COQFLAGS) $*.v

coq: Verif_prog_general.vo

prog.vo: prog.v
prims.vo: prims.v
Verif_prog_general.vo: Verif_prog_general.v prims.vo prog.vo glue.vo specs.vo

c:
	$(CCOMPILER) -w -g -o prog main.c gc_stack.c prog.prog.c glue.c prims.c

clightgen:
	clightgen -DVERIFFI -DCOMPCERT -canonical-idents -normalize -fstruct-passing prims.c
	clightgen -DVERIFFI -DCOMPCERT -canonical-idents -normalize -fstruct-passing glue.c
