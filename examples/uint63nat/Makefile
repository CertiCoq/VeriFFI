CCOMPILER=gcc
CERTIGC=../../CertiGraph/CertiGC/'GC Source'

default: copy coq c

.PHONY: default clean coq c

copy:
#	cp ../../certicoq/theories/Runtime/m.h ./
#	cp ../../certicoq/theories/Runtime/config.h ./
#	cp ../../certicoq/theories/Runtime/values.h ./
#	cp ../../certicoq/theories/Runtime/gc_stack.c ./
#	cp ../../certicoq/theories/Runtime/gc_stack.h ./
	cp $(CERTIGC)/m.h ./
	cp $(CERTIGC)/config.h ./
	cp $(CERTIGC)/values.h ./
	cp $(CERTIGC)/gc.c ./
	cp $(CERTIGC)/gc.h ./
	cp gc.h gc_stack.h

clean:
	rm -f m.h config.h values.h gc_stack.c gc.c gc_stack.h gc.h
	rm -f *.*.c *.*.h *.*.o
	rm -f glue.*.*.c glue.*.*.h
	rm -f glue.c glue.h
	rm -f *.vo *.vok *.vos *.glob

COQFLAGS= -Q ../../library VeriFFI.library -Q ../../generator VeriFFI.generator -Q ../../verification VeriFFI.verification -Q ../../examples VeriFFI.examples -Q ../../CertiGraph CertiGraph



%.vo: %.v
	coqc $(COQFLAGS) $*.v

coq: Verif_prog_general.vo

prog.vo: prog.v
prims.vo: prims.v
Verif_prog_general.vo: Verif_prog_general.v prims.vo prog.vo glue.vo

c:
	$(CCOMPILER) -w -g -o prog main.c gc.c VeriFFI.examples.uint63nat.prog.prog.c glue.c prims.c

clightgen:
	clightgen -DVERIFFI -DCOMPCERT -canonical-idents -normalize -fstruct-passing prims.c
	clightgen -DVERIFFI -DCOMPCERT -canonical-idents -normalize -fstruct-passing glue.c
