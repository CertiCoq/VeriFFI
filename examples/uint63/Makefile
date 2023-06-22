CCOMPILER=gcc

default: copy coq c

.PHONY: default clean coq c

copy:
	cp /home/opam/certicoq/theories/Runtime/gc.c ./
	cp /home/opam/certicoq/theories/Runtime/gc.h ./
	cp /home/opam/certicoq/theories/Runtime/gc_stack.c ./
	cp /home/opam/certicoq/theories/Runtime/gc_stack.h ./
	cp /home/opam/certicoq/theories/Runtime/values.h ./
	cp /home/opam/certicoq/theories/Runtime/config.h ./

clean:
	rm -f ./gc.c
	rm -f ./gc.h
	rm -f ./gc_stack.c
	rm -f ./gc_stack.h
	rm -f ./values.h
	rm -f ./config.h
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

coq:
	coqc prog.v

c:
	$(CCOMPILER) -g -o prog main.c gc_stack.c prog.prog.c glue.c prims.c
	# $(CCOMPILER) -g -o prog -Wno-everything -fomit-frame-pointer main.c gc.c prog.prog.c glue.prog.prog.c prims.c

clightgen:
	clightgen -canonical-idents -normalize prims.c
	clightgen -canonical-idents -normalize glue.c
