CCOMPILER=gcc

default: copy tests prog

.PHONY: default clean tests prog

copy:
	cp ~/certicoq/theories/Runtime/gc.c ./
	cp ~/certicoq/theories/Runtime/gc.h ./
	cp ~/certicoq/theories/Runtime/gc_stack.c ./
	cp ~/certicoq/theories/Runtime/gc_stack.h ./
	cp ~/certicoq/theories/Runtime/values.h ./
	cp ~/certicoq/theories/Runtime/config.h ./

clean:
	rm -f ./gc.c
	rm -f ./gc.h
	rm -f ./gc_stack.c
	rm -f ./gc_stack.h
	rm -f ./values.h
	rm -f ./config.h
	rm -f ./*.*.c
	rm -f ./*.*.h
	rm -f ./glue.*.*.c
	rm -f ./glue.*.*.h
	rm -f ./glue.c
	rm -f ./glue.h
	rm -f ./*.vo
	rm -f ./*.vok
	rm -f ./*.vos
	rm -f ./*.glob

tests: tests.v
	coqc tests.v

prog:
	$(CCOMPILER) -g -o prog -Wno-everything -fomit-frame-pointer main.c gc_stack.c tests.prog.c glue.c io.c
