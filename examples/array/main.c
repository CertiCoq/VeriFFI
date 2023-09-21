#include <stdio.h>
#include <stdlib.h>
#include "gc.h"

extern value body(struct thread_info *);
extern void print_Coq_Init_Datatypes_nat(int_or_ptr64);

_Bool is_ptr(unsigned int s) {
  return (_Bool) Is_block(s);
} 

int main(int argc, char *argv[]) {
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  value tmp = body(tinfo);

  print_Coq_Init_Datatypes_option(tmp, print_Coq_Init_Datatypes_nat);

  puts("");
  return 0;
}
