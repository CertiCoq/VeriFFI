#include <stdio.h>
#include <stdlib.h>
#include "gc.h"

extern value body(struct thread_info *);

_Bool is_ptr(unsigned int s) {
  return (_Bool) Is_block(s);
} 

int main(int argc, char *argv[]) {
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  body(tinfo);

  print_Coq_Init_Datatypes_bool(tinfo->args[1]);
  puts("");
  return 0;
}
