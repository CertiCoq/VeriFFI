#include <stdio.h>
#include <stdlib.h>
#include "glue.h"

extern struct thread_info *make_tinfo();
extern value body(struct thread_info *);

_Bool is_ptr(unsigned int s) {
  return (_Bool) Is_block(s);
} 

int main(int argc, char *argv[]) {
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  value tmp = body(tinfo);

  print_Coq_Init_Datatypes_nat(tmp);
  puts("");
  return 0;
}
