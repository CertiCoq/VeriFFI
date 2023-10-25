#include <stdio.h>
#include <stdlib.h>
#include "gc.h"

extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  value tmp = body(tinfo);

  print_Coq_Init_Datatypes_nat(tmp);
  puts("");
  return 0;
}
