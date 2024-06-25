#include <stdio.h>
#include <stdlib.h>
#include <gc_stack.h>
#include "glue.h"

extern value body(struct thread_info *);

int main(int argc, char *argv[]) {
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  value tmp = body(tinfo);

  print_Coq_Numbers_BinNums_Z(tmp);
  puts("");
  return 0;
}
