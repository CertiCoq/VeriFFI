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

  run_itree(tinfo, tinfo->args[1]);
  return 0;
}
