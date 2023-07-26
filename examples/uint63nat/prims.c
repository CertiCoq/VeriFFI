#include "glue.h"
#include <stdio.h>

typedef unsigned long long uint64;
typedef enum { O, S } nat;

#define LIVEPOINTERS1(tinfo, exp, a) ({ \
  value __ROOT__[1] = { a }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 1, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })

int_or_ptr64 uint63_from_nat(int_or_ptr64 n) {
  int_or_ptr64 temp = n;
  uint64 i = 0;

  while (get_Coq_Init_Datatypes_nat_tag(temp) == S) {
    i++;
    temp = get_args(temp)[0];
  }
  return (int_or_ptr64) ((i << 1) + 1);
}

int_or_ptr64 uint63_to_nat(struct thread_info *tinfo, int_or_ptr64 t) {
  uint64 i = (int_or_ptr64) (((uint64) t) >> 1);
  int_or_ptr64 temp = make_Coq_Init_Datatypes_nat_O();
  while (i) {
    if (!(2 <= tinfo->limit - tinfo->alloc)) {
      tinfo->nalloc = 2;
      garbage_collect(tinfo);
    }
    temp = alloc_make_Coq_Init_Datatypes_nat_S(tinfo, temp);
    i--;
  }
  return temp;
}

int_or_ptr64 uint63_add(int_or_ptr64 x, int_or_ptr64 y) {
  return (int_or_ptr64) ((((((uint64) x) >> 1) + (((uint64) y) >> 1)) << 1) + 1);
}

int_or_ptr64 uint63_mul(int_or_ptr64 x, int_or_ptr64 y) {
  return (int_or_ptr64) ((((((uint64) x) >> 1) * (((uint64) y) >> 1)) << 1) + 1);
}
