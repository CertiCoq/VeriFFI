#include "values.h"
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

value uint63_from_nat(value n) {
  value temp = n;
  uint64 i = 0;

  while (get_Coq_Init_Datatypes_nat_tag(temp) == S) {
    i++;
    temp = get_args(temp)[0];
  }
  return (value) ((i << 1) + 1);
}

value uint63_to_nat(struct thread_info *tinfo, value t) {
  uint64 i = (value) (((uint64) t) >> 1);
  value temp = make_Coq_Init_Datatypes_nat_O();
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

value uint63_add(value x, value y) {
  return (value) ((((((uint64) x) >> 1) + (((uint64) y) >> 1)) << 1) + 1);
}

value uint63_mul(value x, value y) {
  return (value) ((((((uint64) x) >> 1) * (((uint64) y) >> 1)) << 1) + 1);
}
