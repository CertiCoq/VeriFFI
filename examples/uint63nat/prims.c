#include "values.h"
#include "glue.h"
#include <stdio.h>

typedef enum { O, S } nat;

value uint63_from_nat(value n) {
  value temp = n;
  unsigned long long i = 0;

  while (get_Coq_Init_Datatypes_nat_tag(temp) == S) {
    i++;
    temp = get_Coq_Init_Datatypes_S_args(temp)->Coq_Init_Datatypes_S_arg_0;
  }
  return (i << 1) + 1;
}

value uint63_to_nat(struct thread_info *tinfo, value t) {
  value i = t >> 1;
  value temp = make_Coq_Init_Datatypes_nat_O();
  while (i) {
    temp = alloc_make_Coq_Init_Datatypes_nat_S(tinfo, temp);
    i--;
  }
  return temp;
}

value uint63_add(value x, value y) {
  return (((x >> 1) + (y >> 1)) << 1) + 1;
}

value uint63_mul(value x, value y) {
  return (((x >> 1) * (y >> 1)) << 1) + 1;
}
