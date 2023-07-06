#include "glue.h"
#include <stdio.h>

typedef unsigned long long int64;
typedef enum { O, S } nat;

int_or_ptr64 uint63_from_nat(int_or_ptr64 n) {
  int_or_ptr64 temp = n;
  int64 i = 0;
  unsigned int t = get_Coq_Init_Datatypes_nat_tag(temp);

  while (t == S) {
    i++;
    temp = get_Coq_Init_Datatypes_S_args(temp)->Coq_Init_Datatypes_S_arg_0;
    t = get_Coq_Init_Datatypes_nat_tag(temp);
  }
  return (int_or_ptr64) ((i << 1) + 1);
}

int_or_ptr64 uint63_to_nat(struct thread_info *tinfo, int_or_ptr64 t) {
  int_or_ptr64 i = (int_or_ptr64) (((int64) t) >> 1); /* size_t/unsigned long/uint64  */
  int_or_ptr64 temp = make_Coq_Init_Datatypes_nat_O();
  /* for loop? */
  while ((int64)i) {
    /* garbage collection check */
    temp = alloc_make_Coq_Init_Datatypes_nat_S(tinfo, temp);
    i = (int_or_ptr64) ((int64) i-1);
  }
  return temp;
}

int_or_ptr64 uint63_add(int_or_ptr64 x, int_or_ptr64 y) {
  return (int_or_ptr64) ((((((int64) x) >> 1) + (((int64) y) >> 1)) << 1) + 1);
}

int_or_ptr64 uint63_mul(int_or_ptr64 x, int_or_ptr64 y) {
  return (int_or_ptr64) ((((((int64) x) >> 1) * (((int64) y) >> 1)) << 1) + 1);
}