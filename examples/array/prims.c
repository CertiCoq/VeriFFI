#include <stdio.h>
#include "values.h"
#include "glue.h"

typedef enum { O, S } nat;
unsigned long long nat_to_ull(value n) {
  value temp = n;
  unsigned int i = 0;

  while(1) {
    unsigned int tag = get_Coq_Init_Datatypes_nat_tag(temp);
    if(tag == S) {
      i++;
      temp = *((value *) temp);
    } else {
      break;
    }
  }
  return i;
}

typedef enum { PURE, BIND, SET, GET } mi;
value runM(struct thread_info *tinfo, value arr, value tree) {
  value temp, arg0, arg1, temp2;
  switch (get_prog_C_MI_tag(tree)) {
    case PURE:
      printf("PURE\n");
      return get_prog_C_pureI_args(tree)->prog_C_pureI_arg_1;
    case BIND:
      printf("BIND\n");
      arg0 = get_prog_C_bindI_args(tree)->prog_C_bindI_arg_2;
      arg1 = get_prog_C_bindI_args(tree)->prog_C_bindI_arg_3;
      temp = runM(tinfo, arr, arg0);
      printf("intermediate BIND 1\n");
      temp2 = call(tinfo, arg1, temp);
      printf("intermediate BIND 2\n");
      return runM(tinfo, arr, temp2);
    case SET:
      printf("SET\n");
      arg0 = get_prog_C_setI_args(tree)->prog_C_setI_arg_0;
      arg1 = get_prog_C_setI_args(tree)->prog_C_setI_arg_1;
      *((value *) arr + nat_to_ull(arg0)) = arg1;
      return make_Coq_Init_Datatypes_unit_tt();
    case GET:
      printf("GET\n");
      arg0 = get_prog_C_getI_args(tree)->prog_C_getI_arg_0;
      return *((value *) arr + nat_to_ull(arg0));
  }
}

value array_runM(struct thread_info *tinfo, value a, value len, value init, value m) {
  printf("Start array_runM\n");
  unsigned long long size = nat_to_ull(len);
  printf("Array of length %i\n", size);
  value *arr = tinfo->alloc;
  *((unsigned long long *) arr + 0LLU) = size << 9;
  for (unsigned long long i = 1; i <= size; i++) {
    *((unsigned long long *) arr + i) = init;
  }
  tinfo->alloc = tinfo->alloc + size + 1LLU;
  arr = arr + 1LLU;
  // gc?
  printf("End array_runM\n");
  return runM(tinfo, arr, m);

}
