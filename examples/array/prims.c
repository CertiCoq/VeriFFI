#include "values.h"
#include "glue.h"

unsigned long long nat_to_ull(value n) {
  value temp = n;
  unsigned int i = 0;

  while(1) {
    unsigned int tag = get_Coq_Init_Datatypes_nat_tag(temp);
    if(tag == 1) {
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
  value temp, arg0, arg1;
  switch (get_prog_C_MI_tag(tree)) {
    case PURE:
      return *((value *) tree);
    case BIND:
      arg0 = get_prog_C_bindI_args(tree)->prog_C_bindI_arg_2;
      arg1 = get_prog_C_bindI_args(tree)->prog_C_bindI_arg_3;
      temp = runM(tinfo, arr, arg0);
      return runM(tinfo, arr, call(tinfo, arg1, temp));
    case SET:
      arg0 = get_prog_C_setI_args(tree)->prog_C_setI_arg_0;
      arg1 = get_prog_C_setI_args(tree)->prog_C_setI_arg_1;
      *((value *) arr + nat_to_ull(arg0)) = arg1;
      return make_Coq_Init_Datatypes_unit_tt();
    case GET:
      arg0 = get_prog_C_getI_args(tree)->prog_C_getI_arg_0;
      return *((value *) arr + nat_to_ull(arg0));
  }
}

value array_runM(struct thread_info *tinfo, value a, value len, value init, value m) {
  unsigned long long size = nat_to_ull(len);
  value *arr = tinfo->alloc;
  *((unsigned long long *) arr + 0LLU) = size << 9;
  for (unsigned long long i = 1; i <= size; i++) {
    *((unsigned long long *) arr + i) = init;
  }
  tinfo->alloc = tinfo->alloc + size + 1LLU;
  arr = arr + 1LLU;
  // gc?
  runM(tinfo, arr, m);

}
