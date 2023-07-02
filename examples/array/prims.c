#include "values.h"
#include "glue.h"
#include <stddef.h>
#include <stdio.h>

#define SHELTER0(tinfo, exp) (exp)
#define SHELTER1(tinfo, exp, a) ({ \
  value root[1] = { a }; \
  struct stack_frame frame = { root + 1, root, tinfo->fp }; \
  tinfo->fp = &frame; value __TEMP__ = exp; \
  a = root[0]; \
  tinfo->fp = frame.prev; __TEMP__; })
#define SHELTER2(tinfo, exp, a, b) ({ \
  value root[2] = { a, b }; \
  struct stack_frame frame = { root + 2, root, tinfo->fp }; \
  tinfo->fp = &frame; value __TEMP__ = exp; \
  a = root[0]; b = root[1]; \
  tinfo->fp = frame.prev; __TEMP__; })
#define SHELTER3(tinfo, exp, a, b, c) ({ \
  value root[3] = { a, b, c }; \
  struct stack_frame frame = { root + 3, root, tinfo->fp }; \
  tinfo->fp = &frame; value __TEMP__ = exp; \
  a = root[0]; b = root[1]; c = root[2]; \
  tinfo->fp = frame.prev; __TEMP__; })
#define SHELTER4(tinfo, exp, a, b, c, d) ({ \
  value root[4] = { a, b, c, d }; \
  struct stack_frame frame = { root + 4, root, tinfo->fp }; \
  tinfo->fp = &frame; value __TEMP__ = exp; \
  a = root[0]; b = root[1]; c = root[2]; d = root[3]; \
  tinfo->fp = frame.prev; __TEMP__; })

typedef enum { O, S } nat;
unsigned long long nat_to_ull(value n) {
  value temp = n;
  unsigned int i = 0;

  while(1) {
    unsigned int tag = get_Coq_Init_Datatypes_nat_tag(temp);
    if(tag == S) {
      i++;
      temp = get_Coq_Init_Datatypes_S_args(temp)->Coq_Init_Datatypes_S_arg_0;
    } else {
      break;
    }
  } 
  return i;
}

typedef enum { PURE, BIND, SET, GET } mi;
value runM(struct thread_info *tinfo, unsigned long long size, value init, value arr, value action) {
  value i, temp, arg0, arg1;
  switch (get_prog_C_MI_tag(action)) {
    case PURE:
      return get_prog_C_pureI_args(action)->prog_C_pureI_arg_1;
    case BIND:
      arg0 = get_prog_C_bindI_args(action)->prog_C_bindI_arg_2;
      arg1 = get_prog_C_bindI_args(action)->prog_C_bindI_arg_3;
      temp = SHELTER1(tinfo, runM(tinfo, size, init, arr, arg0), arg1);
      temp = SHELTER2(tinfo, call(tinfo, arg1, temp), arr, init);
      return runM(tinfo, size, init, arr, temp);
    case SET:
      arg0 = get_prog_C_setI_args(action)->prog_C_setI_arg_0;
      i = nat_to_ull(arg0);
      arg1 = get_prog_C_setI_args(action)->prog_C_setI_arg_1;
      // check if there's enough memory for the update record (1 word)
      if (!(1 <= tinfo->limit - tinfo->alloc)) {
        tinfo->nalloc = 1;
        SHELTER2(tinfo, garbage_collect(tinfo), arr, arg1);
      }
      // printf("Setting %i from size %i\n", i, size);
      if (i < size) {
        certicoq_modify(tinfo, (value *) arr + i, arg1);
      }
      return make_Coq_Init_Datatypes_unit_tt();
    case GET:
      arg0 = get_prog_C_getI_args(action)->prog_C_getI_arg_0;
      i = nat_to_ull(arg0);
      // printf("Getting %i from size %i\n", i, size);
      if (i < size) {
        return *((value *) arr + i);
      } else {
        return init;
      }
  }
}

value array_runM(struct thread_info *tinfo, value a, value len, value init, value action) {
  size_t size = nat_to_ull(len);
  size_t nalloc = size + 1;
  // check if there's enough memory for the array (size + 1 word for header)
  if (!(nalloc <= tinfo->limit - tinfo->alloc)) {
    tinfo->nalloc = nalloc;
    SHELTER2(tinfo, garbage_collect(tinfo), init, action);
  }
  value *arr = tinfo->alloc;
  arr[0LLU] = size << 9;
  arr = arr + 1LLU;
  for (size_t i = 0; i < size; i++) {
    arr[i] = init;
  }
  tinfo->alloc += nalloc;
  return runM(tinfo, size, init, (value) arr, action);
}
