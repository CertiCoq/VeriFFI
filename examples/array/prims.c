#include "values.h"
#include "glue.h"
#include <stddef.h>
#include <stdio.h>

#define SHELTER0(tinfo, exp) (exp)
#define SHELTER1(tinfo, exp, a) ({ \
  value __ROOT__[1] = { a }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 1, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })
#define SHELTER2(tinfo, exp, a, b) ({ \
  value __ROOT__[2] = { a, b }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 2, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })
#define SHELTER3(tinfo, exp, a, b, c) ({ \
  value __ROOT__[3] = { a, b, c }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 3, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; c = __ROOT__[2]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })
#define SHELTER4(tinfo, exp, a, b, c, d) ({ \
  value __ROOT__[4] = { a, b, c, d }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 4, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; c = __ROOT__[2]; d = __ROOT__[3]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })
#define SHELTER5(tinfo, exp, a, b, c, d, e) ({ \
  value __ROOT__[5] = { a, b, c, d, e }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 5, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; c = __ROOT__[2]; d = __ROOT__[3]; e = __ROOT__[4]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })
#define SHELTER6(tinfo, exp, a, b, c, d, e, f) ({ \
  value __ROOT__[6] = { a, b, c, d, e, f }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 6, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; c = __ROOT__[2]; d = __ROOT__[3]; e = __ROOT__[4]; f = __ROOT__[5]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })
#define SHELTER7(tinfo, exp, a, b, c, d, e, f, g) ({ \
  value __ROOT__[7] = { a, b, c, d, e, f, g }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 7, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; c = __ROOT__[2]; d = __ROOT__[3]; e = __ROOT__[4]; f = __ROOT__[5]; g = __ROOT__[6]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })
#define SHELTER8(tinfo, exp, a, b, c, d, e, f, g, h) ({ \
  value __ROOT__[8] = { a, b, c, d, e, f, g, h }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 8, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; c = __ROOT__[2]; d = __ROOT__[3]; e = __ROOT__[4]; f = __ROOT__[5]; g = __ROOT__[6]; h = __ROOT__[7]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })

typedef enum { O, S } nat;
unsigned long long nat_to_ull(value n) {
  value temp = n;
  unsigned int i = 0;

  while(1) {
    unsigned int tag = get_Coq_Init_Datatypes_nat_tag(temp);
    if(tag == S) {
      i++;
      temp = get_args(temp)[0];
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
      return get_args(action)[1];
    case BIND:
      arg0 = get_args(action)[2];
      arg1 = get_args(action)[3];
      temp = SHELTER4(tinfo, runM(tinfo, size, init, arr, arg0), arg0, arg1, init, arr);
      temp = SHELTER4(tinfo, call(tinfo, arg1, temp), arg1, init, arr, temp);
      return runM(tinfo, size, init, arr, temp);
    case SET:
      arg0 = get_args(action)[0];
      i = nat_to_ull(arg0);
      arg1 = get_args(action)[1];
      // check if there's enough memory for the update record (1 word)
      if (!(1 <= tinfo->limit - tinfo->alloc)) {
        tinfo->nalloc = 1;
        SHELTER2(tinfo, garbage_collect(tinfo), arr, arg1);
      }
      if (i < size) {
        certicoq_modify(tinfo, (value *) arr + i, arg1);
      }
      return make_Coq_Init_Datatypes_unit_tt();
    case GET:
      arg0 = get_args(action)[0];
      i = nat_to_ull(arg0);
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
  arr[0LLU] = size << 10;
  arr = arr + 1LLU;
  for (size_t i = 0; i < size; i++) {
    arr[i] = init;
  }
  tinfo->alloc += nalloc;
  return runM(tinfo, size, init, (value) arr, action);
}
