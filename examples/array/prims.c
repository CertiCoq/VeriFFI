#include "values.h"
#include "glue.h"
#include<stdio.h>

#define shelter0(tinfo, exp) (exp)
#define shelter1(tinfo, exp, a) ({ \
  struct stack_frame frame; value root[1] = { a }; \
  frame.next = root + 1; frame.root = root; \ frame.prev = tinfo->fp; \
  tinfo->fp = &frame; \ value temp = exp; \
  a = root[0]; \
  tinfo->fp = frame.prev; exp })
#define shelter2(tinfo, exp, a, b) ({ \
  struct stack_frame frame; value root[2] = { a, b }; \
  frame.next = root + 2; frame.root = root; \ frame.prev = tinfo->fp; \
  tinfo->fp = &frame; \ value temp = exp; \
  a = root[0]; b = root[1] \
  tinfo->fp = frame.prev; exp })
#define shelter3(tinfo, exp, a, b, c) ({ \
  struct stack_frame frame; value root[3] = { a, b, c }; \
  frame.next = root + 3; frame.root = root; \ frame.prev = tinfo->fp; \
  tinfo->fp = &frame; \ value temp = exp; \
  a = root[0]; b = root[1]; c = root[2] \
  tinfo->fp = frame.prev; exp })
#define shelter4(tinfo, exp, a, b, c, d) ({ \
  struct stack_frame frame; value root[4] = { a, b, c, d }; \
  frame.next = root + 4; frame.root = root; \ frame.prev = tinfo->fp; \
  tinfo->fp = &frame; \ value temp = exp; \
  a = root[0]; b = root[1]; c = root[2]; d = root[3] \
  tinfo->fp = frame.prev; exp })

typedef enum { O, S } nat;
unsigned long long nat_to_ull(value n) {
  value temp = n;
  unsigned int i = 0;

  while(1) {
    unsigned int tag = get_Coq_Init_Datatypes_nat_tag(temp);
    if(tag == S) {
      i++;
      /* temp = *((value *) temp); */
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
      struct stack_frame frame;
      value root[2];
      root[0] = arg1;
      frame.next = root + 1;
      frame.root = root;
      frame.prev = tinfo->fp;
      tinfo->fp = &frame; // Push frame on stack
      temp = runM(tinfo, size, init, arr, arg0);
      arg1 = root[0];
      // Don't pop the old frame and push a new frame!
      // Instead, recycle the stack frame, be environmentally friendly.
      root[0] = arr;
      root[1] = init;
      frame.next = root + 2;
      temp = call(tinfo, arg1, temp);
      arr = root[0];
      init = root[1];
      tinfo->fp = frame.prev; // Pop from stack
      return runM(tinfo, size, init, arr, temp);
    case SET:
      arg0 = get_prog_C_setI_args(action)->prog_C_setI_arg_0;
      i = nat_to_ull(arg0);
      arg1 = get_prog_C_setI_args(action)->prog_C_setI_arg_1;
      // check if there's enough memory for the update record (1 word)
      if (!(1 <= tinfo->limit - tinfo->alloc)) {
        struct stack_frame frame;
        value root[2];
        root[0] = arr;
        root[1] = arg1;
        frame.next = root + 2;
        frame.root = root;
        frame.prev = tinfo->fp;
        tinfo->fp = &frame;
        tinfo->nalloc = 1;
        garbage_collect(tinfo);
        tinfo->fp = frame.prev;
        arr = root[0];
        arg1 = root[1];
      }
      printf("Setting %i from size %i\n", i, size);
      if (i < size) {
        certicoq_modify(tinfo, (value *) arr + i, arg1);
      }
      return make_Coq_Init_Datatypes_unit_tt();
    case GET:
      arg0 = get_prog_C_getI_args(action)->prog_C_getI_arg_0;
      i = nat_to_ull(arg0);
      printf("Getting %i from size %i\n", i, size);
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
    struct stack_frame frame;
    value root[2];
    root[0] = init;
    root[1] = action;
    frame.next = root + 2;
    frame.root = root;
    frame.prev = tinfo->fp;
    tinfo->fp = &frame;
    tinfo->nalloc = nalloc;
    garbage_collect(tinfo);
    tinfo->fp = frame.prev;
    init = root[0];
    action = root[1];
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
