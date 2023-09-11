#include "values.h"
struct closure;
struct stack_frame;
struct thread_info;
struct closure {
  void (*func)(struct thread_info, value, value);
  value env;
};

struct stack_frame {
  value *next;
  value *root;
  struct stack_frame *prev;
};

struct thread_info {
  value *alloc;
  value *limit;
  struct heap *heap;
  value args[1024];
  struct stack_frame *fp;
  unsigned long long nalloc;
};

extern unsigned int get_unboxed_ordinal(value);
extern unsigned int get_boxed_ordinal(value);
extern value *get_args(value);
extern value make_Coq_Init_Datatypes_option_Some(value, value *);
extern value alloc_make_Coq_Init_Datatypes_option_Some(struct thread_info *, value);
extern value make_Coq_Init_Datatypes_option_None(void);
extern value make_Coq_Init_Datatypes_nat_O(void);
extern value make_Coq_Init_Datatypes_nat_S(value, value *);
extern value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, value);
extern value make_Coq_Init_Datatypes_unit_tt(void);
extern value make_prog_C_MI_pureI(value, value, value *);
extern value alloc_make_prog_C_MI_pureI(struct thread_info *, value, value);
extern value make_prog_C_MI_bindI(value, value, value, value, value *);
extern value alloc_make_prog_C_MI_bindI(struct thread_info *, value, value, value, value);
extern value make_prog_C_MI_setI(value, value, value *);
extern value alloc_make_prog_C_MI_setI(struct thread_info *, value, value);
extern value make_prog_C_MI_getI(value, value *);
extern value alloc_make_prog_C_MI_getI(struct thread_info *, value);
extern unsigned int get_Coq_Init_Datatypes_option_tag(value);
extern unsigned int get_Coq_Init_Datatypes_nat_tag(value);
extern unsigned int get_Coq_Init_Datatypes_unit_tag(value);
extern unsigned int get_prog_C_MI_tag(value);
extern void print_Coq_Init_Datatypes_option(value, void (*)(value));
extern void print_Coq_Init_Datatypes_nat(value);
extern void print_Coq_Init_Datatypes_unit(value);
extern void print_prog_C_MI(value);
extern value call(struct thread_info *, value, value);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Init_Datatypes_option[2][5];

extern signed char const names_of_Coq_Init_Datatypes_nat[2][2];

extern signed char const names_of_Coq_Init_Datatypes_unit[1][3];

extern signed char const names_of_prog_C_MI[4][6];


