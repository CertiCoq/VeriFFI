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
extern value make_Coq_Init_Datatypes_nat_O(void);
extern value make_Coq_Init_Datatypes_nat_S(value, value *);
extern value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, value);
extern value make_Coq_Init_Datatypes_bool_true(void);
extern value make_Coq_Init_Datatypes_bool_false(void);
extern value make_prog_exp_etrue(void);
extern value make_prog_exp_efalse(void);
extern value make_prog_exp_eand(value, value, value *);
extern value alloc_make_prog_exp_eand(struct thread_info *, value, value);
extern value make_prog_exp_eor(value, value, value *);
extern value alloc_make_prog_exp_eor(struct thread_info *, value, value);
extern value make_prog_exp_eif(value, value, value, value *);
extern value alloc_make_prog_exp_eif(struct thread_info *, value, value, value);
extern value make_Coq_Init_Datatypes_unit_tt(void);
extern value make_prog_T_mkT(value, value, value, value *);
extern value alloc_make_prog_T_mkT(struct thread_info *, value, value, value);
extern unsigned int get_Coq_Init_Datatypes_nat_tag(value);
extern unsigned int get_Coq_Init_Datatypes_bool_tag(value);
extern unsigned int get_prog_exp_tag(value);
extern unsigned int get_Coq_Init_Datatypes_unit_tag(value);
extern unsigned int get_prog_T_tag(value);
extern void print_Coq_Init_Datatypes_nat(value);
extern void print_Coq_Init_Datatypes_bool(value);
extern void print_prog_exp(value);
extern void print_Coq_Init_Datatypes_unit(value);
extern void print_prog_T(value);
extern value call(struct thread_info *, value, value);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Init_Datatypes_nat[2][2];

extern signed char const names_of_Coq_Init_Datatypes_bool[2][6];

extern signed char const names_of_prog_exp[5][7];

extern signed char const names_of_Coq_Init_Datatypes_unit[1][3];

extern signed char const names_of_prog_T[1][4];


