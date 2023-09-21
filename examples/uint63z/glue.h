#include "values.h"
struct closure;
struct stack_frame;
struct thread_info;
struct closure {
  value (*func)(struct thread_info, value, value);
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
extern value make_Coq_Numbers_BinNums_positive_xI(value, value *);
extern value alloc_make_Coq_Numbers_BinNums_positive_xI(struct thread_info *, value);
extern value make_Coq_Numbers_BinNums_positive_xO(value, value *);
extern value alloc_make_Coq_Numbers_BinNums_positive_xO(struct thread_info *, value);
extern value make_Coq_Numbers_BinNums_positive_xH(void);
extern value make_Coq_Numbers_BinNums_Z_Z0(void);
extern value make_Coq_Numbers_BinNums_Z_Zpos(value, value *);
extern value alloc_make_Coq_Numbers_BinNums_Z_Zpos(struct thread_info *, value);
extern value make_Coq_Numbers_BinNums_Z_Zneg(value, value *);
extern value alloc_make_Coq_Numbers_BinNums_Z_Zneg(struct thread_info *, value);
extern unsigned int get_Coq_Numbers_BinNums_positive_tag(value);
extern unsigned int get_Coq_Numbers_BinNums_Z_tag(value);
extern void print_Coq_Numbers_BinNums_positive(value);
extern void print_Coq_Numbers_BinNums_Z(value);
extern value call(struct thread_info *, value, value);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Numbers_BinNums_positive[3][3];

extern signed char const names_of_Coq_Numbers_BinNums_Z[3][5];


