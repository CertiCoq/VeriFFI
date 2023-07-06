typedef void * __attribute((aligned(4))) int_or_ptr32;
typedef void * __attribute((aligned(8))) int_or_ptr64;
struct closure;
struct stack_frame;
struct thread_info;
struct Coq_Init_Datatypes_O_args;
struct Coq_Init_Datatypes_S_args;
struct closure {
  void (*func)(struct thread_info, int_or_ptr64, int_or_ptr64);
  int_or_ptr64 env;
};

struct stack_frame {
  int_or_ptr64 *next;
  int_or_ptr64 *root;
  struct stack_frame *prev;
};

struct thread_info {
  int_or_ptr64 *alloc;
  int_or_ptr64 *limit;
  struct heap *heap;
  int_or_ptr64 args[1024];
  struct stack_frame *fp;
  unsigned long long nalloc;
};

struct Coq_Init_Datatypes_O_args {
};

struct Coq_Init_Datatypes_S_args {
  int_or_ptr64 Coq_Init_Datatypes_S_arg_0;
};

extern unsigned int get_unboxed_ordinal(int_or_ptr64);
extern unsigned int get_boxed_ordinal(int_or_ptr64);
extern int_or_ptr64 make_Coq_Init_Datatypes_nat_O(void);
extern int_or_ptr64 make_Coq_Init_Datatypes_nat_S(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, int_or_ptr64);
extern unsigned int get_Coq_Init_Datatypes_nat_tag(int_or_ptr64);
extern struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(int_or_ptr64);
extern void print_Coq_Init_Datatypes_nat(int_or_ptr64);
extern int_or_ptr64 call(struct thread_info *, int_or_ptr64, int_or_ptr64);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Init_Datatypes_nat[2][2];


