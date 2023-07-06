typedef void * __attribute((aligned(4))) int_or_ptr32;
typedef void * __attribute((aligned(8))) int_or_ptr64;
struct closure;
struct stack_frame;
struct thread_info;
struct Coq_Init_Datatypes_O_args;
struct Coq_Init_Datatypes_S_args;
struct Coq_Init_Datatypes_true_args;
struct Coq_Init_Datatypes_false_args;
struct prog_etrue_args;
struct prog_efalse_args;
struct prog_eand_args;
struct prog_eor_args;
struct prog_eif_args;
struct Coq_Init_Datatypes_tt_args;
struct prog_mkT_args;
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

struct Coq_Init_Datatypes_true_args {
};

struct Coq_Init_Datatypes_false_args {
};

struct prog_etrue_args {
};

struct prog_efalse_args {
};

struct prog_eand_args {
  int_or_ptr64 prog_eand_arg_0;
};

struct prog_eor_args {
  int_or_ptr64 prog_eor_arg_0;
};

struct prog_eif_args {
  int_or_ptr64 prog_eif_arg_0;
  int_or_ptr64 prog_eif_arg_1;
  int_or_ptr64 prog_eif_arg_2;
};

struct Coq_Init_Datatypes_tt_args {
};

struct prog_mkT_args {
  int_or_ptr64 prog_mkT_arg_0;
  int_or_ptr64 prog_mkT_arg_1;
  int_or_ptr64 prog_mkT_arg_2;
};

extern unsigned int get_unboxed_ordinal(int_or_ptr64);
extern unsigned int get_boxed_ordinal(int_or_ptr64);
extern int_or_ptr64 make_Coq_Init_Datatypes_nat_O(void);
extern int_or_ptr64 make_Coq_Init_Datatypes_nat_S(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, int_or_ptr64);
extern int_or_ptr64 make_Coq_Init_Datatypes_bool_true(void);
extern int_or_ptr64 make_Coq_Init_Datatypes_bool_false(void);
extern int_or_ptr64 make_prog_exp_etrue(void);
extern int_or_ptr64 make_prog_exp_efalse(void);
extern int_or_ptr64 make_prog_exp_eand(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_prog_exp_eand(struct thread_info *, int_or_ptr64);
extern int_or_ptr64 make_prog_exp_eor(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_prog_exp_eor(struct thread_info *, int_or_ptr64);
extern int_or_ptr64 make_prog_exp_eif(int_or_ptr64, int_or_ptr64, int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_prog_exp_eif(struct thread_info *, int_or_ptr64, int_or_ptr64, int_or_ptr64);
extern int_or_ptr64 make_Coq_Init_Datatypes_unit_tt(void);
extern int_or_ptr64 make_prog_T_mkT(int_or_ptr64, int_or_ptr64, int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_prog_T_mkT(struct thread_info *, int_or_ptr64, int_or_ptr64, int_or_ptr64);
extern unsigned int get_Coq_Init_Datatypes_nat_tag(int_or_ptr64);
extern unsigned int get_Coq_Init_Datatypes_bool_tag(int_or_ptr64);
extern unsigned int get_prog_exp_tag(int_or_ptr64);
extern unsigned int get_Coq_Init_Datatypes_unit_tag(int_or_ptr64);
extern unsigned int get_prog_T_tag(int_or_ptr64);
extern struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_true_args *get_Coq_Init_Datatypes_true_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_false_args *get_Coq_Init_Datatypes_false_args(int_or_ptr64);
extern struct prog_etrue_args *get_prog_etrue_args(int_or_ptr64);
extern struct prog_efalse_args *get_prog_efalse_args(int_or_ptr64);
extern struct prog_eand_args *get_prog_eand_args(int_or_ptr64);
extern struct prog_eor_args *get_prog_eor_args(int_or_ptr64);
extern struct prog_eif_args *get_prog_eif_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_tt_args *get_Coq_Init_Datatypes_tt_args(int_or_ptr64);
extern struct prog_mkT_args *get_prog_mkT_args(int_or_ptr64);
extern void print_Coq_Init_Datatypes_nat(int_or_ptr64);
extern void print_Coq_Init_Datatypes_bool(int_or_ptr64);
extern void print_prog_exp(int_or_ptr64);
extern void print_Coq_Init_Datatypes_unit(int_or_ptr64);
extern void print_prog_T(int_or_ptr64);
extern int_or_ptr64 call(struct thread_info *, int_or_ptr64, int_or_ptr64);
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


