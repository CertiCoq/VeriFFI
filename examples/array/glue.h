typedef void * __attribute((aligned(4))) int_or_ptr32;
typedef void * __attribute((aligned(8))) int_or_ptr64;
struct thread_info;
struct closure;
struct Coq_Init_Datatypes_tt_args;
struct Coq_Init_Datatypes_O_args;
struct Coq_Init_Datatypes_S_args;
struct Coq_Init_Datatypes_true_args;
struct Coq_Init_Datatypes_false_args;
struct Coq_Init_Datatypes_pair_args;
struct Coq_Init_Datatypes_Some_args;
struct Coq_Init_Datatypes_None_args;
struct prog_C_pureI_args;
struct prog_C_bindI_args;
struct prog_C_setI_args;
struct prog_C_getI_args;
struct thread_info {
  int_or_ptr64 *alloc;
  int_or_ptr64 *limit;
  struct heap *heap;
  int_or_ptr64 args[1024];
};

struct closure {
  void (*func)(struct thread_info, int_or_ptr64, int_or_ptr64);
  int_or_ptr64 env;
};

struct Coq_Init_Datatypes_tt_args {
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

struct Coq_Init_Datatypes_pair_args {
  int_or_ptr64 Coq_Init_Datatypes_pair_arg_0;
  int_or_ptr64 Coq_Init_Datatypes_pair_arg_1;
};

struct Coq_Init_Datatypes_Some_args {
  int_or_ptr64 Coq_Init_Datatypes_Some_arg_0;
};

struct Coq_Init_Datatypes_None_args {
};

struct prog_C_pureI_args {
  int_or_ptr64 prog_C_pureI_arg_0;
  int_or_ptr64 prog_C_pureI_arg_1;
};

struct prog_C_bindI_args {
  int_or_ptr64 prog_C_bindI_arg_0;
  int_or_ptr64 prog_C_bindI_arg_1;
  int_or_ptr64 prog_C_bindI_arg_2;
  int_or_ptr64 prog_C_bindI_arg_3;
};

struct prog_C_setI_args {
  int_or_ptr64 prog_C_setI_arg_0;
  int_or_ptr64 prog_C_setI_arg_1;
};

struct prog_C_getI_args {
  int_or_ptr64 prog_C_getI_arg_0;
};

extern unsigned int get_unboxed_ordinal(int_or_ptr64);
extern unsigned int get_boxed_ordinal(int_or_ptr64);
extern int_or_ptr64 make_Coq_Init_Datatypes_unit_tt(void);
extern int_or_ptr64 make_Coq_Init_Datatypes_nat_O(void);
extern int_or_ptr64 make_Coq_Init_Datatypes_nat_S(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, int_or_ptr64);
extern int_or_ptr64 make_Coq_Init_Datatypes_bool_true(void);
extern int_or_ptr64 make_Coq_Init_Datatypes_bool_false(void);
extern int_or_ptr64 make_Coq_Init_Datatypes_prod_pair(int_or_ptr64, int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_Coq_Init_Datatypes_prod_pair(struct thread_info *, int_or_ptr64, int_or_ptr64);
extern int_or_ptr64 make_Coq_Init_Datatypes_option_Some(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_Coq_Init_Datatypes_option_Some(struct thread_info *, int_or_ptr64);
extern int_or_ptr64 make_Coq_Init_Datatypes_option_None(void);
extern int_or_ptr64 make_prog_C_MI_pureI(int_or_ptr64, int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_prog_C_MI_pureI(struct thread_info *, int_or_ptr64, int_or_ptr64);
extern int_or_ptr64 make_prog_C_MI_bindI(int_or_ptr64, int_or_ptr64, int_or_ptr64, int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_prog_C_MI_bindI(struct thread_info *, int_or_ptr64, int_or_ptr64, int_or_ptr64, int_or_ptr64);
extern int_or_ptr64 make_prog_C_MI_setI(int_or_ptr64, int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_prog_C_MI_setI(struct thread_info *, int_or_ptr64, int_or_ptr64);
extern int_or_ptr64 make_prog_C_MI_getI(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_prog_C_MI_getI(struct thread_info *, int_or_ptr64);
extern unsigned int get_Coq_Init_Datatypes_unit_tag(int_or_ptr64);
extern unsigned int get_Coq_Init_Datatypes_nat_tag(int_or_ptr64);
extern unsigned int get_Coq_Init_Datatypes_bool_tag(int_or_ptr64);
extern unsigned int get_Coq_Init_Datatypes_prod_tag(int_or_ptr64);
extern unsigned int get_Coq_Init_Datatypes_option_tag(int_or_ptr64);
extern unsigned int get_prog_C_MI_tag(int_or_ptr64);
extern struct Coq_Init_Datatypes_tt_args *get_Coq_Init_Datatypes_tt_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_true_args *get_Coq_Init_Datatypes_true_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_false_args *get_Coq_Init_Datatypes_false_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_pair_args *get_Coq_Init_Datatypes_pair_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_Some_args *get_Coq_Init_Datatypes_Some_args(int_or_ptr64);
extern struct Coq_Init_Datatypes_None_args *get_Coq_Init_Datatypes_None_args(int_or_ptr64);
extern struct prog_C_pureI_args *get_prog_C_pureI_args(int_or_ptr64);
extern struct prog_C_bindI_args *get_prog_C_bindI_args(int_or_ptr64);
extern struct prog_C_setI_args *get_prog_C_setI_args(int_or_ptr64);
extern struct prog_C_getI_args *get_prog_C_getI_args(int_or_ptr64);
extern void print_Coq_Init_Datatypes_unit(int_or_ptr64);
extern void print_Coq_Init_Datatypes_nat(int_or_ptr64);
extern void print_Coq_Init_Datatypes_bool(int_or_ptr64);
extern void print_Coq_Init_Datatypes_prod(int_or_ptr64, void (*)(int_or_ptr64), void (*)(int_or_ptr64));
extern void print_Coq_Init_Datatypes_option(int_or_ptr64, void (*)(int_or_ptr64));
extern void print_prog_C_MI(int_or_ptr64);
extern void halt(struct thread_info *, int_or_ptr64, int_or_ptr64);
extern int_or_ptr64 call(struct thread_info *, int_or_ptr64, int_or_ptr64);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Init_Datatypes_unit[1][3];

extern signed char const names_of_Coq_Init_Datatypes_nat[2][2];

extern signed char const names_of_Coq_Init_Datatypes_bool[2][6];

extern signed char const names_of_Coq_Init_Datatypes_prod[1][5];

extern signed char const names_of_Coq_Init_Datatypes_option[2][5];

extern signed char const names_of_prog_C_MI[4][6];

extern int_or_ptr64 const halt_clo[2];


