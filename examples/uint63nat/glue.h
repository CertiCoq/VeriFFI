
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
struct thread_info {
  void * __attribute((aligned(8))) *alloc;
  void * __attribute((aligned(8))) *limit;
  struct heap *heap;
  void * __attribute((aligned(8))) *args[1024];
};

struct Coq_Init_Datatypes_O_args {
};

struct Coq_Init_Datatypes_S_args {
  void * __attribute((aligned(8))) *Coq_Init_Datatypes_S_arg_0;
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
  void * __attribute((aligned(8))) *prog_eand_arg_0;
};

struct prog_eor_args {
  void * __attribute((aligned(8))) *prog_eor_arg_0;
};

struct prog_eif_args {
  void * __attribute((aligned(8))) *prog_eif_arg_0;
  void * __attribute((aligned(8))) *prog_eif_arg_1;
  void * __attribute((aligned(8))) *prog_eif_arg_2;
};

struct Coq_Init_Datatypes_tt_args {
};

struct prog_mkT_args {
  void * __attribute((aligned(8))) *prog_mkT_arg_0;
  void * __attribute((aligned(8))) *prog_mkT_arg_1;
  void * __attribute((aligned(8))) *prog_mkT_arg_2;
};

extern unsigned int get_unboxed_ordinal(void * __attribute((aligned(8))) *);
extern unsigned int get_boxed_ordinal(void * __attribute((aligned(8))) *);
extern void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_nat_O(void);
extern void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_nat_S(void * __attribute((aligned(8))) *, unsigned long long *);
extern void * __attribute((aligned(8))) *alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, void * __attribute((aligned(8))) *);
extern void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_bool_true(void);
extern void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_bool_false(void);
extern void * __attribute((aligned(8))) *make_prog_exp_etrue(void);
extern void * __attribute((aligned(8))) *make_prog_exp_efalse(void);
extern void * __attribute((aligned(8))) *make_prog_exp_eand(void * __attribute((aligned(8))) *, unsigned long long *);
extern void * __attribute((aligned(8))) *alloc_make_prog_exp_eand(struct thread_info *, void * __attribute((aligned(8))) *);
extern void * __attribute((aligned(8))) *make_prog_exp_eor(void * __attribute((aligned(8))) *, unsigned long long *);
extern void * __attribute((aligned(8))) *alloc_make_prog_exp_eor(struct thread_info *, void * __attribute((aligned(8))) *);
extern void * __attribute((aligned(8))) *make_prog_exp_eif(void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, unsigned long long *);
extern void * __attribute((aligned(8))) *alloc_make_prog_exp_eif(struct thread_info *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *);
extern void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_unit_tt(void);
extern void * __attribute((aligned(8))) *make_prog_T_mkT(void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, unsigned long long *);
extern void * __attribute((aligned(8))) *alloc_make_prog_T_mkT(struct thread_info *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *);
extern unsigned int get_Coq_Init_Datatypes_nat_tag(void * __attribute((aligned(8))) *);
extern unsigned int get_Coq_Init_Datatypes_bool_tag(void * __attribute((aligned(8))) *);
extern unsigned int get_prog_exp_tag(void * __attribute((aligned(8))) *);
extern unsigned int get_Coq_Init_Datatypes_unit_tag(void * __attribute((aligned(8))) *);
extern unsigned int get_prog_T_tag(void * __attribute((aligned(8))) *);
extern struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(void * __attribute((aligned(8))) *);
extern struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(void * __attribute((aligned(8))) *);
extern struct Coq_Init_Datatypes_true_args *get_Coq_Init_Datatypes_true_args(void * __attribute((aligned(8))) *);
extern struct Coq_Init_Datatypes_false_args *get_Coq_Init_Datatypes_false_args(void * __attribute((aligned(8))) *);
extern struct prog_etrue_args *get_prog_etrue_args(void * __attribute((aligned(8))) *);
extern struct prog_efalse_args *get_prog_efalse_args(void * __attribute((aligned(8))) *);
extern struct prog_eand_args *get_prog_eand_args(void * __attribute((aligned(8))) *);
extern struct prog_eor_args *get_prog_eor_args(void * __attribute((aligned(8))) *);
extern struct prog_eif_args *get_prog_eif_args(void * __attribute((aligned(8))) *);
extern struct Coq_Init_Datatypes_tt_args *get_Coq_Init_Datatypes_tt_args(void * __attribute((aligned(8))) *);
extern struct prog_mkT_args *get_prog_mkT_args(void * __attribute((aligned(8))) *);
extern void print_Coq_Init_Datatypes_nat(void * __attribute((aligned(8))) *);
extern void print_Coq_Init_Datatypes_bool(void * __attribute((aligned(8))) *);
extern void print_prog_exp(void * __attribute((aligned(8))) *);
extern void print_Coq_Init_Datatypes_unit(void * __attribute((aligned(8))) *);
extern void print_prog_T(void * __attribute((aligned(8))) *);
extern void halt(struct thread_info *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *);
extern void * __attribute((aligned(8))) *call(struct thread_info *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *);
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

extern void * __attribute((aligned(8))) *const halt_clo[2];


