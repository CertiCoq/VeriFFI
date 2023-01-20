
struct thread_info;
struct Coq_Numbers_BinNums_xI_args;
struct Coq_Numbers_BinNums_xO_args;
struct Coq_Numbers_BinNums_xH_args;
struct Coq_Numbers_BinNums_Z0_args;
struct Coq_Numbers_BinNums_Zpos_args;
struct Coq_Numbers_BinNums_Zneg_args;
struct thread_info {
  unsigned long long *alloc;
  unsigned long long *limit;
  struct heap *heap;
  unsigned long long args[1024];
};

struct Coq_Numbers_BinNums_xI_args {
  unsigned long long Coq_Numbers_BinNums_xI_arg_0;
};

struct Coq_Numbers_BinNums_xO_args {
  unsigned long long Coq_Numbers_BinNums_xO_arg_0;
};

struct Coq_Numbers_BinNums_xH_args {
};

struct Coq_Numbers_BinNums_Z0_args {
};

struct Coq_Numbers_BinNums_Zpos_args {
  unsigned long long Coq_Numbers_BinNums_Zpos_arg_0;
};

struct Coq_Numbers_BinNums_Zneg_args {
  unsigned long long Coq_Numbers_BinNums_Zneg_arg_0;
};

extern unsigned int get_unboxed_ordinal(unsigned long long);
extern unsigned int get_boxed_ordinal(unsigned long long);
extern unsigned long long make_Coq_Numbers_BinNums_positive_xI(unsigned long long, unsigned long long *);
extern unsigned long long alloc_make_Coq_Numbers_BinNums_positive_xI(struct thread_info *, unsigned long long);
extern unsigned long long make_Coq_Numbers_BinNums_positive_xO(unsigned long long, unsigned long long *);
extern unsigned long long alloc_make_Coq_Numbers_BinNums_positive_xO(struct thread_info *, unsigned long long);
extern unsigned long long make_Coq_Numbers_BinNums_positive_xH(void);
extern unsigned long long make_Coq_Numbers_BinNums_Z_Z0(void);
extern unsigned long long make_Coq_Numbers_BinNums_Z_Zpos(unsigned long long, unsigned long long *);
extern unsigned long long alloc_make_Coq_Numbers_BinNums_Z_Zpos(struct thread_info *, unsigned long long);
extern unsigned long long make_Coq_Numbers_BinNums_Z_Zneg(unsigned long long, unsigned long long *);
extern unsigned long long alloc_make_Coq_Numbers_BinNums_Z_Zneg(struct thread_info *, unsigned long long);
extern unsigned int get_Coq_Numbers_BinNums_positive_tag(unsigned long long);
extern unsigned int get_Coq_Numbers_BinNums_Z_tag(unsigned long long);
extern struct Coq_Numbers_BinNums_xI_args *get_Coq_Numbers_BinNums_xI_args(unsigned long long);
extern struct Coq_Numbers_BinNums_xO_args *get_Coq_Numbers_BinNums_xO_args(unsigned long long);
extern struct Coq_Numbers_BinNums_xH_args *get_Coq_Numbers_BinNums_xH_args(unsigned long long);
extern struct Coq_Numbers_BinNums_Z0_args *get_Coq_Numbers_BinNums_Z0_args(unsigned long long);
extern struct Coq_Numbers_BinNums_Zpos_args *get_Coq_Numbers_BinNums_Zpos_args(unsigned long long);
extern struct Coq_Numbers_BinNums_Zneg_args *get_Coq_Numbers_BinNums_Zneg_args(unsigned long long);
extern void print_Coq_Numbers_BinNums_positive(unsigned long long);
extern void print_Coq_Numbers_BinNums_Z(unsigned long long);
extern void halt(struct thread_info *, unsigned long long, unsigned long long);
extern unsigned long long call(struct thread_info *, unsigned long long, unsigned long long);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Numbers_BinNums_positive[3][3];

extern signed char const names_of_Coq_Numbers_BinNums_Z[3][5];

extern unsigned long long const halt_clo[2];


