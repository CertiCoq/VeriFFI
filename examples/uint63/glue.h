typedef void * __attribute((aligned(4))) int_or_ptr32;
typedef void * __attribute((aligned(8))) int_or_ptr64;
struct thread_info;
struct closure;
struct Coq_Numbers_BinNums_xI_args;
struct Coq_Numbers_BinNums_xO_args;
struct Coq_Numbers_BinNums_xH_args;
struct Coq_Numbers_BinNums_Z0_args;
struct Coq_Numbers_BinNums_Zpos_args;
struct Coq_Numbers_BinNums_Zneg_args;
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

struct Coq_Numbers_BinNums_xI_args {
  int_or_ptr64 Coq_Numbers_BinNums_xI_arg_0;
};

struct Coq_Numbers_BinNums_xO_args {
  int_or_ptr64 Coq_Numbers_BinNums_xO_arg_0;
};

struct Coq_Numbers_BinNums_xH_args {
};

struct Coq_Numbers_BinNums_Z0_args {
};

struct Coq_Numbers_BinNums_Zpos_args {
  int_or_ptr64 Coq_Numbers_BinNums_Zpos_arg_0;
};

struct Coq_Numbers_BinNums_Zneg_args {
  int_or_ptr64 Coq_Numbers_BinNums_Zneg_arg_0;
};

extern unsigned int get_unboxed_ordinal(int_or_ptr64);
extern unsigned int get_boxed_ordinal(int_or_ptr64);
extern int_or_ptr64 make_Coq_Numbers_BinNums_positive_xI(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_Coq_Numbers_BinNums_positive_xI(struct thread_info *, int_or_ptr64);
extern int_or_ptr64 make_Coq_Numbers_BinNums_positive_xO(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_Coq_Numbers_BinNums_positive_xO(struct thread_info *, int_or_ptr64);
extern int_or_ptr64 make_Coq_Numbers_BinNums_positive_xH(void);
extern int_or_ptr64 make_Coq_Numbers_BinNums_Z_Z0(void);
extern int_or_ptr64 make_Coq_Numbers_BinNums_Z_Zpos(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_Coq_Numbers_BinNums_Z_Zpos(struct thread_info *, int_or_ptr64);
extern int_or_ptr64 make_Coq_Numbers_BinNums_Z_Zneg(int_or_ptr64, int_or_ptr64 *);
extern int_or_ptr64 alloc_make_Coq_Numbers_BinNums_Z_Zneg(struct thread_info *, int_or_ptr64);
extern unsigned int get_Coq_Numbers_BinNums_positive_tag(int_or_ptr64);
extern unsigned int get_Coq_Numbers_BinNums_Z_tag(int_or_ptr64);
extern struct Coq_Numbers_BinNums_xI_args *get_Coq_Numbers_BinNums_xI_args(int_or_ptr64);
extern struct Coq_Numbers_BinNums_xO_args *get_Coq_Numbers_BinNums_xO_args(int_or_ptr64);
extern struct Coq_Numbers_BinNums_xH_args *get_Coq_Numbers_BinNums_xH_args(int_or_ptr64);
extern struct Coq_Numbers_BinNums_Z0_args *get_Coq_Numbers_BinNums_Z0_args(int_or_ptr64);
extern struct Coq_Numbers_BinNums_Zpos_args *get_Coq_Numbers_BinNums_Zpos_args(int_or_ptr64);
extern struct Coq_Numbers_BinNums_Zneg_args *get_Coq_Numbers_BinNums_Zneg_args(int_or_ptr64);
extern void print_Coq_Numbers_BinNums_positive(int_or_ptr64);
extern void print_Coq_Numbers_BinNums_Z(int_or_ptr64);
extern void halt(struct thread_info *, int_or_ptr64, int_or_ptr64);
extern int_or_ptr64 call(struct thread_info *, int_or_ptr64, int_or_ptr64);
extern signed char const lparen_lit[2];

extern signed char const rparen_lit[2];

extern signed char const space_lit[2];

extern signed char const fun_lit[6];

extern signed char const type_lit[7];

extern signed char const unk_lit[6];

extern signed char const prop_lit[7];

extern signed char const names_of_Coq_Numbers_BinNums_positive[3][3];

extern signed char const names_of_Coq_Numbers_BinNums_Z[3][5];

extern int_or_ptr64 const halt_clo[2];


