
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

extern int printf(signed char *);
extern _Bool is_ptr(void * __attribute((aligned(8))) *);
unsigned int get_unboxed_ordinal(void * __attribute((aligned(8))) *);
unsigned int get_boxed_ordinal(void * __attribute((aligned(8))) *);
void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_nat_O(void);
void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_nat_S(void * __attribute((aligned(8))) *, unsigned long long *);
void * __attribute((aligned(8))) *alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, void * __attribute((aligned(8))) *);
void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_bool_true(void);
void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_bool_false(void);
void * __attribute((aligned(8))) *make_prog_exp_etrue(void);
void * __attribute((aligned(8))) *make_prog_exp_efalse(void);
void * __attribute((aligned(8))) *make_prog_exp_eand(void * __attribute((aligned(8))) *, unsigned long long *);
void * __attribute((aligned(8))) *alloc_make_prog_exp_eand(struct thread_info *, void * __attribute((aligned(8))) *);
void * __attribute((aligned(8))) *make_prog_exp_eor(void * __attribute((aligned(8))) *, unsigned long long *);
void * __attribute((aligned(8))) *alloc_make_prog_exp_eor(struct thread_info *, void * __attribute((aligned(8))) *);
void * __attribute((aligned(8))) *make_prog_exp_eif(void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, unsigned long long *);
void * __attribute((aligned(8))) *alloc_make_prog_exp_eif(struct thread_info *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *);
void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_unit_tt(void);
void * __attribute((aligned(8))) *make_prog_T_mkT(void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, unsigned long long *);
void * __attribute((aligned(8))) *alloc_make_prog_T_mkT(struct thread_info *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *);
unsigned int get_Coq_Init_Datatypes_nat_tag(void * __attribute((aligned(8))) *);
unsigned int get_Coq_Init_Datatypes_bool_tag(void * __attribute((aligned(8))) *);
unsigned int get_prog_exp_tag(void * __attribute((aligned(8))) *);
unsigned int get_Coq_Init_Datatypes_unit_tag(void * __attribute((aligned(8))) *);
unsigned int get_prog_T_tag(void * __attribute((aligned(8))) *);
struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(void * __attribute((aligned(8))) *);
struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(void * __attribute((aligned(8))) *);
struct Coq_Init_Datatypes_true_args *get_Coq_Init_Datatypes_true_args(void * __attribute((aligned(8))) *);
struct Coq_Init_Datatypes_false_args *get_Coq_Init_Datatypes_false_args(void * __attribute((aligned(8))) *);
struct prog_etrue_args *get_prog_etrue_args(void * __attribute((aligned(8))) *);
struct prog_efalse_args *get_prog_efalse_args(void * __attribute((aligned(8))) *);
struct prog_eand_args *get_prog_eand_args(void * __attribute((aligned(8))) *);
struct prog_eor_args *get_prog_eor_args(void * __attribute((aligned(8))) *);
struct prog_eif_args *get_prog_eif_args(void * __attribute((aligned(8))) *);
struct Coq_Init_Datatypes_tt_args *get_Coq_Init_Datatypes_tt_args(void * __attribute((aligned(8))) *);
struct prog_mkT_args *get_prog_mkT_args(void * __attribute((aligned(8))) *);
void print_Coq_Init_Datatypes_nat(void * __attribute((aligned(8))) *);
void print_Coq_Init_Datatypes_bool(void * __attribute((aligned(8))) *);
void print_prog_exp(void * __attribute((aligned(8))) *);
void print_Coq_Init_Datatypes_unit(void * __attribute((aligned(8))) *);
void print_prog_T(void * __attribute((aligned(8))) *);
void halt(struct thread_info *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *);
void * __attribute((aligned(8))) *call(struct thread_info *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *);
signed char const lparen_lit[2] = { 40, 0, };

signed char const rparen_lit[2] = { 41, 0, };

signed char const space_lit[2] = { 32, 0, };

signed char const fun_lit[6] = { 60, 102, 117, 110, 62, 0, };

signed char const type_lit[7] = { 60, 116, 121, 112, 101, 62, 0, };

signed char const unk_lit[6] = { 60, 117, 110, 107, 62, 0, };

signed char const prop_lit[7] = { 60, 112, 114, 111, 112, 62, 0, };

unsigned int get_unboxed_ordinal(void * __attribute((aligned(8))) *$v)
{
  return (unsigned long long) $v >> 1LL;
}

unsigned int get_boxed_ordinal(void * __attribute((aligned(8))) *$v)
{
  return *((unsigned long long *) $v + 18446744073709551615LLU) & 255LL;
}

signed char const names_of_Coq_Init_Datatypes_nat[2][2] = { 79, 0, 83, 0,
  /* skip 0 */ };

signed char const names_of_Coq_Init_Datatypes_bool[2][6] = { 116, 114, 117,
  101, 0, 0, 102, 97, 108, 115, 101, 0, /* skip 0 */ };

signed char const names_of_prog_exp[5][7] = { 101, 116, 114, 117, 101, 0, 0,
  101, 102, 97, 108, 115, 101, 0, 101, 97, 110, 100, 0, 0, 0, 101, 111, 114,
  0, 0, 0, 0, 101, 105, 102, 0, 0, 0, 0, /* skip 0 */ };

signed char const names_of_Coq_Init_Datatypes_unit[1][3] = { 116, 116, 0,
  /* skip 0 */ };

signed char const names_of_prog_T[1][4] = { 109, 107, 84, 0, /* skip 0 */ };

void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_nat_O(void)
{
  return 1;
}

void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_nat_S(void * __attribute((aligned(8))) *$arg0, unsigned long long *$argv)
{
  *((unsigned long long *) $argv + 0LLU) = 1024LL;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  return $argv + 1LL;
}

void * __attribute((aligned(8))) *alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *$tinfo, void * __attribute((aligned(8))) *$arg0)
{
  register unsigned long long *$argv;
  $argv = (*$tinfo).alloc;
  *((unsigned long long *) $argv + 0LLU) = 1024LL;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_bool_true(void)
{
  return 1;
}

void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_bool_false(void)
{
  return 3;
}

void * __attribute((aligned(8))) *make_prog_exp_etrue(void)
{
  return 1;
}

void * __attribute((aligned(8))) *make_prog_exp_efalse(void)
{
  return 3;
}

void * __attribute((aligned(8))) *make_prog_exp_eand(void * __attribute((aligned(8))) *$arg0, unsigned long long *$argv)
{
  *((unsigned long long *) $argv + 0LLU) = 1024LL;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  return $argv + 1LL;
}

void * __attribute((aligned(8))) *alloc_make_prog_exp_eand(struct thread_info *$tinfo, void * __attribute((aligned(8))) *$arg0)
{
  register unsigned long long *$argv;
  $argv = (*$tinfo).alloc;
  *((unsigned long long *) $argv + 0LLU) = 1024LL;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

void * __attribute((aligned(8))) *make_prog_exp_eor(void * __attribute((aligned(8))) *$arg0, unsigned long long *$argv)
{
  *((unsigned long long *) $argv + 0LLU) = 1025LL;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  return $argv + 1LL;
}

void * __attribute((aligned(8))) *alloc_make_prog_exp_eor(struct thread_info *$tinfo, void * __attribute((aligned(8))) *$arg0)
{
  register unsigned long long *$argv;
  $argv = (*$tinfo).alloc;
  *((unsigned long long *) $argv + 0LLU) = 1025LL;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

void * __attribute((aligned(8))) *make_prog_exp_eif(void * __attribute((aligned(8))) *$arg0, void * __attribute((aligned(8))) *$arg1, void * __attribute((aligned(8))) *$arg2, unsigned long long *$argv)
{
  *((unsigned long long *) $argv + 0LLU) = 3074LL;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  *((unsigned long long *) $argv + 2LLU) = $arg1;
  *((unsigned long long *) $argv + 3LLU) = $arg2;
  return $argv + 1LL;
}

void * __attribute((aligned(8))) *alloc_make_prog_exp_eif(struct thread_info *$tinfo, void * __attribute((aligned(8))) *$arg0, void * __attribute((aligned(8))) *$arg1, void * __attribute((aligned(8))) *$arg2)
{
  register unsigned long long *$argv;
  $argv = (*$tinfo).alloc;
  *((unsigned long long *) $argv + 0LLU) = 3074LL;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  *((unsigned long long *) $argv + 2LLU) = $arg1;
  *((unsigned long long *) $argv + 3LLU) = $arg2;
  (*$tinfo).alloc = (*$tinfo).alloc + 4LL;
  return $argv + 1LL;
}

void * __attribute((aligned(8))) *make_Coq_Init_Datatypes_unit_tt(void)
{
  return 1;
}

void * __attribute((aligned(8))) *make_prog_T_mkT(void * __attribute((aligned(8))) *$arg0, void * __attribute((aligned(8))) *$arg1, void * __attribute((aligned(8))) *$arg2, unsigned long long *$argv)
{
  *((unsigned long long *) $argv + 0LLU) = 3072LL;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  *((unsigned long long *) $argv + 2LLU) = $arg1;
  *((unsigned long long *) $argv + 3LLU) = $arg2;
  return $argv + 1LL;
}

void * __attribute((aligned(8))) *alloc_make_prog_T_mkT(struct thread_info *$tinfo, void * __attribute((aligned(8))) *$arg0, void * __attribute((aligned(8))) *$arg1, void * __attribute((aligned(8))) *$arg2)
{
  register unsigned long long *$argv;
  $argv = (*$tinfo).alloc;
  *((unsigned long long *) $argv + 0LLU) = 3072LL;
  *((unsigned long long *) $argv + 1LLU) = $arg0;
  *((unsigned long long *) $argv + 2LLU) = $arg1;
  *((unsigned long long *) $argv + 3LLU) = $arg2;
  (*$tinfo).alloc = (*$tinfo).alloc + 4LL;
  return $argv + 1LL;
}

unsigned int get_Coq_Init_Datatypes_nat_tag(void * __attribute((aligned(8))) *$v)
{
  register _Bool $b;
  register unsigned int $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1U;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0U;
      
    }
  }
}

unsigned int get_Coq_Init_Datatypes_bool_tag(void * __attribute((aligned(8))) *$v)
{
  register unsigned int $t;
  $t = get_unboxed_ordinal($v);
  return $t;
}

unsigned int get_prog_exp_tag(void * __attribute((aligned(8))) *$v)
{
  register _Bool $b;
  register unsigned int $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 2U;
      case 1:
        return 3U;
      case 2:
        return 4U;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0U;
      case 1:
        return 1U;
      
    }
  }
}

unsigned int get_Coq_Init_Datatypes_unit_tag(void * __attribute((aligned(8))) *$v)
{
  register unsigned int $t;
  $t = get_unboxed_ordinal($v);
  return $t;
}

unsigned int get_prog_T_tag(void * __attribute((aligned(8))) *$v)
{
  register unsigned int $t;
  $t = get_boxed_ordinal($v);
  return $t;
}

struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(void * __attribute((aligned(8))) *$v)
{
  return (struct Coq_Init_Datatypes_O_args *) 0;
}

struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(void * __attribute((aligned(8))) *$v)
{
  return (struct Coq_Init_Datatypes_S_args *) $v;
}

struct Coq_Init_Datatypes_true_args *get_Coq_Init_Datatypes_true_args(void * __attribute((aligned(8))) *$v)
{
  return (struct Coq_Init_Datatypes_true_args *) 0;
}

struct Coq_Init_Datatypes_false_args *get_Coq_Init_Datatypes_false_args(void * __attribute((aligned(8))) *$v)
{
  return (struct Coq_Init_Datatypes_false_args *) 0;
}

struct prog_etrue_args *get_prog_etrue_args(void * __attribute((aligned(8))) *$v)
{
  return (struct prog_etrue_args *) 0;
}

struct prog_efalse_args *get_prog_efalse_args(void * __attribute((aligned(8))) *$v)
{
  return (struct prog_efalse_args *) 0;
}

struct prog_eand_args *get_prog_eand_args(void * __attribute((aligned(8))) *$v)
{
  return (struct prog_eand_args *) $v;
}

struct prog_eor_args *get_prog_eor_args(void * __attribute((aligned(8))) *$v)
{
  return (struct prog_eor_args *) $v;
}

struct prog_eif_args *get_prog_eif_args(void * __attribute((aligned(8))) *$v)
{
  return (struct prog_eif_args *) $v;
}

struct Coq_Init_Datatypes_tt_args *get_Coq_Init_Datatypes_tt_args(void * __attribute((aligned(8))) *$v)
{
  return (struct Coq_Init_Datatypes_tt_args *) 0;
}

struct prog_mkT_args *get_prog_mkT_args(void * __attribute((aligned(8))) *$v)
{
  return (struct prog_mkT_args *) $v;
}

void print_Coq_Init_Datatypes_nat(void * __attribute((aligned(8))) *$v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Init_Datatypes_nat_tag($v);
  switch ($tag) {
    case 0:
      printf(*(names_of_Coq_Init_Datatypes_nat + $tag));
      break;
    case 1:
      $args = get_Coq_Init_Datatypes_S_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Init_Datatypes_nat + $tag));
      printf(space_lit);
      print_Coq_Init_Datatypes_nat
        (*((void * __attribute((aligned(8))) **) $args + 0));
      printf(rparen_lit);
      break;
    
  }
}

void print_Coq_Init_Datatypes_bool(void * __attribute((aligned(8))) *$v)
{
  register unsigned int $tag;
  $tag = get_Coq_Init_Datatypes_bool_tag($v);
  printf(*(names_of_Coq_Init_Datatypes_bool + $tag));
}

void print_prog_exp(void * __attribute((aligned(8))) *$v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_prog_exp_tag($v);
  switch ($tag) {
    case 0:
      printf(*(names_of_prog_exp + $tag));
      break;
    case 1:
      printf(*(names_of_prog_exp + $tag));
      break;
    case 2:
      $args = get_prog_eand_args($v);
      printf(lparen_lit);
      printf(*(names_of_prog_exp + $tag));
      printf(space_lit);
      print_prog_exp(*((void * __attribute((aligned(8))) **) $args + 0));
      printf(rparen_lit);
      break;
    case 3:
      $args = get_prog_eor_args($v);
      printf(lparen_lit);
      printf(*(names_of_prog_exp + $tag));
      printf(space_lit);
      print_prog_exp(*((void * __attribute((aligned(8))) **) $args + 0));
      printf(rparen_lit);
      break;
    case 4:
      $args = get_prog_eif_args($v);
      printf(lparen_lit);
      printf(*(names_of_prog_exp + $tag));
      printf(space_lit);
      print_prog_exp(*((void * __attribute((aligned(8))) **) $args + 0));
      printf(space_lit);
      print_prog_exp(*((void * __attribute((aligned(8))) **) $args + 1));
      printf(space_lit);
      print_prog_exp(*((void * __attribute((aligned(8))) **) $args + 2));
      printf(rparen_lit);
      break;
    
  }
}

void print_Coq_Init_Datatypes_unit(void * __attribute((aligned(8))) *$v)
{
  register unsigned int $tag;
  $tag = get_Coq_Init_Datatypes_unit_tag($v);
  printf(*(names_of_Coq_Init_Datatypes_unit + $tag));
}

void print_prog_T(void * __attribute((aligned(8))) *$v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_prog_T_tag($v);
  switch ($tag) {
    case 0:
      $args = get_prog_mkT_args($v);
      printf(lparen_lit);
      printf(*(names_of_prog_T + $tag));
      printf(space_lit);
      print_Coq_Init_Datatypes_nat
        (*((void * __attribute((aligned(8))) **) $args + 0));
      printf(space_lit);
      print_Coq_Init_Datatypes_bool
        (*((void * __attribute((aligned(8))) **) $args + 1));
      printf(space_lit);
      print_Coq_Init_Datatypes_unit
        (*((void * __attribute((aligned(8))) **) $args + 2));
      printf(rparen_lit);
      break;
    
  }
}

void halt(struct thread_info *$tinfo, void * __attribute((aligned(8))) *$env, void * __attribute((aligned(8))) *$arg)
{
  *((unsigned long long *) (*$tinfo).args + 1LLU) = $arg;
  return;
}

void * __attribute((aligned(8))) *const halt_clo[2] = { &halt, 1LL, };

void * __attribute((aligned(8))) *call(struct thread_info *$tinfo, void * __attribute((aligned(8))) *$clo, void * __attribute((aligned(8))) *$arg)
{
  register unsigned long long *$f;
  register unsigned long long *$envi;
  $f = *((unsigned long long *) $clo + 0LLU);
  $envi = *((unsigned long long *) $clo + 1LLU);
  ((void (*)(struct thread_info *, void * __attribute((aligned(8))) *, void * __attribute((aligned(8))) *)) 
    $f)
    ($tinfo, $envi, $arg);
  return *((unsigned long long *) (*$tinfo).args + 1LLU);
}


