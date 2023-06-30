typedef void * __attribute((aligned(4))) int_or_ptr32;
typedef void * __attribute((aligned(8))) int_or_ptr64;
struct closure;
struct stack_frame;
struct thread_info;
struct Coq_Init_Datatypes_Some_args;
struct Coq_Init_Datatypes_None_args;
struct Coq_Init_Datatypes_O_args;
struct Coq_Init_Datatypes_S_args;
struct Coq_Init_Datatypes_tt_args;
struct prog_C_pureI_args;
struct prog_C_bindI_args;
struct prog_C_setI_args;
struct prog_C_getI_args;
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

struct Coq_Init_Datatypes_Some_args {
  int_or_ptr64 Coq_Init_Datatypes_Some_arg_0;
};

struct Coq_Init_Datatypes_None_args {
};

struct Coq_Init_Datatypes_O_args {
};

struct Coq_Init_Datatypes_S_args {
  int_or_ptr64 Coq_Init_Datatypes_S_arg_0;
};

struct Coq_Init_Datatypes_tt_args {
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

extern int printf(signed char *);
extern _Bool is_ptr(int_or_ptr64);
unsigned int get_unboxed_ordinal(int_or_ptr64);
unsigned int get_boxed_ordinal(int_or_ptr64);
int_or_ptr64 make_Coq_Init_Datatypes_option_Some(int_or_ptr64, int_or_ptr64 *);
int_or_ptr64 alloc_make_Coq_Init_Datatypes_option_Some(struct thread_info *, int_or_ptr64);
int_or_ptr64 make_Coq_Init_Datatypes_option_None(void);
int_or_ptr64 make_Coq_Init_Datatypes_nat_O(void);
int_or_ptr64 make_Coq_Init_Datatypes_nat_S(int_or_ptr64, int_or_ptr64 *);
int_or_ptr64 alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, int_or_ptr64);
int_or_ptr64 make_Coq_Init_Datatypes_unit_tt(void);
int_or_ptr64 make_prog_C_MI_pureI(int_or_ptr64, int_or_ptr64, int_or_ptr64 *);
int_or_ptr64 alloc_make_prog_C_MI_pureI(struct thread_info *, int_or_ptr64, int_or_ptr64);
int_or_ptr64 make_prog_C_MI_bindI(int_or_ptr64, int_or_ptr64, int_or_ptr64, int_or_ptr64, int_or_ptr64 *);
int_or_ptr64 alloc_make_prog_C_MI_bindI(struct thread_info *, int_or_ptr64, int_or_ptr64, int_or_ptr64, int_or_ptr64);
int_or_ptr64 make_prog_C_MI_setI(int_or_ptr64, int_or_ptr64, int_or_ptr64 *);
int_or_ptr64 alloc_make_prog_C_MI_setI(struct thread_info *, int_or_ptr64, int_or_ptr64);
int_or_ptr64 make_prog_C_MI_getI(int_or_ptr64, int_or_ptr64 *);
int_or_ptr64 alloc_make_prog_C_MI_getI(struct thread_info *, int_or_ptr64);
unsigned int get_Coq_Init_Datatypes_option_tag(int_or_ptr64);
unsigned int get_Coq_Init_Datatypes_nat_tag(int_or_ptr64);
unsigned int get_Coq_Init_Datatypes_unit_tag(int_or_ptr64);
unsigned int get_prog_C_MI_tag(int_or_ptr64);
struct Coq_Init_Datatypes_Some_args *get_Coq_Init_Datatypes_Some_args(int_or_ptr64);
struct Coq_Init_Datatypes_None_args *get_Coq_Init_Datatypes_None_args(int_or_ptr64);
struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(int_or_ptr64);
struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(int_or_ptr64);
struct Coq_Init_Datatypes_tt_args *get_Coq_Init_Datatypes_tt_args(int_or_ptr64);
struct prog_C_pureI_args *get_prog_C_pureI_args(int_or_ptr64);
struct prog_C_bindI_args *get_prog_C_bindI_args(int_or_ptr64);
struct prog_C_setI_args *get_prog_C_setI_args(int_or_ptr64);
struct prog_C_getI_args *get_prog_C_getI_args(int_or_ptr64);
void print_Coq_Init_Datatypes_option(int_or_ptr64, void (*)(int_or_ptr64));
void print_Coq_Init_Datatypes_nat(int_or_ptr64);
void print_Coq_Init_Datatypes_unit(int_or_ptr64);
void print_prog_C_MI(int_or_ptr64);
int_or_ptr64 call(struct thread_info *, int_or_ptr64, int_or_ptr64);
signed char const lparen_lit[2] = { 40, 0, };

signed char const rparen_lit[2] = { 41, 0, };

signed char const space_lit[2] = { 32, 0, };

signed char const fun_lit[6] = { 60, 102, 117, 110, 62, 0, };

signed char const type_lit[7] = { 60, 116, 121, 112, 101, 62, 0, };

signed char const unk_lit[6] = { 60, 117, 110, 107, 62, 0, };

signed char const prop_lit[7] = { 60, 112, 114, 111, 112, 62, 0, };

unsigned int get_unboxed_ordinal(int_or_ptr64 $v)
{
  return (unsigned long long) $v >> 1LL;
}

unsigned int get_boxed_ordinal(int_or_ptr64 $v)
{
  return *((unsigned long long *) $v + -1LL) & 255LL;
}

signed char const names_of_Coq_Init_Datatypes_option[2][5] = { 83, 111, 109,
  101, 0, 78, 111, 110, 101, 0, /* skip 0 */ };

signed char const names_of_Coq_Init_Datatypes_nat[2][2] = { 79, 0, 83, 0,
  /* skip 0 */ };

signed char const names_of_Coq_Init_Datatypes_unit[1][3] = { 116, 116, 0,
  /* skip 0 */ };

signed char const names_of_prog_C_MI[4][6] = { 112, 117, 114, 101, 73, 0, 98,
  105, 110, 100, 73, 0, 115, 101, 116, 73, 0, 0, 103, 101, 116, 73, 0, 0,
  /* skip 0 */ };

int_or_ptr64 make_Coq_Init_Datatypes_option_Some(int_or_ptr64 $arg0, int_or_ptr64 *$argv)
{
  *($argv + 0LL) = (int_or_ptr64) 1024LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

int_or_ptr64 alloc_make_Coq_Init_Datatypes_option_Some(struct thread_info *$tinfo, int_or_ptr64 $arg0)
{
  register int_or_ptr64 *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1024LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

int_or_ptr64 make_Coq_Init_Datatypes_option_None(void)
{
  return 1;
}

int_or_ptr64 make_Coq_Init_Datatypes_nat_O(void)
{
  return 1;
}

int_or_ptr64 make_Coq_Init_Datatypes_nat_S(int_or_ptr64 $arg0, int_or_ptr64 *$argv)
{
  *($argv + 0LL) = (int_or_ptr64) 1024LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

int_or_ptr64 alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *$tinfo, int_or_ptr64 $arg0)
{
  register int_or_ptr64 *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1024LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

int_or_ptr64 make_Coq_Init_Datatypes_unit_tt(void)
{
  return 1;
}

int_or_ptr64 make_prog_C_MI_pureI(int_or_ptr64 $arg0, int_or_ptr64 $arg1, int_or_ptr64 *$argv)
{
  *($argv + 0LL) = (int_or_ptr64) 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  return $argv + 1LL;
}

int_or_ptr64 alloc_make_prog_C_MI_pureI(struct thread_info *$tinfo, int_or_ptr64 $arg0, int_or_ptr64 $arg1)
{
  register int_or_ptr64 *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 2048LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  (*$tinfo).alloc = (*$tinfo).alloc + 3LL;
  return $argv + 1LL;
}

int_or_ptr64 make_prog_C_MI_bindI(int_or_ptr64 $arg0, int_or_ptr64 $arg1, int_or_ptr64 $arg2, int_or_ptr64 $arg3, int_or_ptr64 *$argv)
{
  *($argv + 0LL) = (int_or_ptr64) 4097LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  *($argv + 3LL) = $arg2;
  *($argv + 4LL) = $arg3;
  return $argv + 1LL;
}

int_or_ptr64 alloc_make_prog_C_MI_bindI(struct thread_info *$tinfo, int_or_ptr64 $arg0, int_or_ptr64 $arg1, int_or_ptr64 $arg2, int_or_ptr64 $arg3)
{
  register int_or_ptr64 *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 4097LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  *($argv + 3LL) = $arg2;
  *($argv + 4LL) = $arg3;
  (*$tinfo).alloc = (*$tinfo).alloc + 5LL;
  return $argv + 1LL;
}

int_or_ptr64 make_prog_C_MI_setI(int_or_ptr64 $arg0, int_or_ptr64 $arg1, int_or_ptr64 *$argv)
{
  *($argv + 0LL) = (int_or_ptr64) 2050LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  return $argv + 1LL;
}

int_or_ptr64 alloc_make_prog_C_MI_setI(struct thread_info *$tinfo, int_or_ptr64 $arg0, int_or_ptr64 $arg1)
{
  register int_or_ptr64 *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 2050LL;
  *($argv + 1LL) = $arg0;
  *($argv + 2LL) = $arg1;
  (*$tinfo).alloc = (*$tinfo).alloc + 3LL;
  return $argv + 1LL;
}

int_or_ptr64 make_prog_C_MI_getI(int_or_ptr64 $arg0, int_or_ptr64 *$argv)
{
  *($argv + 0LL) = (int_or_ptr64) 1027LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

int_or_ptr64 alloc_make_prog_C_MI_getI(struct thread_info *$tinfo, int_or_ptr64 $arg0)
{
  register int_or_ptr64 *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1027LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

unsigned int get_Coq_Init_Datatypes_option_tag(int_or_ptr64 $v)
{
  register _Bool $b;
  register unsigned int $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0U;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1U;
      
    }
  }
}

unsigned int get_Coq_Init_Datatypes_nat_tag(int_or_ptr64 $v)
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

unsigned int get_Coq_Init_Datatypes_unit_tag(int_or_ptr64 $v)
{
  register unsigned int $t;
  $t = get_unboxed_ordinal($v);
  return $t;
}

unsigned int get_prog_C_MI_tag(int_or_ptr64 $v)
{
  register unsigned int $t;
  $t = get_boxed_ordinal($v);
  return $t;
}

struct Coq_Init_Datatypes_Some_args *get_Coq_Init_Datatypes_Some_args(int_or_ptr64 $v)
{
  return (struct Coq_Init_Datatypes_Some_args *) $v;
}

struct Coq_Init_Datatypes_None_args *get_Coq_Init_Datatypes_None_args(int_or_ptr64 $v)
{
  return (struct Coq_Init_Datatypes_None_args *) 0;
}

struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(int_or_ptr64 $v)
{
  return (struct Coq_Init_Datatypes_O_args *) 0;
}

struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(int_or_ptr64 $v)
{
  return (struct Coq_Init_Datatypes_S_args *) $v;
}

struct Coq_Init_Datatypes_tt_args *get_Coq_Init_Datatypes_tt_args(int_or_ptr64 $v)
{
  return (struct Coq_Init_Datatypes_tt_args *) 0;
}

struct prog_C_pureI_args *get_prog_C_pureI_args(int_or_ptr64 $v)
{
  return (struct prog_C_pureI_args *) $v;
}

struct prog_C_bindI_args *get_prog_C_bindI_args(int_or_ptr64 $v)
{
  return (struct prog_C_bindI_args *) $v;
}

struct prog_C_setI_args *get_prog_C_setI_args(int_or_ptr64 $v)
{
  return (struct prog_C_setI_args *) $v;
}

struct prog_C_getI_args *get_prog_C_getI_args(int_or_ptr64 $v)
{
  return (struct prog_C_getI_args *) $v;
}

void print_Coq_Init_Datatypes_option(int_or_ptr64 $v, void $print_param_A(int_or_ptr64))
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Init_Datatypes_option_tag($v);
  switch ($tag) {
    case 0:
      $args = get_Coq_Init_Datatypes_Some_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Init_Datatypes_option + $tag));
      printf(space_lit);
      $print_param_A(*((int_or_ptr64 *) $args + 0));
      printf(rparen_lit);
      break;
    case 1:
      printf(*(names_of_Coq_Init_Datatypes_option + $tag));
      break;
    
  }
}

void print_Coq_Init_Datatypes_nat(int_or_ptr64 $v)
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
      print_Coq_Init_Datatypes_nat(*((int_or_ptr64 *) $args + 0));
      printf(rparen_lit);
      break;
    
  }
}

void print_Coq_Init_Datatypes_unit(int_or_ptr64 $v)
{
  register unsigned int $tag;
  $tag = get_Coq_Init_Datatypes_unit_tag($v);
  printf(*(names_of_Coq_Init_Datatypes_unit + $tag));
}

void print_prog_C_MI(int_or_ptr64 $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_prog_C_MI_tag($v);
  switch ($tag) {
    case 0:
      $args = get_prog_C_pureI_args($v);
      printf(lparen_lit);
      printf(*(names_of_prog_C_MI + $tag));
      printf(space_lit);
      printf(type_lit);
      printf(space_lit);
      printf(unk_lit);
      printf(rparen_lit);
      break;
    case 1:
      $args = get_prog_C_bindI_args($v);
      printf(lparen_lit);
      printf(*(names_of_prog_C_MI + $tag));
      printf(space_lit);
      printf(type_lit);
      printf(space_lit);
      printf(type_lit);
      printf(space_lit);
      printf(space_lit);
      printf(fun_lit);
      printf(rparen_lit);
      break;
    case 2:
      $args = get_prog_C_setI_args($v);
      printf(lparen_lit);
      printf(*(names_of_prog_C_MI + $tag));
      printf(space_lit);
      print_Coq_Init_Datatypes_nat(*((int_or_ptr64 *) $args + 0));
      printf(space_lit);
      printf(unk_lit);
      printf(rparen_lit);
      break;
    case 3:
      $args = get_prog_C_getI_args($v);
      printf(lparen_lit);
      printf(*(names_of_prog_C_MI + $tag));
      printf(space_lit);
      print_Coq_Init_Datatypes_nat(*((int_or_ptr64 *) $args + 0));
      printf(rparen_lit);
      break;
    
  }
}

int_or_ptr64 call(struct thread_info *$tinfo, int_or_ptr64 $clo, int_or_ptr64 $arg)
{
  register unsigned long long *$f;
  register unsigned long long *$envi;
  $f = (*((struct closure *) $clo)).func;
  $envi = (*((struct closure *) $clo)).env;
  ((void (*)(struct thread_info *, int_or_ptr64, int_or_ptr64)) $f)
    ($tinfo, $envi, $arg);
  return *((*$tinfo).args + 1LL);
}


