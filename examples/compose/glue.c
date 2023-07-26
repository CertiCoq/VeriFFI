typedef void * __attribute((aligned(4))) int_or_ptr32;
typedef void * __attribute((aligned(8))) int_or_ptr64;
struct closure;
struct stack_frame;
struct thread_info;
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

extern int printf(signed char *);
extern _Bool is_ptr(int_or_ptr64);
unsigned int get_unboxed_ordinal(int_or_ptr64);
unsigned int get_boxed_ordinal(int_or_ptr64);
int_or_ptr64 *get_args(int_or_ptr64);
int_or_ptr64 make_Coq_Init_Datatypes_nat_O(void);
int_or_ptr64 make_Coq_Init_Datatypes_nat_S(int_or_ptr64, int_or_ptr64 *);
int_or_ptr64 alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, int_or_ptr64);
unsigned int get_Coq_Init_Datatypes_nat_tag(int_or_ptr64);
void print_Coq_Init_Datatypes_nat(int_or_ptr64);
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

int_or_ptr64 *get_args(int_or_ptr64 $v)
{
  return (int_or_ptr64 *) $v;
}

signed char const names_of_Coq_Init_Datatypes_nat[2][2] = { 79, 0, 83, 0,
  /* skip 0 */ };

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
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Init_Datatypes_nat + $tag));
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


