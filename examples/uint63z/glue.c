#include "values.h"
struct closure;
struct stack_frame;
struct thread_info;
struct closure {
  void (*func)(struct thread_info, value, value);
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

extern int printf(signed char *);
extern _Bool is_ptr(value);
unsigned int get_unboxed_ordinal(value);
unsigned int get_boxed_ordinal(value);
value *get_args(value);
value make_Coq_Numbers_BinNums_positive_xI(value, value *);
value alloc_make_Coq_Numbers_BinNums_positive_xI(struct thread_info *, value);
value make_Coq_Numbers_BinNums_positive_xO(value, value *);
value alloc_make_Coq_Numbers_BinNums_positive_xO(struct thread_info *, value);
value make_Coq_Numbers_BinNums_positive_xH(void);
value make_Coq_Numbers_BinNums_Z_Z0(void);
value make_Coq_Numbers_BinNums_Z_Zpos(value, value *);
value alloc_make_Coq_Numbers_BinNums_Z_Zpos(struct thread_info *, value);
value make_Coq_Numbers_BinNums_Z_Zneg(value, value *);
value alloc_make_Coq_Numbers_BinNums_Z_Zneg(struct thread_info *, value);
unsigned int get_Coq_Numbers_BinNums_positive_tag(value);
unsigned int get_Coq_Numbers_BinNums_Z_tag(value);
void print_Coq_Numbers_BinNums_positive(value);
void print_Coq_Numbers_BinNums_Z(value);
value call(struct thread_info *, value, value);
signed char const lparen_lit[2] = { 40, 0, };

signed char const rparen_lit[2] = { 41, 0, };

signed char const space_lit[2] = { 32, 0, };

signed char const fun_lit[6] = { 60, 102, 117, 110, 62, 0, };

signed char const type_lit[7] = { 60, 116, 121, 112, 101, 62, 0, };

signed char const unk_lit[6] = { 60, 117, 110, 107, 62, 0, };

signed char const prop_lit[7] = { 60, 112, 114, 111, 112, 62, 0, };

unsigned int get_unboxed_ordinal(value $v)
{
  return (unsigned long long) $v >> 1LL;
}

unsigned int get_boxed_ordinal(value $v)
{
  return *((unsigned long long *) $v + -1LL) & 255LL;
}

value *get_args(value $v)
{
  return (value *) $v;
}

signed char const names_of_Coq_Numbers_BinNums_positive[3][3] = { 120, 73, 0,
  120, 79, 0, 120, 72, 0, /* skip 0 */ };

signed char const names_of_Coq_Numbers_BinNums_Z[3][5] = { 90, 48, 0, 0, 0,
  90, 112, 111, 115, 0, 90, 110, 101, 103, 0, /* skip 0 */ };

value make_Coq_Numbers_BinNums_positive_xI(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1024LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_Coq_Numbers_BinNums_positive_xI(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1024LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

value make_Coq_Numbers_BinNums_positive_xO(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1025LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_Coq_Numbers_BinNums_positive_xO(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1025LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

value make_Coq_Numbers_BinNums_positive_xH(void)
{
  return 1;
}

value make_Coq_Numbers_BinNums_Z_Z0(void)
{
  return 1;
}

value make_Coq_Numbers_BinNums_Z_Zpos(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1024LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_Coq_Numbers_BinNums_Z_Zpos(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1024LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

value make_Coq_Numbers_BinNums_Z_Zneg(value $arg0, value *$argv)
{
  *($argv + 0LL) = (value) 1025LL;
  *($argv + 1LL) = $arg0;
  return $argv + 1LL;
}

value alloc_make_Coq_Numbers_BinNums_Z_Zneg(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *($argv + 0LL) = 1025LL;
  *($argv + 1LL) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LL;
  return $argv + 1LL;
}

unsigned int get_Coq_Numbers_BinNums_positive_tag(value $v)
{
  register _Bool $b;
  register unsigned int $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0U;
      case 1:
        return 1U;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 2U;
      
    }
  }
}

unsigned int get_Coq_Numbers_BinNums_Z_tag(value $v)
{
  register _Bool $b;
  register unsigned int $t;
  $b = is_ptr($v);
  if ($b) {
    $t = get_boxed_ordinal($v);
    switch ($t) {
      case 0:
        return 1U;
      case 1:
        return 2U;
      
    }
  } else {
    $t = get_unboxed_ordinal($v);
    switch ($t) {
      case 0:
        return 0U;
      
    }
  }
}

void print_Coq_Numbers_BinNums_positive(value $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Numbers_BinNums_positive_tag($v);
  switch ($tag) {
    case 0:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Numbers_BinNums_positive + $tag));
      printf(space_lit);
      print_Coq_Numbers_BinNums_positive(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    case 1:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Numbers_BinNums_positive + $tag));
      printf(space_lit);
      print_Coq_Numbers_BinNums_positive(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    case 2:
      printf(*(names_of_Coq_Numbers_BinNums_positive + $tag));
      break;
    
  }
}

void print_Coq_Numbers_BinNums_Z(value $v)
{
  register unsigned int $tag;
  register void *$args;
  $tag = get_Coq_Numbers_BinNums_Z_tag($v);
  switch ($tag) {
    case 0:
      printf(*(names_of_Coq_Numbers_BinNums_Z + $tag));
      break;
    case 1:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Numbers_BinNums_Z + $tag));
      printf(space_lit);
      print_Coq_Numbers_BinNums_positive(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    case 2:
      $args = get_args($v);
      printf(lparen_lit);
      printf(*(names_of_Coq_Numbers_BinNums_Z + $tag));
      printf(space_lit);
      print_Coq_Numbers_BinNums_positive(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    
  }
}

value call(struct thread_info *$tinfo, value $clo, value $arg)
{
  register unsigned long long *$f;
  register unsigned long long *$envi;
  $f = (*((struct closure *) $clo)).func;
  $envi = (*((struct closure *) $clo)).env;
  ((void (*)(struct thread_info *, value, value)) $f)($tinfo, $envi, $arg);
  return *((*$tinfo).args + 1LL);
}


