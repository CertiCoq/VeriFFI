typedef void  * value
#ifdef COMPCERT
 __attribute((aligned(_Alignof(void *))))
#endif
 ;

struct thread_info;
struct Coq_Init_Datatypes_O_args;
struct Coq_Init_Datatypes_S_args;
struct thread_info {
  value *alloc;
  value *limit;
  struct heap *heap;
  value args[1024];
};

struct Coq_Init_Datatypes_O_args {
};

struct Coq_Init_Datatypes_S_args {
  value Coq_Init_Datatypes_S_arg_0;
};

extern int printf(signed char *);
extern _Bool is_ptr(value);
unsigned int get_unboxed_ordinal(value);
unsigned int get_boxed_ordinal(value);
value make_Coq_Init_Datatypes_nat_O(void);
value make_Coq_Init_Datatypes_nat_S(value, value *);
value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, value);
unsigned int get_Coq_Init_Datatypes_nat_tag(value);
struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(value);
struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(value);
void print_Coq_Init_Datatypes_nat(value);
void halt(struct thread_info *, value, value);
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
  return (unsigned long long)$v >> 1LLU;
}

unsigned int get_boxed_ordinal(value $v)
{
  return (unsigned long long)(*((value*) $v + 18446744073709551615LLU)) & 255LLU;
}

signed char const names_of_Coq_Init_Datatypes_nat[2][2] = { 79, 0, 83, 0,
  /* skip 0 */ };

value make_Coq_Init_Datatypes_nat_O(void)
{
  return 1;
}

value make_Coq_Init_Datatypes_nat_S(value $arg0, value *$argv)
{
  *((value *) $argv + 0LLU) = 1024LLU;
  *((value *) $argv + 1LLU) = $arg0;
  return $argv + 1LLU;
}

value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *$tinfo, value $arg0)
{
  register value *$argv;
  $argv = (*$tinfo).alloc;
  *((value *) $argv + 0LLU) = 1024LLU;
  *((value *) $argv + 1LLU) = $arg0;
  (*$tinfo).alloc = (*$tinfo).alloc + 2LLU;
  return $argv + 1LLU;
}

unsigned int get_Coq_Init_Datatypes_nat_tag(value $v)
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

struct Coq_Init_Datatypes_O_args *get_Coq_Init_Datatypes_O_args(value $v)
{
  return (struct Coq_Init_Datatypes_O_args *) 0;
}

struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(value $v)
{
  return (struct Coq_Init_Datatypes_S_args *) $v;
}

void print_Coq_Init_Datatypes_nat(value $v)
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
      print_Coq_Init_Datatypes_nat(*((value *) $args + 0));
      printf(rparen_lit);
      break;
    
  }
}

void halt(struct thread_info *$tinfo, value $env, value $arg)
{
  *((value *) (*$tinfo).args + 1LLU) = $arg;
  return;
}

value const halt_clo[2] = { &halt, 1LL, };

value call(struct thread_info *$tinfo, value $clo, value $arg)
{
  register value *$f;
  register value *$envi;
  $f = *((value *) $clo + 0LLU);
  $envi = *((value *) $clo + 1LLU);
  ((void (*)(struct thread_info *, value, value)) 
    $f)
    ($tinfo, $envi, $arg);
  return *((value *) (*$tinfo).args + 1LLU);
}


