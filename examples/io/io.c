#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include "glue.h"

unsigned long long calls(struct thread_info* tinfo, unsigned long long clos, unsigned int n, ...)
{
  unsigned long long v = clos;
  va_list args;
  va_start(args, n);

  for(; n != 0; n--) {
    v = va_arg(args, unsigned long long);
    clos = call(tinfo, clos, v);
  }
  va_end(args);
  return clos;
}

///////////////////////////////////////////////////////////////////

unsigned char ascii_to_char(unsigned long long x) {
  unsigned char c = 0;
  for(unsigned int i = 0; i < 8; i++) {
    unsigned int tag = get_Coq_Init_Datatypes_bool_tag(*((unsigned long long *) *((unsigned long long *) x) + i));
    c += !tag << i;
  }
  return c;
}

unsigned long long print_gallina_string(struct thread_info *tinfo, unsigned long long s) {
  unsigned long long temp = s;

  while(1) {
    unsigned int tag = get_Coq_Strings_String_string_tag(temp);
    if(tag == 1) {
      printf("%c", ascii_to_char(temp));
      temp = *((unsigned long long *) temp + 1ULL);
    } else {
      break;
    }
  } 
  printf("\n");
  fflush(stdout);

  return make_Coq_Init_Datatypes_unit_tt();
}

/////////////////////////////////////////////////////////////////

unsigned long long bool_to_value(_Bool b) {
  if(b)
    return make_Coq_Init_Datatypes_bool_true();
  else
    return make_Coq_Init_Datatypes_bool_false();
}

unsigned long long char_to_value(struct thread_info *tinfo, char c) {
  unsigned long long v[8];
  for(unsigned int i = 0; i < 8; i++) {
    v[i] = bool_to_value(c & (1 << i));
  }
  return alloc_make_Coq_Strings_Ascii_ascii_Ascii(tinfo, v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]);
}

unsigned long long string_to_value(struct thread_info *tinfo, char *s) {
  unsigned long long temp = make_Coq_Strings_String_string_EmptyString();
  for (unsigned int i = strlen(s); 0 < i; i--) {
    unsigned long long c = char_to_value(tinfo, s[i-1]);
    temp = alloc_make_Coq_Strings_String_string_String(tinfo, c, temp);
  }
  return temp;
}

unsigned long long scan_gallina_string(struct thread_info *tinfo) { 
  char input[100];
  scanf("%s", input);

  unsigned long long s = string_to_value(tinfo, input);
  return s;
}

/////////////////////////////////////////////////////////////////

typedef enum { PRINT_STRING, SCAN_STRING } console;
unsigned long long run_console(struct thread_info * tinfo, unsigned long long action)
{
  switch (get_tests_console_tag(action)) {
    case PRINT_STRING:
      return print_gallina_string(tinfo, (char *) *((unsigned long long *) action));
    case SCAN_STRING:
      return scan_gallina_string(tinfo);
  }
}

typedef enum { RET, VIS, TAU } itree;
unsigned long long run_itree(struct thread_info * tinfo, unsigned long long tree)
{
  unsigned long long temp;
  switch (get_tests_itree_tag(tree)) {
    case RET:
      return *((unsigned long long *) tree);
    case VIS:
      temp = run_console(tinfo, *((unsigned long long *) tree + 1));
      return run_itree(tinfo, call(tinfo, *((unsigned long long *) tree + 2), temp));
    case TAU:
      return run_itree(tinfo, *((unsigned long long *) tree));
  }
}
