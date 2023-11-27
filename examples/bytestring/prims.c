#include <values.h>
#include "glue.h"
#include <stddef.h>
#include <stdio.h>
#include <string.h>

#define LIVEPOINTERS0(tinfo, exp) (exp)
#define LIVEPOINTERS1(tinfo, exp, a) ({ \
  value __ROOT__[1] = { a }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 1, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })
#define LIVEPOINTERS1_(tinfo, exp, a) ({ \
  value __ROOT__[1] = { a }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 1, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; exp; \
  a = __ROOT__[0]; \
  tinfo->fp = __FRAME__.prev; })
#define LIVEPOINTERS2(tinfo, exp, a, b) ({ \
  value __ROOT__[2] = { a, b }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 2, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })
#define LIVEPOINTERS2_(tinfo, exp, a, b) ({ \
  value __ROOT__[2] = { a, b }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 2, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; \
  tinfo->fp = __FRAME__.prev; })
#define LIVEPOINTERS3(tinfo, exp, a, b, c) ({ \
  value __ROOT__[3] = { a, b, c }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 3, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; c = __ROOT__[2]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })
#define LIVEPOINTERS4(tinfo, exp, a, b, c, d) ({ \
  value __ROOT__[4] = { a, b, c, d }; \
  struct stack_frame __FRAME__ = { __ROOT__ + 4, __ROOT__, tinfo->fp }; \
  tinfo->fp = &__FRAME__; value __TEMP__ = exp; \
  a = __ROOT__[0]; b = __ROOT__[1]; c = __ROOT__[2]; d = __ROOT__[3]; \
  tinfo->fp = __FRAME__.prev; __TEMP__; })

value bytestrlen(value s)
{
  value *ptr = (value *) s;
  value *headerptr = ptr - 1;
  value header = *headerptr;
  value words = header >> 10;
  value bytes = words * sizeof(value);
  value padding = (value) *((char *) s + (bytes - 1)) + 1;
  return bytes - padding;
}

/* value bytestrlen(value s) */
/* { */
/*   value words = (*((value *) s - 1) >> 10); */
/*   value bytes = words * sizeof(value); */
/*   value padding = (value) *((char *) s + (bytes - 1)) + 1; */
/*   return bytes - padding; */
/* } */

unsigned char ascii_to_char(value x) {
  unsigned char c = 0;
  for(unsigned int i = 0; i < 8; i++) {
    unsigned int tag = get_Coq_Init_Datatypes_bool_tag(*((value *) *((value *) x) + i));
    c += !tag << i;
  }
  return c;
}

/////////////////////////////////////////////////////////////////

value bool_to_value(_Bool b) {
  if(b)
    return make_Coq_Init_Datatypes_bool_true();
  else
    return make_Coq_Init_Datatypes_bool_false();
}

value char_to_value(struct thread_info *tinfo, char c) {
  value v[8];
  for(unsigned int i = 0; i < 8; i++) {
    v[i] = bool_to_value(c & (1 << i));
  }
  return alloc_make_Coq_Strings_Ascii_ascii_Ascii(tinfo, v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]);
}

value string_to_value(struct thread_info *tinfo, char *s) {
  value temp = make_Coq_Strings_String_string_EmptyString();
  for (unsigned int i = strlen(s); 0 < i; i--) {
    value c = char_to_value(tinfo, s[i-1]);
    temp = alloc_make_Coq_Strings_String_string_String(tinfo, c, temp);
  }
  return temp;
}

/////////////////////////////////////////////////////////////////

/*
value word8_to_ascii(struct thread_info *tinfo, value w)
{
  fprintf(stderr, "word8_to_ascii unimplemented");
  exit(EXIT_FAILURE);
}
value ascii_to_word8(struct thread_info *tinfo, value v)
{
  fprintf(stderr, "ascii_to_word8 unimplemented");
  exit(EXIT_FAILURE);
}

value to_upper(struct thread_info *tinfo, value v)
{
  char c = (char) (v >> 1); 
  char up = toupper(c);
  return (((value) up) << 1) + 1;
}

value map(struct thread_info *tinfo, value f, value s)
{
  value len = bytestrlen(s);

  value mod = len % sizeof(value);
  value pad_length = sizeof(value) - (len % sizeof(value));
  value needed = (len + pad_length) / sizeof(value) + 1;
  if (!(needed <= tinfo->limit - tinfo->alloc)) {
    fprintf(stderr, "not enough memory, call GC");
    exit(EXIT_FAILURE);
  }

  value *argv = (value *) tinfo->alloc;
  *((value *) argv + 0LLU) = ((needed - 1) << 10) + 252LLU; // string tag

  char *ptr = (char *) (argv + 1LLU);
  char *t = (char *) s;
  for (value i = 0; i < len; i++) {
    value c = (*t << 1) + 1;
    *ptr = call(tinfo, f, c) >> 1;; 
    ptr++; t++; 
  }

  // make the padding
  char i = 0;
  while (i < pad_length - 1) { *ptr = 0; ptr++; i++; }
  *ptr = i; // last char in the padding is # of 0s coming before the last char

  tinfo->alloc += needed;
  return (value) (argv + 1LLU);
}
*/

value append(struct thread_info *tinfo, value s1, value s2)
{
  value len1 = bytestrlen(s1);
  value len2 = bytestrlen(s2);
  value sum = len1 + len2;
  value mod = sum % sizeof(value);
  value pad_length = sizeof(value) - (sum % sizeof(value));
  value nalloc = (sum + pad_length) / sizeof(value) + 1;
  if (!(nalloc <= tinfo->limit - tinfo->alloc)) {
    tinfo->nalloc = nalloc;
    LIVEPOINTERS2_(tinfo, garbage_collect(tinfo), s1, s2);
  }

  value *argv = (value *) tinfo->alloc;
  *((value *) argv + 0LLU) = ((nalloc - 1) << 10) + 252LLU; // string tag
  
  // take a pointer pointing to the beginning of destination string
  char *ptr = (char *) (argv + 1LLU);
  char *t1 = (char *) s1;
  char *t2 = (char *) s2;

  // copy the OCaml-string pointed by t1 and t2
  // into the array pointed by ptr
  // skip the padding in each one, we'll make our own padding later
  for (value i = 0; i < len1; i++) { *ptr = *t1; ptr++; t1++; }
  for (value i = 0; i < len2; i++) { *ptr = *t2; ptr++; t2++; }

  // make the padding
  char i = 0;
  while (i < pad_length - 1) { *ptr = 0; ptr++; i++; }
  *ptr = i; // last char in the padding is # of 0s coming before the last char

  tinfo->alloc += nalloc;
  return (value) (argv + 1LLU);
}

value pack(struct thread_info *tinfo, value s)
{
  value temp = s;
  value len = 0;
  while(get_Coq_Strings_String_string_tag(temp) == 1) {
    len++;
    temp = *((value *) temp + 1ULL);
  } 
  value mod = len % sizeof(value);
  value pad_length = sizeof(value) - (len % sizeof(value));
  value nalloc = (len + pad_length) / sizeof(value) + 1;
  if (!(nalloc <= tinfo->limit - tinfo->alloc)) {
    tinfo->nalloc = nalloc;
    LIVEPOINTERS1_(tinfo, garbage_collect(tinfo), s);
  }

  value *argv = (value *) tinfo->alloc;
  *((value *) argv + 0LLU) = ((nalloc - 1) << 10) + 252LLU; // string tag

  char *ptr = (char *) (argv + 1LLU);
  temp = s;
  while(get_Coq_Strings_String_string_tag(temp) == 1) {
    *ptr = ascii_to_char(temp);
    ptr++;
    temp = *((value *) temp + 1ULL);
  } 

  // make the padding
  char i = 0;
  while (i < pad_length - 1) { *ptr = 0; ptr++; i++; }
  *ptr = i; // last char in the padding is # of 0s coming before the last char

  tinfo->alloc += nalloc;
  return (value) (argv + 1LLU);
}


value unpack(struct thread_info *tinfo, value bs)
{
  // 3 for the String constructor, 9 for the ASCII constructor.
  value nalloc = bytestrlen(bs) * (3 + 9);
  if (!(nalloc <= tinfo->limit - tinfo->alloc)) {
    tinfo->nalloc = nalloc;
    LIVEPOINTERS1_(tinfo, garbage_collect(tinfo), bs);
  }

  char *s = (char *) bs;
  value temp = make_Coq_Strings_String_string_EmptyString();
  for (unsigned int i = bytestrlen(bs); 0 < i; i--) {
    value c = char_to_value(tinfo, s[i-1]);
    temp = alloc_make_Coq_Strings_String_string_String(tinfo, c, temp);
  }
  return temp;
}

// from https://codereview.stackexchange.com/a/207541/68819
// allocates enough memory for a string (which has to be freed later)
// returns its length by assigning it to the pointer in the argument
char *scan(FILE *stream, size_t *length)
{
  size_t capacity = 16;
  char *buffer = malloc(capacity);
  if (!buffer) { return NULL; }
  size_t i = 0;

  int c; // current input character
  while ((c = fgetc(stream)) != EOF) {
    if (i + 2 > capacity) {
      // ensure space for c and terminating NUL
      capacity *= 2;
      char *newbuf = realloc(buffer, capacity);
      if (!newbuf) {
        // allocation failed - undo the read, terminate string, and return
        ungetc(c, stdin);
        buffer[i] = '\0';
        return buffer;
      }
      buffer = newbuf;
    }

    // We have enough space; now store it
    if (c == '\n') { break; }
    buffer[i++] = (char) c;
  }

  if (i == 0) { free(buffer); return NULL; } // we didn't read anything

  buffer[i] = '\0';
  *length = i;

  return buffer;
}

value scan_bytestring(struct thread_info *tinfo, value instream)
{
  size_t len;
  char *s = scan((FILE *) instream, &len);

  value mod = len % sizeof(value);
  value pad_length = sizeof(value) - (len % sizeof(value));
  value nalloc = (len + pad_length) / sizeof(value) + 1;
  if (!(nalloc <= tinfo->limit - tinfo->alloc)) {
    tinfo->nalloc = nalloc;
    LIVEPOINTERS1_(tinfo, garbage_collect(tinfo), instream);
  }

  value *argv = (value *) tinfo->alloc;
  *((value *) argv + 0LLU) = ((nalloc - 1) << 10) + 252LLU; // string tag

  char *ptr = (char *) (argv + 1LLU);
  char *t = (char *) s;
  while (*t != '\0') { *ptr = *t; ptr++; t++; }

  // make the padding
  char i = 0;
  while (i < pad_length - 1) { *ptr = 0; ptr++; i++; }
  *ptr = i; // last char in the padding is # of 0s coming before the last char

  tinfo->alloc += nalloc;
  return (value) (argv + 1LLU);
}

/////////////////////////////////////////////////////////////////

typedef enum { PURE, BIND, PRINT, SCAN } M;
value runM(struct thread_info * tinfo, value a, value instream, value outstream, value action)
{
  value temp, arg0, arg1;
  switch (get_prog_C_MI_tag(action)) {
    case PURE:
      return get_args(action)[1];
    case BIND:
      arg0 = get_args(action)[2];
      arg1 = get_args(action)[3];
      temp = LIVEPOINTERS4(tinfo, runM(tinfo, a, instream, outstream, arg0), arg0, arg1, instream, outstream);
      temp = LIVEPOINTERS4(tinfo, call(tinfo, arg1, temp), arg1, instream, outstream, temp);
      return runM(tinfo, a, instream, outstream, temp);
    case PRINT:
      {
        value s = *((value *) action);
        value len = bytestrlen(s);
        for (value i = 0; i < len; i ++) {
          fprintf((FILE *) outstream, "%c", ((char *) s)[i]);
        }
        fprintf((FILE *) outstream, "\n");
        return 0;
      }
    case SCAN:
      return scan_bytestring(tinfo, instream);
    default:
      return 0;
  }
}

value get_stdin(struct thread_info * tinfo, value _tt) {
  return stdin;
}

value get_stdout(struct thread_info * tinfo, value _tt) {
  return stdout;
}
