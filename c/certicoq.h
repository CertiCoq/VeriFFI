#ifndef CERTICOQ_H
#define CERTICOQ_H


/*
 * Abort routines
 */
void certicoq_prim__abort(const char *fn, const char *fmt, ...);
#define certicoq_abort_str(str) certicoq_prim__abort(__FUNCTION__, "%s", str)
#define certicoq_abort(fmt, ...) certicoq_prim__abort(__FUNCTION__, fmt, __VA_ARGS__)
#define certicoq_abort_if_null(p) if (!(p)) { certicoq_prim__abort(__FUNCTION__, "expected non-null pointer\n"); }
#define certicoq_abort_if_not_null(p) if (p) { certicoq_prim__abort(__FUNCTION__, "expected null pointer\n"); }


/*
 * GC
 */
#include "gc_stack.h"


/*
 * CertiCoq stuff
 */
extern value call(struct thread_info *, value, value);
value calls(struct thread_info* tinfo, value clos, unsigned int n, ...);

extern value make_Coq_Init_Datatypes_unit_tt(void);

extern value make_Coq_Init_Datatypes_option_None(void);
extern value alloc_make_Coq_Init_Datatypes_option_Some(struct thread_info *, value);

extern unsigned int get_Coq_Init_Datatypes_bool_tag(value);
extern value make_Coq_Init_Datatypes_bool_true(void);
extern value make_Coq_Init_Datatypes_bool_false(void);

extern unsigned int get_Coq_Init_Datatypes_list_tag(value);
extern value make_Coq_Init_Datatypes_list_nil(void);
extern value alloc_make_Coq_Init_Datatypes_list_cons(struct thread_info *, value, value);

extern value make_Coq_Init_Datatypes_nat_O(void);
extern value alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *, value);

extern value alloc_make_Coq_Strings_Ascii_ascii_Ascii(struct thread_info *, value, value, value, value, value, value, value, value);

extern unsigned int get_Coq_Strings_String_string_tag(value);
extern value make_Coq_Strings_String_string_EmptyString(void);
extern value alloc_make_Coq_Strings_String_string_String(struct thread_info *, value, value);
struct Coq_Strings_String_String_args {
    value Coq_Strings_String_String_arg_0;
    value Coq_Strings_String_String_arg_1;
};
extern struct Coq_Strings_String_String_args *get_Coq_Strings_String_String_args(value v);


/*
 * Primops
 */
/* #include "array.h" */
#include "blob.h"
/* #include "bytestring.h" */
/* #include "uint8.h" */
/* #include "int63.h" */
/* #include "mut.h" */


/*
 * Effects
 */
enum certicoq_prim__effect_tag {
    certicoq_prim__E_bytestring = 0,
    certicoq_prim__E_mut,
    certicoq_prim__E_array,
};

extern enum certicoq_prim__effect_tag get_CertiCoqExt_Lib_CertiCoqRT_E_tag(value);

value certicoq_prim__exec_effect(struct thread_info *tinfo, value effect_val);


/*
 * ITrees
 */
enum certicoq_prim__itree_tag {
    certicoq_prim__IT_ret = 0,
    certicoq_prim__IT_vis,
    certicoq_prim__IT_tau
};

extern enum certicoq_prim__itree_tag get_CertiCoqExt_Lib_CertiCoqRT_ITree_tag(value);

value certicoq_prim__exec_itree(value (*exec_effect)(struct thread_info *, value), struct thread_info *tinfo, value itree_val);

#endif /* CERTICOQ_H */
