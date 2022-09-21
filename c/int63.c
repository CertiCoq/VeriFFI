/* Tim Carstens 2021 */

#ifndef CERTICOQ_INT63_C
#define CERTICOQ_INT63_C

#include "certicoq.h"
#include "int63.h"


/*
 * Encoding/decoding
value certicoq_encode_int63(int64_t x) {
    return (x << 1) | 1;
}

int64_t certicoq_decode_int63(value x) {
    return (int64_t)x >> 1;
}
*/

/*
 * Prims
value certicoq_prim__int63_zero() {
    return certicoq_encode_int63(0);
}

value certicoq_prim__int63_one() {
    return certicoq_encode_int63(1);
}

value certicoq_prim__int63_neg(value x) {
    return 2 - x;
}

value certicoq_prim__int63_abs(value x) {
    return x < 0 ? certicoq_prim__int63_neg(x) : x;
}
*/

value certicoq_prim__int63_from_Z(struct thread_info *tinfo, value x) {
  return 0;  
}

value certicoq_prim__int63_to_Z(struct thread_info *tinfo, value x) {
  size_t n = ((uintnat)x)>>1;
  return 0;  
}

value certicoq_prim__int63_add(struct thread_info *tinfo, value x, value y) {
  return (value)(((uintnat)x + (uintnat)y) - (uintnat)1);
}

value certicoq_prim__int63_sub(struct thread_info *tinfo, value x, value y) {
    return (x - y) + 1;
}

value certicoq_prim__int63_mul(struct thread_info *tinfo, value x, value y) {
  return (value)((((uintnat)x)>>1) * (((uintnat)y)-1) + 1);
}

value certicoq_prim__int63_div(struct thread_info *tinfo, value x, value y) {
  return (value)((((uintnat)x)-1) * (((uintnat)y)>>1)+(uintnat)1);
}

/*
value certicoq_prim__int63_rem(value x, value y) {
    const int64_t _x = certicoq_decode_int63(x);
    const int64_t _y = certicoq_decode_int63(y);
    const int64_t _z = _x % _y;
    return certicoq_encode_int63(_z);
}

value certicoq_prim__int63_shiftl(value x, value y) {
    const int64_t _x = certicoq_decode_int63(x);
    const int64_t _y = certicoq_decode_int63(y);
    const int64_t _z = _x << _y;
    return certicoq_encode_int63(_z);
}

value certicoq_prim__int63_shiftr(value x, value y) {
    const int64_t _x = certicoq_decode_int63(x);
    const int64_t _y = certicoq_decode_int63(y);
    const int64_t _z = _x >> _y;
    return certicoq_encode_int63(_z);
}
*/

value certicoq_prim__int63_or(struct thread_info *tinfo, value x, value y) {
    return x | y;
}

value certicoq_prim__int63_and(struct thread_info *tinfo, value x, value y) {
    return x & y;
}

value certicoq_prim__int63_xor(struct thread_info *tinfo, value x, value y) {
    return (value)1 | (x ^ y);
}

value certicoq_prim__int63_not(struct thread_info *tinfo, value x) {
    return (value)1 | ~ x;
}

value certicoq_prim__int63_is_eq(struct thread_info *tinfo, value x, value y) {
    return (x == y) ? make_Coq_Init_Datatypes_bool_true() : make_Coq_Init_Datatypes_bool_false();
}

value certicoq_prim__int63_is_lt(struct thread_info *tinfo, value x, value y) {
  return ((uintnat)x < (uintnat)y) ? make_Coq_Init_Datatypes_bool_true() : make_Coq_Init_Datatypes_bool_false();
}

/*
value certicoq_prim__int63_to_nat(struct thread_info *tinfo, value x_val) {
    int64_t x = certicoq_decode_int63(x_val);
    value ret = make_Coq_Init_Datatypes_nat_O();
    while (x > 0) {
        ret = alloc_make_Coq_Init_Datatypes_nat_S(tinfo, ret);
        x--;
    }
    return ret;
}
*/

#endif /* CERTICOQ_INT63_C */
