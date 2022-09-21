/* Tim Carstens 2021 */

#ifndef CERTICOQ_INT63_H
#define CERTICOQ_INT63_H

/*
 * Encoding/decoding
 */
#include <stdint.h>

value certicoq_encode_int63(int64_t x);
int64_t certicoq_decode_int63(value x);


/*
 * Prims
 */
value certicoq_prim__int63_zero();
value certicoq_prim__int63_one();
value certicoq_prim__int63_neg(value x);
value certicoq_prim__int63_abs(value x);
value certicoq_prim__int63_add(value x, value y);
value certicoq_prim__int63_sub(value x, value y);
value certicoq_prim__int63_mul(value x, value y);
value certicoq_prim__int63_div(value x, value y);
value certicoq_prim__int63_rem(value x, value y);
value certicoq_prim__int63_shiftl(value x, value y);
value certicoq_prim__int63_shiftr(value x, value y);
value certicoq_prim__int63_or(value x, value y);
value certicoq_prim__int63_and(value x, value y);
value certicoq_prim__int63_xor(value x, value y);
value certicoq_prim__int63_not(value x);
value certicoq_prim__int63_is_eq(value x, value y);
value certicoq_prim__int63_is_lt(value x, value y);
value certicoq_prim__int63_to_nat(struct thread_info *tinfo, value x_val);

#endif /* CERTICOQ_INT63_H */
