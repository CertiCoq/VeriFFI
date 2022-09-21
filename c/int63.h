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
value certicoq_prim__int63_zero(struct thread_info *tinfo);
value certicoq_prim__int63_one(struct thread_info *tinfo);
value certicoq_prim__int63_neg(struct thread_info *tinfo, value x);
value certicoq_prim__int63_abs(struct thread_info *tinfo, value x);
value certicoq_prim__int63_add(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_sub(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_mul(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_div(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_rem(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_shiftl(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_shiftr(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_or(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_and(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_xor(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_not(struct thread_info *tinfo, value x);
value certicoq_prim__int63_is_eq(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_is_lt(struct thread_info *tinfo, value x, value y);
value certicoq_prim__int63_to_nat(struct thread_info *tinfo, value x_val);

#endif /* CERTICOQ_INT63_H */
