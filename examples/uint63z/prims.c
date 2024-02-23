#include <values.h>
#include "glue.h"

typedef enum { XI, XO, XH } tag_positive;
// not very space efficient but it should be easy to prove
value uint63_from_positive(value p) {
  switch (get_Coq_Numbers_BinNums_positive_tag(p)) {
    case XI:
      return ((2 * ((size_t)(uint63_from_positive(get_args(p)[0])) >> 1) + 1) << 1) + 1;
    case XO:
      return ((2 * ((size_t)(uint63_from_positive(get_args(p)[0])) >> 1)) << 1) + 1;
    case XH:
      return (1 << 1) + 1;
  }
}

typedef enum { Z0, ZPOS, ZNEG } tag_Z;
value uint63_from_Z(value z) {
  switch (get_Coq_Numbers_BinNums_Z_tag(z)) {
    case Z0:
      return 0;
    case ZPOS:
      return uint63_from_positive(get_args(z)[0]);
    case ZNEG:
      return (value)(-(size_t)(uint63_from_positive(get_args(z)[0])));
  }
}

value uint63_to_Z(struct thread_info *tinfo, value t) {
  if (t == 1) {
    return make_Coq_Numbers_BinNums_Z_Z0();
  }
  value temp = 0;
  // loop over bits from left (most significant) to right (least significant)
  // ignore the last bit, hence i > 0, not i >= 0
  for (unsigned int i = sizeof(value) * 8 - 1; i > 0; i--) {
    _Bool bit = ((size_t)t & (1ULL << i)) >> i;
    if (bit) {
      if (temp) {
        temp = alloc_make_Coq_Numbers_BinNums_positive_xI(tinfo, temp);
      } else {
        temp = make_Coq_Numbers_BinNums_positive_xH();
      }
    } else if (temp) {
      temp = alloc_make_Coq_Numbers_BinNums_positive_xO(tinfo, temp);
    }
    // ignore the 0 bits before the first significant 1
  }
  return alloc_make_Coq_Numbers_BinNums_Z_Zpos(tinfo, temp);
}

value uint63_add(value x, value y) {
  return (value)(((((size_t)x >> 1) + ((size_t)y >> 1)) << 1) + 1);
}

value uint63_mul(value x, value y) {
  return (value)(((((size_t)x >> 1) * ((size_t)y >> 1)) << 1) + 1);
}
