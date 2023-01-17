#include <stdio.h>
/* #include "values.h" */
#include "glue.prog.prog.h"
typedef unsigned long long value;

value uint63_from_Z(value z) {
  return z;
}

value uint63_to_Z(struct thread_info *tinfo, value t) {
  return make_Coq_Numbers_BinNums_Z_Z0();
}

value uint63_add(value x, value y) {
  return (((x >> 1) + (y >> 1)) << 1) + 1;
}

value uint63_mul(value x, value y) {
  return (((x >> 1) * (y >> 1)) << 1) + 1;
}
