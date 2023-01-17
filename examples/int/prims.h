#include <stdio.h>
/* #include "values.h" */
#include "glue.prog.prog.h"
typedef unsigned long long value;

value uint63_from_Z(value z);

value uint63_to_Z(struct thread_info *tinfo, value t);

value uint63_add(value x, value y);

value uint63_mul(value x, value y);
