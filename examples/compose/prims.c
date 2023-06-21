#include "values.h"
#include "glue.h"
#include <stdio.h>

value compose(struct thread_info *tinfo, value a, value b, value c, value g, value f, value x) {
  value temp = call(tinfo, f, x);
  return call(tinfo, g, temp);
}
