#include "values.h"
value word8_to_ascii(struct thread_info *, value);
value ascii_to_word8(struct thread_info *, value);
value to_upper(struct thread_info *, value);
value append(struct thread_info *, value, value);
value pack(struct thread_info *, value);
/* value unpack(struct thread_info *, value); */
value map(struct thread_info *, value, value);
