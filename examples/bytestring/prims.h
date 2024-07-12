value append(struct thread_info *tinfo, value, value);
value pack(struct thread_info *tinfo, value);
value unpack(struct thread_info *tinfo, value);
value runM(struct thread_info *tinfo, value, value, value, value);
value get_stdin(struct thread_info *tinfo, value);
value get_stdout(struct thread_info *tinfo, value);
