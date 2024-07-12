From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.13".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "examples/bytestring/prims.c".
  Definition normalized := true.
End Info.

Definition __ALLOC : ident := $"_ALLOC".
Definition __LIMIT : ident := $"_LIMIT".
Definition ___FRAME__ : ident := $"__FRAME__".
Definition ___PREV__ : ident := $"__PREV__".
Definition ___ROOT__ : ident := $"__ROOT__".
Definition ___RTEMP__ : ident := $"__RTEMP__".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fence : ident := $"__builtin_fence".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___sFILE : ident := $"__sFILE".
Definition ___sFILEX : ident := $"__sFILEX".
Definition ___sbuf : ident := $"__sbuf".
Definition ___stdinp : ident := $"__stdinp".
Definition ___stdoutp : ident := $"__stdoutp".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition __base : ident := $"_base".
Definition __bf : ident := $"_bf".
Definition __blksize : ident := $"_blksize".
Definition __close : ident := $"_close".
Definition __cookie : ident := $"_cookie".
Definition __extra : ident := $"_extra".
Definition __file : ident := $"_file".
Definition __flags : ident := $"_flags".
Definition __lb : ident := $"_lb".
Definition __lbfsize : ident := $"_lbfsize".
Definition __nbuf : ident := $"_nbuf".
Definition __offset : ident := $"_offset".
Definition __p : ident := $"_p".
Definition __r : ident := $"_r".
Definition __read : ident := $"_read".
Definition __seek : ident := $"_seek".
Definition __size : ident := $"_size".
Definition __tt : ident := $"_tt".
Definition __ub : ident := $"_ub".
Definition __ubuf : ident := $"_ubuf".
Definition __ur : ident := $"_ur".
Definition __w : ident := $"_w".
Definition __write : ident := $"_write".
Definition _a : ident := $"a".
Definition _action : ident := $"action".
Definition _alloc : ident := $"alloc".
Definition _alloc_make_Coq_Strings_Ascii_ascii_Ascii : ident := $"alloc_make_Coq_Strings_Ascii_ascii_Ascii".
Definition _alloc_make_Coq_Strings_String_string_String : ident := $"alloc_make_Coq_Strings_String_string_String".
Definition _append : ident := $"append".
Definition _arg0 : ident := $"arg0".
Definition _arg1 : ident := $"arg1".
Definition _args : ident := $"args".
Definition _argv : ident := $"argv".
Definition _ascii_to_char : ident := $"ascii_to_char".
Definition _b : ident := $"b".
Definition _bool_to_value : ident := $"bool_to_value".
Definition _buffer : ident := $"buffer".
Definition _bump_allocptr : ident := $"bump_allocptr".
Definition _bytes : ident := $"bytes".
Definition _bytestrlen : ident := $"bytestrlen".
Definition _c : ident := $"c".
Definition _call : ident := $"call".
Definition _capacity : ident := $"capacity".
Definition _char_to_value : ident := $"char_to_value".
Definition _fgetc : ident := $"fgetc".
Definition _fp : ident := $"fp".
Definition _fprintf : ident := $"fprintf".
Definition _free : ident := $"free".
Definition _garbage_collect : ident := $"garbage_collect".
Definition _get_Coq_Init_Datatypes_bool_tag : ident := $"get_Coq_Init_Datatypes_bool_tag".
Definition _get_Coq_Strings_String_string_tag : ident := $"get_Coq_Strings_String_string_tag".
Definition _get_args : ident := $"get_args".
Definition _get_prog_C_MI_tag : ident := $"get_prog_C_MI_tag".
Definition _get_stdin : ident := $"get_stdin".
Definition _get_stdout : ident := $"get_stdout".
Definition _header : ident := $"header".
Definition _heap : ident := $"heap".
Definition _i : ident := $"i".
Definition _instream : ident := $"instream".
Definition _len : ident := $"len".
Definition _len1 : ident := $"len1".
Definition _len2 : ident := $"len2".
Definition _length : ident := $"length".
Definition _limit : ident := $"limit".
Definition _main : ident := $"main".
Definition _make_Coq_Init_Datatypes_bool_false : ident := $"make_Coq_Init_Datatypes_bool_false".
Definition _make_Coq_Init_Datatypes_bool_true : ident := $"make_Coq_Init_Datatypes_bool_true".
Definition _make_Coq_Strings_String_string_EmptyString : ident := $"make_Coq_Strings_String_string_EmptyString".
Definition _malloc : ident := $"malloc".
Definition _mod : ident := $"mod".
Definition _n : ident := $"n".
Definition _nalloc : ident := $"nalloc".
Definition _new : ident := $"new".
Definition _newbuf : ident := $"newbuf".
Definition _next : ident := $"next".
Definition _odata : ident := $"odata".
Definition _outstream : ident := $"outstream".
Definition _pack : ident := $"pack".
Definition _pad_length : ident := $"pad_length".
Definition _padding : ident := $"padding".
Definition _prev : ident := $"prev".
Definition _ptr : ident := $"ptr".
Definition _realloc : ident := $"realloc".
Definition _rem_limit : ident := $"rem_limit".
Definition _root : ident := $"root".
Definition _runM : ident := $"runM".
Definition _s : ident := $"s".
Definition _save0 : ident := $"save0".
Definition _save1 : ident := $"save1".
Definition _scan : ident := $"scan".
Definition _scan_bytestring : ident := $"scan_bytestring".
Definition _space : ident := $"space".
Definition _spaces : ident := $"spaces".
Definition _stack_frame : ident := $"stack_frame".
Definition _start : ident := $"start".
Definition _stream : ident := $"stream".
Definition _string_to_value : ident := $"string_to_value".
Definition _strlen : ident := $"strlen".
Definition _sum : ident := $"sum".
Definition _t : ident := $"t".
Definition _t1 : ident := $"t1".
Definition _t2 : ident := $"t2".
Definition _tag : ident := $"tag".
Definition _temp : ident := $"temp".
Definition _thread_info : ident := $"thread_info".
Definition _tinfo : ident := $"tinfo".
Definition _ungetc : ident := $"ungetc".
Definition _unpack : ident := $"unpack".
Definition _v : ident := $"v".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 3);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stdinp := {|
  gvar_info := (tptr (Tstruct ___sFILE noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v___stdoutp := {|
  gvar_info := (tptr (Tstruct ___sFILE noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_bytestrlen := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_s, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_header, tulong) :: (_bytes, tulong) :: (_padding, tulong) ::
               (_t'2, (talignas 3%N (tptr tvoid))) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd
          (Ecast (Etempvar _s (talignas 3%N (tptr tvoid)))
            (tptr (talignas 3%N (tptr tvoid))))
          (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
          (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid))))
    (Sset _header (Ecast (Etempvar _t'2 (talignas 3%N (tptr tvoid))) tulong)))
  (Ssequence
    (Sset _bytes
      (Ebinop Omul
        (Ebinop Oshr (Etempvar _header tulong)
          (Econst_int (Int.repr 10) tint) tulong)
        (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd
              (Ecast (Etempvar _s (talignas 3%N (tptr tvoid))) (tptr tuchar))
              (Ebinop Osub (Etempvar _bytes tulong)
                (Econst_int (Int.repr 1) tint) tulong) (tptr tuchar)) tuchar))
        (Sset _padding
          (Ecast
            (Ebinop Oadd (Etempvar _t'1 tuchar)
              (Econst_int (Int.repr 1) tint) tint) tulong)))
      (Sreturn (Some (Ebinop Osub (Etempvar _bytes tulong)
                       (Etempvar _padding tulong) tulong))))))
|}.

Definition f_ascii_to_char := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, tuchar) :: (_i, tuint) :: (_tag, tuint) ::
               (_t'2, tulong) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sset _c (Ecast (Econst_int (Int.repr 0) tint) tuchar))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Econst_int (Int.repr 8) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _get_args (Tfunction
                                    (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                    (tptr (talignas 3%N (tptr tvoid)))
                                    cc_default))
                  ((Etempvar _x (talignas 3%N (tptr tvoid))) :: nil))
                (Ssequence
                  (Sset _t'3
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))
                        (Etempvar _i tuint)
                        (tptr (talignas 3%N (tptr tvoid))))
                      (talignas 3%N (tptr tvoid))))
                  (Scall (Some _t'2)
                    (Evar _get_Coq_Init_Datatypes_bool_tag (Tfunction
                                                             (Tcons
                                                               (talignas 3%N (tptr tvoid))
                                                               Tnil) tulong
                                                             cc_default))
                    ((Etempvar _t'3 (talignas 3%N (tptr tvoid))) :: nil))))
              (Sset _tag (Ecast (Etempvar _t'2 tulong) tuint)))
            (Sset _c
              (Ecast
                (Ebinop Oadd (Etempvar _c tuchar)
                  (Ebinop Oshl (Eunop Onotbool (Etempvar _tag tuint) tint)
                    (Etempvar _i tuint) tint) tint) tuchar))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn (Some (Etempvar _c tuchar)))))
|}.

Definition f_bool_to_value := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_b, tbool) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (talignas 3%N (tptr tvoid))) ::
               (_t'1, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Sifthenelse (Etempvar _b tbool)
  (Ssequence
    (Scall (Some _t'1)
      (Evar _make_Coq_Init_Datatypes_bool_true (Tfunction Tnil
                                                 (talignas 3%N (tptr tvoid))
                                                 cc_default)) nil)
    (Sreturn (Some (Etempvar _t'1 (talignas 3%N (tptr tvoid))))))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _make_Coq_Init_Datatypes_bool_false (Tfunction Tnil
                                                  (talignas 3%N (tptr tvoid))
                                                  cc_default)) nil)
    (Sreturn (Some (Etempvar _t'2 (talignas 3%N (tptr tvoid)))))))
|}.

Definition f_char_to_value := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_c, tuchar) :: nil);
  fn_vars := ((_v, (tarray (talignas 3%N (tptr tvoid)) 8)) :: nil);
  fn_temps := ((_i, tuint) :: (_t'2, (talignas 3%N (tptr tvoid))) ::
               (_t'1, (talignas 3%N (tptr tvoid))) ::
               (_t'10, (talignas 3%N (tptr tvoid))) ::
               (_t'9, (talignas 3%N (tptr tvoid))) ::
               (_t'8, (talignas 3%N (tptr tvoid))) ::
               (_t'7, (talignas 3%N (tptr tvoid))) ::
               (_t'6, (talignas 3%N (tptr tvoid))) ::
               (_t'5, (talignas 3%N (tptr tvoid))) ::
               (_t'4, (talignas 3%N (tptr tvoid))) ::
               (_t'3, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 8) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Scall (Some _t'1)
            (Evar _bool_to_value (Tfunction (Tcons tbool Tnil)
                                   (talignas 3%N (tptr tvoid)) cc_default))
            ((Ebinop Oand (Etempvar _c tuchar)
               (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                 (Etempvar _i tuint) tint) tint) :: nil))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _v (tarray (talignas 3%N (tptr tvoid)) 8))
                (Etempvar _i tuint) (tptr (talignas 3%N (tptr tvoid))))
              (talignas 3%N (tptr tvoid)))
            (Etempvar _t'1 (talignas 3%N (tptr tvoid))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Ederef
          (Ebinop Oadd (Evar _v (tarray (talignas 3%N (tptr tvoid)) 8))
            (Econst_int (Int.repr 0) tint)
            (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid))))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Evar _v (tarray (talignas 3%N (tptr tvoid)) 8))
              (Econst_int (Int.repr 1) tint)
              (tptr (talignas 3%N (tptr tvoid))))
            (talignas 3%N (tptr tvoid))))
        (Ssequence
          (Sset _t'5
            (Ederef
              (Ebinop Oadd (Evar _v (tarray (talignas 3%N (tptr tvoid)) 8))
                (Econst_int (Int.repr 2) tint)
                (tptr (talignas 3%N (tptr tvoid))))
              (talignas 3%N (tptr tvoid))))
          (Ssequence
            (Sset _t'6
              (Ederef
                (Ebinop Oadd (Evar _v (tarray (talignas 3%N (tptr tvoid)) 8))
                  (Econst_int (Int.repr 3) tint)
                  (tptr (talignas 3%N (tptr tvoid))))
                (talignas 3%N (tptr tvoid))))
            (Ssequence
              (Sset _t'7
                (Ederef
                  (Ebinop Oadd
                    (Evar _v (tarray (talignas 3%N (tptr tvoid)) 8))
                    (Econst_int (Int.repr 4) tint)
                    (tptr (talignas 3%N (tptr tvoid))))
                  (talignas 3%N (tptr tvoid))))
              (Ssequence
                (Sset _t'8
                  (Ederef
                    (Ebinop Oadd
                      (Evar _v (tarray (talignas 3%N (tptr tvoid)) 8))
                      (Econst_int (Int.repr 5) tint)
                      (tptr (talignas 3%N (tptr tvoid))))
                    (talignas 3%N (tptr tvoid))))
                (Ssequence
                  (Sset _t'9
                    (Ederef
                      (Ebinop Oadd
                        (Evar _v (tarray (talignas 3%N (tptr tvoid)) 8))
                        (Econst_int (Int.repr 6) tint)
                        (tptr (talignas 3%N (tptr tvoid))))
                      (talignas 3%N (tptr tvoid))))
                  (Ssequence
                    (Sset _t'10
                      (Ederef
                        (Ebinop Oadd
                          (Evar _v (tarray (talignas 3%N (tptr tvoid)) 8))
                          (Econst_int (Int.repr 7) tint)
                          (tptr (talignas 3%N (tptr tvoid))))
                        (talignas 3%N (tptr tvoid))))
                    (Scall (Some _t'2)
                      (Evar _alloc_make_Coq_Strings_Ascii_ascii_Ascii 
                      (Tfunction
                        (Tcons (tptr (Tstruct _thread_info noattr))
                          (Tcons (talignas 3%N (tptr tvoid))
                            (Tcons (talignas 3%N (tptr tvoid))
                              (Tcons (talignas 3%N (tptr tvoid))
                                (Tcons (talignas 3%N (tptr tvoid))
                                  (Tcons (talignas 3%N (tptr tvoid))
                                    (Tcons (talignas 3%N (tptr tvoid))
                                      (Tcons (talignas 3%N (tptr tvoid))
                                        (Tcons (talignas 3%N (tptr tvoid))
                                          Tnil)))))))))
                        (talignas 3%N (tptr tvoid)) cc_default))
                      ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                       (Etempvar _t'3 (talignas 3%N (tptr tvoid))) ::
                       (Etempvar _t'4 (talignas 3%N (tptr tvoid))) ::
                       (Etempvar _t'5 (talignas 3%N (tptr tvoid))) ::
                       (Etempvar _t'6 (talignas 3%N (tptr tvoid))) ::
                       (Etempvar _t'7 (talignas 3%N (tptr tvoid))) ::
                       (Etempvar _t'8 (talignas 3%N (tptr tvoid))) ::
                       (Etempvar _t'9 (talignas 3%N (tptr tvoid))) ::
                       (Etempvar _t'10 (talignas 3%N (tptr tvoid))) :: nil))))))))))
    (Sreturn (Some (Etempvar _t'2 (talignas 3%N (tptr tvoid)))))))
|}.

Definition f_string_to_value := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_s, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_temp, (talignas 3%N (tptr tvoid))) :: (_i, tuint) ::
               (_c, (talignas 3%N (tptr tvoid))) ::
               (_t'4, (talignas 3%N (tptr tvoid))) ::
               (_t'3, (talignas 3%N (tptr tvoid))) :: (_t'2, tulong) ::
               (_t'1, (talignas 3%N (tptr tvoid))) :: (_t'5, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _make_Coq_Strings_String_string_EmptyString (Tfunction Tnil
                                                          (talignas 3%N (tptr tvoid))
                                                          cc_default)) nil)
    (Sset _temp (Etempvar _t'1 (talignas 3%N (tptr tvoid)))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tulong
                          cc_default)) ((Etempvar _s (tptr tuchar)) :: nil))
        (Sset _i (Ecast (Etempvar _t'2 tulong) tuint)))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 0) tint)
                         (Etempvar _i tuint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'5
                  (Ederef
                    (Ebinop Oadd (Etempvar _s (tptr tuchar))
                      (Ebinop Osub (Etempvar _i tuint)
                        (Econst_int (Int.repr 1) tint) tuint) (tptr tuchar))
                    tuchar))
                (Scall (Some _t'3)
                  (Evar _char_to_value (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _thread_info noattr))
                                           (Tcons tuchar Tnil))
                                         (talignas 3%N (tptr tvoid))
                                         cc_default))
                  ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                   (Etempvar _t'5 tuchar) :: nil)))
              (Sset _c (Etempvar _t'3 (talignas 3%N (tptr tvoid)))))
            (Ssequence
              (Scall (Some _t'4)
                (Evar _alloc_make_Coq_Strings_String_string_String (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _thread_info noattr))
                                                                    (Tcons
                                                                    (talignas 3%N (tptr tvoid))
                                                                    (Tcons
                                                                    (talignas 3%N (tptr tvoid))
                                                                    Tnil)))
                                                                    (talignas 3%N (tptr tvoid))
                                                                    cc_default))
                ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                 (Etempvar _c (talignas 3%N (tptr tvoid))) ::
                 (Etempvar _temp (talignas 3%N (tptr tvoid))) :: nil))
              (Sset _temp (Etempvar _t'4 (talignas 3%N (tptr tvoid)))))))
        (Sset _i
          (Ebinop Osub (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn (Some (Etempvar _temp (talignas 3%N (tptr tvoid)))))))
|}.

Definition f_append := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_save0, (talignas 3%N (tptr tvoid))) ::
                (_save1, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := ((___ROOT__, (tarray (talignas 3%N (tptr tvoid)) 2)) ::
              (___FRAME__, (Tstruct _stack_frame noattr)) :: nil);
  fn_temps := ((_i, tulong) :: (_len1, tulong) :: (_len2, tulong) ::
               (_sum, tulong) :: (_mod, tulong) :: (_pad_length, tulong) ::
               (__ALLOC, (tptr (talignas 3%N (tptr tvoid)))) ::
               (__LIMIT, (tptr (talignas 3%N (tptr tvoid)))) ::
               (___PREV__, (tptr (Tstruct _stack_frame noattr))) ::
               (_nalloc, tulong) ::
               (___RTEMP__, (talignas 3%N (tptr tvoid))) ::
               (_argv, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_ptr, (tptr tuchar)) :: (_t1, (tptr tuchar)) ::
               (_t2, (tptr tuchar)) :: (_t'2, tulong) :: (_t'1, tulong) ::
               (_t'6, (tptr (Tstruct _stack_frame noattr))) ::
               (_t'5, tuchar) :: (_t'4, tuchar) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _bytestrlen (Tfunction (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                          tulong cc_default))
      ((Etempvar _save0 (talignas 3%N (tptr tvoid))) :: nil))
    (Sset _len1 (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _bytestrlen (Tfunction (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                            tulong cc_default))
        ((Etempvar _save1 (talignas 3%N (tptr tvoid))) :: nil))
      (Sset _len2 (Etempvar _t'2 tulong)))
    (Ssequence
      (Sset _sum
        (Ebinop Oadd (Etempvar _len1 tulong) (Etempvar _len2 tulong) tulong))
      (Ssequence
        (Sset _mod
          (Ebinop Omod (Etempvar _sum tulong)
            (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong))
        (Ssequence
          (Sset _pad_length
            (Ebinop Osub (Esizeof (talignas 3%N (tptr tvoid)) tulong)
              (Ebinop Omod (Etempvar _sum tulong)
                (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong) tulong))
          (Ssequence
            (Sassign
              (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _next
                (tptr (talignas 3%N (tptr tvoid))))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
            (Ssequence
              (Sassign
                (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _root
                  (tptr (talignas 3%N (tptr tvoid))))
                (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2)))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                        (Tstruct _thread_info noattr)) _fp
                      (tptr (Tstruct _stack_frame noattr))))
                  (Sassign
                    (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                      _prev (tptr (Tstruct _stack_frame noattr)))
                    (Etempvar _t'6 (tptr (Tstruct _stack_frame noattr)))))
                (Ssequence
                  (Sset _nalloc
                    (Ebinop Oadd
                      (Ebinop Odiv
                        (Ebinop Oadd (Etempvar _sum tulong)
                          (Etempvar _pad_length tulong) tulong)
                        (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong)
                      (Econst_int (Int.repr 1) tint) tulong))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset __LIMIT
                          (Efield
                            (Ederef
                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                              (Tstruct _thread_info noattr)) _limit
                            (tptr (talignas 3%N (tptr tvoid)))))
                        (Sset __ALLOC
                          (Efield
                            (Ederef
                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                              (Tstruct _thread_info noattr)) _alloc
                            (tptr (talignas 3%N (tptr tvoid))))))
                      (Sifthenelse (Eunop Onotbool
                                     (Ebinop Ole (Etempvar _nalloc tulong)
                                       (Ebinop Osub
                                         (Etempvar __LIMIT (tptr (talignas 3%N (tptr tvoid))))
                                         (Etempvar __ALLOC (tptr (talignas 3%N (tptr tvoid))))
                                         tlong) tint) tint)
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                (Tstruct _thread_info noattr)) _nalloc
                              tulong) (Etempvar _nalloc tulong))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                                  (Tstruct _thread_info noattr))
                                                _fp
                                                (tptr (Tstruct _stack_frame noattr)))
                                              (Eaddrof
                                                (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                                (tptr (Tstruct _stack_frame noattr))))
                                            (Sassign
                                              (Efield
                                                (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                                _next
                                                (tptr (talignas 3%N (tptr tvoid))))
                                              (Ebinop Oadd
                                                (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2))
                                                (Econst_int (Int.repr 2) tint)
                                                (tptr (talignas 3%N (tptr tvoid))))))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr (talignas 3%N (tptr tvoid))))
                                              (talignas 3%N (tptr tvoid)))
                                            (Etempvar _save0 (talignas 3%N (tptr tvoid)))))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr (talignas 3%N (tptr tvoid))))
                                            (talignas 3%N (tptr tvoid)))
                                          (Etempvar _save1 (talignas 3%N (tptr tvoid)))))
                                      (Scall None
                                        (Evar _garbage_collect (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _thread_info noattr))
                                                                   Tnil)
                                                                 tvoid
                                                                 cc_default))
                                        ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                                         nil)))
                                    (Sset ___RTEMP__
                                      (Ecast
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          (tptr tvoid))
                                        (talignas 3%N (tptr tvoid)))))
                                  (Sset _save0
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2))
                                        (Econst_int (Int.repr 0) tint)
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (talignas 3%N (tptr tvoid)))))
                                (Sset _save1
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr (talignas 3%N (tptr tvoid))))
                                    (talignas 3%N (tptr tvoid)))))
                              (Sset ___PREV__
                                (Efield
                                  (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                  _prev (tptr (Tstruct _stack_frame noattr)))))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                  (Tstruct _thread_info noattr)) _fp
                                (tptr (Tstruct _stack_frame noattr)))
                              (Etempvar ___PREV__ (tptr (Tstruct _stack_frame noattr))))))
                        Sskip))
                    (Ssequence
                      (Sset _argv
                        (Efield
                          (Ederef
                            (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                            (Tstruct _thread_info noattr)) _alloc
                          (tptr (talignas 3%N (tptr tvoid)))))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _argv (tptr (talignas 3%N (tptr tvoid))))
                              (Econst_long (Int64.repr 0) tulong)
                              (tptr (talignas 3%N (tptr tvoid))))
                            (talignas 3%N (tptr tvoid)))
                          (Ecast
                            (Ebinop Oadd
                              (Ebinop Oshl
                                (Ebinop Osub (Etempvar _nalloc tulong)
                                  (Econst_int (Int.repr 1) tint) tulong)
                                (Econst_int (Int.repr 10) tint) tulong)
                              (Econst_long (Int64.repr 252) tulong) tulong)
                            (tptr (talignas 3%N (tptr tvoid)))))
                        (Ssequence
                          (Sset _ptr
                            (Ecast
                              (Ebinop Oadd
                                (Etempvar _argv (tptr (talignas 3%N (tptr tvoid))))
                                (Econst_long (Int64.repr 1) tulong)
                                (tptr (talignas 3%N (tptr tvoid))))
                              (tptr tuchar)))
                          (Ssequence
                            (Sset _t1
                              (Ecast
                                (Etempvar _save0 (talignas 3%N (tptr tvoid)))
                                (tptr tuchar)))
                            (Ssequence
                              (Sset _t2
                                (Ecast
                                  (Etempvar _save1 (talignas 3%N (tptr tvoid)))
                                  (tptr tuchar)))
                              (Ssequence
                                (Ssequence
                                  (Sset _i
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      tulong))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i tulong)
                                                     (Etempvar _len1 tulong)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Sset _t'5
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t1 (tptr tuchar))
                                              (Etempvar _i tulong)
                                              (tptr tuchar)) tuchar))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _ptr (tptr tuchar))
                                              (Etempvar _i tulong)
                                              (tptr tuchar)) tuchar)
                                          (Etempvar _t'5 tuchar))))
                                    (Sset _i
                                      (Ebinop Oadd (Etempvar _i tulong)
                                        (Econst_int (Int.repr 1) tint)
                                        tulong))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _i
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        tulong))
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _i tulong)
                                                       (Etempvar _len2 tulong)
                                                       tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Sset _t'4
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t2 (tptr tuchar))
                                                (Etempvar _i tulong)
                                                (tptr tuchar)) tuchar))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _ptr (tptr tuchar))
                                                (Ebinop Oadd
                                                  (Etempvar _len1 tulong)
                                                  (Etempvar _i tulong)
                                                  tulong) (tptr tuchar))
                                              tuchar) (Etempvar _t'4 tuchar))))
                                      (Sset _i
                                        (Ebinop Oadd (Etempvar _i tulong)
                                          (Econst_int (Int.repr 1) tint)
                                          tulong))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _i
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          tulong))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i tulong)
                                                         (Ebinop Osub
                                                           (Etempvar _pad_length tulong)
                                                           (Econst_int (Int.repr 1) tint)
                                                           tulong) tint)
                                            Sskip
                                            Sbreak)
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _ptr (tptr tuchar))
                                                (Ebinop Oadd
                                                  (Ebinop Oadd
                                                    (Etempvar _len1 tulong)
                                                    (Etempvar _len2 tulong)
                                                    tulong)
                                                  (Etempvar _i tulong)
                                                  tulong) (tptr tuchar))
                                              tuchar)
                                            (Econst_int (Int.repr 0) tint)))
                                        (Sset _i
                                          (Ebinop Oadd (Etempvar _i tulong)
                                            (Econst_int (Int.repr 1) tint)
                                            tulong))))
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _ptr (tptr tuchar))
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Etempvar _len1 tulong)
                                                (Etempvar _len2 tulong)
                                                tulong)
                                              (Ebinop Osub
                                                (Etempvar _pad_length tulong)
                                                (Econst_int (Int.repr 1) tint)
                                                tulong) tulong)
                                            (tptr tuchar)) tuchar)
                                        (Ebinop Osub
                                          (Etempvar _pad_length tulong)
                                          (Econst_int (Int.repr 1) tint)
                                          tulong))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'3
                                            (Efield
                                              (Ederef
                                                (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                                (Tstruct _thread_info noattr))
                                              _alloc
                                              (tptr (talignas 3%N (tptr tvoid)))))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                                (Tstruct _thread_info noattr))
                                              _alloc
                                              (tptr (talignas 3%N (tptr tvoid))))
                                            (Ebinop Oadd
                                              (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))
                                              (Etempvar _nalloc tulong)
                                              (tptr (talignas 3%N (tptr tvoid))))))
                                        (Sreturn (Some (Ecast
                                                         (Ebinop Oadd
                                                           (Etempvar _argv (tptr (talignas 3%N (tptr tvoid))))
                                                           (Econst_long (Int64.repr 1) tulong)
                                                           (tptr (talignas 3%N (tptr tvoid))))
                                                         (talignas 3%N (tptr tvoid)))))))))))))))))))))))))
|}.

Definition f_bump_allocptr := {|
  fn_return := (tptr (talignas 3%N (tptr tvoid)));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_new, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _new
    (Efield
      (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc
      (tptr (talignas 3%N (tptr tvoid)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
          (Tstruct _thread_info noattr)) _alloc
        (tptr (talignas 3%N (tptr tvoid))))
      (Ebinop Oadd (Etempvar _new (tptr (talignas 3%N (tptr tvoid))))
        (Etempvar _n tulong) (tptr (talignas 3%N (tptr tvoid)))))
    (Sreturn (Some (Etempvar _new (tptr (talignas 3%N (tptr tvoid))))))))
|}.

Definition f_pack := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_save0, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := ((___ROOT__, (tarray (talignas 3%N (tptr tvoid)) 1)) ::
              (___FRAME__, (Tstruct _stack_frame noattr)) :: nil);
  fn_temps := ((__ALLOC, (tptr (talignas 3%N (tptr tvoid)))) ::
               (__LIMIT, (tptr (talignas 3%N (tptr tvoid)))) ::
               (___PREV__, (tptr (Tstruct _stack_frame noattr))) ::
               (_nalloc, tulong) ::
               (___RTEMP__, (talignas 3%N (tptr tvoid))) ::
               (_temp, (talignas 3%N (tptr tvoid))) :: (_i, tulong) ::
               (_len, tulong) :: (_mod, tulong) :: (_pad_length, tulong) ::
               (_argv, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_ptr, (tptr tuchar)) ::
               (_t'7, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'6, tuchar) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, tulong) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, tulong) ::
               (_t'9, (tptr (Tstruct _stack_frame noattr))) ::
               (_t'8, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _next
      (tptr (talignas 3%N (tptr tvoid))))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sassign
      (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _root
        (tptr (talignas 3%N (tptr tvoid))))
      (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1)))
    (Ssequence
      (Ssequence
        (Sset _t'9
          (Efield
            (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _fp
            (tptr (Tstruct _stack_frame noattr))))
        (Sassign
          (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _prev
            (tptr (Tstruct _stack_frame noattr)))
          (Etempvar _t'9 (tptr (Tstruct _stack_frame noattr)))))
      (Ssequence
        (Sset _temp (Etempvar _save0 (talignas 3%N (tptr tvoid))))
        (Ssequence
          (Sset _len (Ecast (Econst_int (Int.repr 0) tint) tulong))
          (Ssequence
            (Sloop
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _get_Coq_Strings_String_string_tag (Tfunction
                                                               (Tcons
                                                                 (talignas 3%N (tptr tvoid))
                                                                 Tnil) tulong
                                                               cc_default))
                    ((Etempvar _temp (talignas 3%N (tptr tvoid))) :: nil))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tulong)
                                 (Econst_int (Int.repr 1) tint) tint)
                    Sskip
                    Sbreak))
                (Ssequence
                  (Sset _len
                    (Ebinop Oadd (Etempvar _len tulong)
                      (Econst_int (Int.repr 1) tint) tulong))
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar _get_args (Tfunction
                                        (Tcons (talignas 3%N (tptr tvoid))
                                          Tnil)
                                        (tptr (talignas 3%N (tptr tvoid)))
                                        cc_default))
                      ((Etempvar _temp (talignas 3%N (tptr tvoid))) :: nil))
                    (Sset _temp
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))
                          (Econst_int (Int.repr 1) tint)
                          (tptr (talignas 3%N (tptr tvoid))))
                        (talignas 3%N (tptr tvoid)))))))
              Sskip)
            (Ssequence
              (Sset _mod
                (Ebinop Omod (Etempvar _len tulong)
                  (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong))
              (Ssequence
                (Sset _pad_length
                  (Ebinop Osub (Esizeof (talignas 3%N (tptr tvoid)) tulong)
                    (Ebinop Omod (Etempvar _len tulong)
                      (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong)
                    tulong))
                (Ssequence
                  (Sset _nalloc
                    (Ebinop Oadd
                      (Ebinop Odiv
                        (Ebinop Oadd (Etempvar _len tulong)
                          (Etempvar _pad_length tulong) tulong)
                        (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong)
                      (Econst_long (Int64.repr 1) tulong) tulong))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset __LIMIT
                          (Efield
                            (Ederef
                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                              (Tstruct _thread_info noattr)) _limit
                            (tptr (talignas 3%N (tptr tvoid)))))
                        (Sset __ALLOC
                          (Efield
                            (Ederef
                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                              (Tstruct _thread_info noattr)) _alloc
                            (tptr (talignas 3%N (tptr tvoid))))))
                      (Sifthenelse (Eunop Onotbool
                                     (Ebinop Ole (Etempvar _nalloc tulong)
                                       (Ebinop Osub
                                         (Etempvar __LIMIT (tptr (talignas 3%N (tptr tvoid))))
                                         (Etempvar __ALLOC (tptr (talignas 3%N (tptr tvoid))))
                                         tlong) tint) tint)
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                (Tstruct _thread_info noattr)) _nalloc
                              tulong) (Etempvar _nalloc tulong))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                              (Tstruct _thread_info noattr))
                                            _fp
                                            (tptr (Tstruct _stack_frame noattr)))
                                          (Eaddrof
                                            (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                            (tptr (Tstruct _stack_frame noattr))))
                                        (Sassign
                                          (Efield
                                            (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                            _next
                                            (tptr (talignas 3%N (tptr tvoid))))
                                          (Ebinop Oadd
                                            (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr (talignas 3%N (tptr tvoid))))))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr (talignas 3%N (tptr tvoid))))
                                          (talignas 3%N (tptr tvoid)))
                                        (Etempvar _save0 (talignas 3%N (tptr tvoid)))))
                                    (Scall None
                                      (Evar _garbage_collect (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _thread_info noattr))
                                                                 Tnil) tvoid
                                                               cc_default))
                                      ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                                       nil)))
                                  (Sset ___RTEMP__
                                    (Ecast
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        (tptr tvoid))
                                      (talignas 3%N (tptr tvoid)))))
                                (Sset _save0
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                      (Econst_int (Int.repr 0) tint)
                                      (tptr (talignas 3%N (tptr tvoid))))
                                    (talignas 3%N (tptr tvoid)))))
                              (Sset ___PREV__
                                (Efield
                                  (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                  _prev (tptr (Tstruct _stack_frame noattr)))))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                  (Tstruct _thread_info noattr)) _fp
                                (tptr (Tstruct _stack_frame noattr)))
                              (Etempvar ___PREV__ (tptr (Tstruct _stack_frame noattr))))))
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'3)
                          (Evar _bump_allocptr (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _thread_info noattr))
                                                   (Tcons tulong Tnil))
                                                 (tptr (talignas 3%N (tptr tvoid)))
                                                 cc_default))
                          ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                           (Etempvar _nalloc tulong) :: nil))
                        (Sset _argv
                          (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _argv (tptr (talignas 3%N (tptr tvoid))))
                              (Econst_long (Int64.repr 0) tulong)
                              (tptr (talignas 3%N (tptr tvoid))))
                            (talignas 3%N (tptr tvoid)))
                          (Ecast
                            (Ebinop Oadd
                              (Ebinop Oshl
                                (Ebinop Osub (Etempvar _nalloc tulong)
                                  (Econst_int (Int.repr 1) tint) tulong)
                                (Econst_int (Int.repr 10) tint) tulong)
                              (Econst_long (Int64.repr 252) tulong) tulong)
                            (talignas 3%N (tptr tvoid))))
                        (Ssequence
                          (Sset _ptr
                            (Ecast
                              (Ebinop Oadd
                                (Etempvar _argv (tptr (talignas 3%N (tptr tvoid))))
                                (Econst_long (Int64.repr 1) tulong)
                                (tptr (talignas 3%N (tptr tvoid))))
                              (tptr tuchar)))
                          (Ssequence
                            (Sset _temp
                              (Etempvar _save0 (talignas 3%N (tptr tvoid))))
                            (Ssequence
                              (Sloop
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'4)
                                      (Evar _get_Coq_Strings_String_string_tag 
                                      (Tfunction
                                        (Tcons (talignas 3%N (tptr tvoid))
                                          Tnil) tulong cc_default))
                                      ((Etempvar _temp (talignas 3%N (tptr tvoid))) ::
                                       nil))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _t'4 tulong)
                                                   (Econst_int (Int.repr 1) tint)
                                                   tint)
                                      Sskip
                                      Sbreak))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'5)
                                          (Evar _get_args (Tfunction
                                                            (Tcons
                                                              (talignas 3%N (tptr tvoid))
                                                              Tnil)
                                                            (tptr (talignas 3%N (tptr tvoid)))
                                                            cc_default))
                                          ((Etempvar _temp (talignas 3%N (tptr tvoid))) ::
                                           nil))
                                        (Ssequence
                                          (Sset _t'8
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid))))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr (talignas 3%N (tptr tvoid))))
                                              (talignas 3%N (tptr tvoid))))
                                          (Scall (Some _t'6)
                                            (Evar _ascii_to_char (Tfunction
                                                                   (Tcons
                                                                    (talignas 3%N (tptr tvoid))
                                                                    Tnil)
                                                                   tuchar
                                                                   cc_default))
                                            ((Etempvar _t'8 (talignas 3%N (tptr tvoid))) ::
                                             nil))))
                                      (Sassign
                                        (Ederef (Etempvar _ptr (tptr tuchar))
                                          tuchar) (Etempvar _t'6 tuchar)))
                                    (Ssequence
                                      (Sset _ptr
                                        (Ebinop Oadd
                                          (Etempvar _ptr (tptr tuchar))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuchar)))
                                      (Ssequence
                                        (Scall (Some _t'7)
                                          (Evar _get_args (Tfunction
                                                            (Tcons
                                                              (talignas 3%N (tptr tvoid))
                                                              Tnil)
                                                            (tptr (talignas 3%N (tptr tvoid)))
                                                            cc_default))
                                          ((Etempvar _temp (talignas 3%N (tptr tvoid))) ::
                                           nil))
                                        (Sset _temp
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'7 (tptr (talignas 3%N (tptr tvoid))))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr (talignas 3%N (tptr tvoid))))
                                            (talignas 3%N (tptr tvoid))))))))
                                Sskip)
                              (Ssequence
                                (Ssequence
                                  (Sset _i
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      tulong))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i tulong)
                                                     (Ebinop Osub
                                                       (Etempvar _pad_length tulong)
                                                       (Econst_int (Int.repr 1) tint)
                                                       tulong) tint)
                                        Sskip
                                        Sbreak)
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _ptr (tptr tuchar))
                                            (Etempvar _i tulong)
                                            (tptr tuchar)) tuchar)
                                        (Econst_int (Int.repr 0) tint)))
                                    (Sset _i
                                      (Ebinop Oadd (Etempvar _i tulong)
                                        (Econst_int (Int.repr 1) tint)
                                        tulong))))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _ptr (tptr tuchar))
                                        (Etempvar _i tulong) (tptr tuchar))
                                      tuchar) (Etempvar _i tulong))
                                  (Sreturn (Some (Ecast
                                                   (Ebinop Oadd
                                                     (Etempvar _argv (tptr (talignas 3%N (tptr tvoid))))
                                                     (Econst_long (Int64.repr 1) tulong)
                                                     (tptr (talignas 3%N (tptr tvoid))))
                                                   (talignas 3%N (tptr tvoid))))))))))))))))))))))
|}.

Definition f_unpack := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_save0, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := ((___ROOT__, (tarray (talignas 3%N (tptr tvoid)) 2)) ::
              (___FRAME__, (Tstruct _stack_frame noattr)) :: nil);
  fn_temps := ((_c, tuchar) :: (_v, (talignas 3%N (tptr tvoid))) ::
               (_len, tulong) :: (_save1, (talignas 3%N (tptr tvoid))) ::
               (__ALLOC, (tptr (talignas 3%N (tptr tvoid)))) ::
               (__LIMIT, (tptr (talignas 3%N (tptr tvoid)))) ::
               (___PREV__, (tptr (Tstruct _stack_frame noattr))) ::
               (_nalloc, tulong) ::
               (___RTEMP__, (talignas 3%N (tptr tvoid))) ::
               (_t'5, (talignas 3%N (tptr tvoid))) ::
               (_t'4, (talignas 3%N (tptr tvoid))) :: (_t'3, tulong) ::
               (_t'2, (talignas 3%N (tptr tvoid))) :: (_t'1, tulong) ::
               (_t'7, (tptr (Tstruct _stack_frame noattr))) ::
               (_t'6, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _bytestrlen (Tfunction (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                          tulong cc_default))
      ((Etempvar _save0 (talignas 3%N (tptr tvoid))) :: nil))
    (Sset _len (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _make_Coq_Strings_String_string_EmptyString (Tfunction Tnil
                                                            (talignas 3%N (tptr tvoid))
                                                            cc_default)) nil)
      (Sset _save1 (Etempvar _t'2 (talignas 3%N (tptr tvoid)))))
    (Ssequence
      (Sassign
        (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _next
          (tptr (talignas 3%N (tptr tvoid))))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _root
            (tptr (talignas 3%N (tptr tvoid))))
          (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2)))
        (Ssequence
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef
                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _fp
                (tptr (Tstruct _stack_frame noattr))))
            (Sassign
              (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _prev
                (tptr (Tstruct _stack_frame noattr)))
              (Etempvar _t'7 (tptr (Tstruct _stack_frame noattr)))))
          (Ssequence
            (Sloop
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'3 (Etempvar _len tulong))
                    (Sset _len
                      (Ebinop Osub (Etempvar _t'3 tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  (Sifthenelse (Etempvar _t'3 tulong) Sskip Sbreak))
                (Ssequence
                  (Sset _nalloc
                    (Ecast (Econst_int (Int.repr 12) tint) tulong))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset __LIMIT
                          (Efield
                            (Ederef
                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                              (Tstruct _thread_info noattr)) _limit
                            (tptr (talignas 3%N (tptr tvoid)))))
                        (Sset __ALLOC
                          (Efield
                            (Ederef
                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                              (Tstruct _thread_info noattr)) _alloc
                            (tptr (talignas 3%N (tptr tvoid))))))
                      (Sifthenelse (Eunop Onotbool
                                     (Ebinop Ole (Etempvar _nalloc tulong)
                                       (Ebinop Osub
                                         (Etempvar __LIMIT (tptr (talignas 3%N (tptr tvoid))))
                                         (Etempvar __ALLOC (tptr (talignas 3%N (tptr tvoid))))
                                         tlong) tint) tint)
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                (Tstruct _thread_info noattr)) _nalloc
                              tulong) (Etempvar _nalloc tulong))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                                  (Tstruct _thread_info noattr))
                                                _fp
                                                (tptr (Tstruct _stack_frame noattr)))
                                              (Eaddrof
                                                (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                                (tptr (Tstruct _stack_frame noattr))))
                                            (Sassign
                                              (Efield
                                                (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                                _next
                                                (tptr (talignas 3%N (tptr tvoid))))
                                              (Ebinop Oadd
                                                (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2))
                                                (Econst_int (Int.repr 2) tint)
                                                (tptr (talignas 3%N (tptr tvoid))))))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr (talignas 3%N (tptr tvoid))))
                                              (talignas 3%N (tptr tvoid)))
                                            (Etempvar _save0 (talignas 3%N (tptr tvoid)))))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr (talignas 3%N (tptr tvoid))))
                                            (talignas 3%N (tptr tvoid)))
                                          (Etempvar _save1 (talignas 3%N (tptr tvoid)))))
                                      (Scall None
                                        (Evar _garbage_collect (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _thread_info noattr))
                                                                   Tnil)
                                                                 tvoid
                                                                 cc_default))
                                        ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                                         nil)))
                                    (Sset ___RTEMP__
                                      (Ecast
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          (tptr tvoid))
                                        (talignas 3%N (tptr tvoid)))))
                                  (Sset _save0
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2))
                                        (Econst_int (Int.repr 0) tint)
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (talignas 3%N (tptr tvoid)))))
                                (Sset _save1
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 2))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr (talignas 3%N (tptr tvoid))))
                                    (talignas 3%N (tptr tvoid)))))
                              (Sset ___PREV__
                                (Efield
                                  (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                  _prev (tptr (Tstruct _stack_frame noattr)))))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                  (Tstruct _thread_info noattr)) _fp
                                (tptr (Tstruct _stack_frame noattr)))
                              (Etempvar ___PREV__ (tptr (Tstruct _stack_frame noattr))))))
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Sset _t'6
                          (Ederef
                            (Ebinop Oadd
                              (Ecast
                                (Etempvar _save1 (talignas 3%N (tptr tvoid)))
                                (tptr tuchar)) (Etempvar _len tulong)
                              (tptr tuchar)) tuchar))
                        (Sset _c (Ecast (Etempvar _t'6 tuchar) tuchar)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _char_to_value (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _thread_info noattr))
                                                     (Tcons tuchar Tnil))
                                                   (talignas 3%N (tptr tvoid))
                                                   cc_default))
                            ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                             (Etempvar _c tuchar) :: nil))
                          (Sset _v
                            (Etempvar _t'4 (talignas 3%N (tptr tvoid)))))
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar _alloc_make_Coq_Strings_String_string_String 
                            (Tfunction
                              (Tcons (tptr (Tstruct _thread_info noattr))
                                (Tcons (talignas 3%N (tptr tvoid))
                                  (Tcons (talignas 3%N (tptr tvoid)) Tnil)))
                              (talignas 3%N (tptr tvoid)) cc_default))
                            ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                             (Etempvar _v (talignas 3%N (tptr tvoid))) ::
                             (Etempvar _save1 (talignas 3%N (tptr tvoid))) ::
                             nil))
                          (Sset _save1
                            (Etempvar _t'5 (talignas 3%N (tptr tvoid))))))))))
              Sskip)
            (Sreturn (Some (Etempvar _save1 (talignas 3%N (tptr tvoid)))))))))))
|}.

Definition f_scan := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_stream, (tptr (Tstruct ___sFILE noattr))) ::
                (_length, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_capacity, tulong) :: (_buffer, (tptr tuchar)) ::
               (_i, tulong) :: (_c, tint) :: (_newbuf, (tptr tuchar)) ::
               (_t'5, tulong) :: (_t'4, (tptr tvoid)) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, (tptr tvoid)) ::
               (_t'6, (tptr (Tstruct ___sFILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _capacity (Ecast (Econst_int (Int.repr 16) tint) tulong))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Etempvar _capacity tulong) :: nil))
      (Sset _buffer (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool (Etempvar _buffer (tptr tuchar)) tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip)
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Ssequence
          (Sloop
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar _fgetc (Tfunction
                                     (Tcons (tptr (Tstruct ___sFILE noattr))
                                       Tnil) tint cc_default))
                      ((Etempvar _stream (tptr (Tstruct ___sFILE noattr))) ::
                       nil))
                    (Sset _t'3 (Ecast (Etempvar _t'2 tint) tint)))
                  (Sset _c (Etempvar _t'3 tint)))
                (Sifthenelse (Ebinop One (Etempvar _t'3 tint)
                               (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                 tint) tint)
                  Sskip
                  Sbreak))
              (Ssequence
                (Sifthenelse (Ebinop Ogt
                               (Ebinop Oadd (Etempvar _i tulong)
                                 (Econst_int (Int.repr 2) tint) tulong)
                               (Etempvar _capacity tulong) tint)
                  (Ssequence
                    (Sset _capacity
                      (Ebinop Omul (Etempvar _capacity tulong)
                        (Econst_int (Int.repr 2) tint) tulong))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar _realloc (Tfunction
                                           (Tcons (tptr tvoid)
                                             (Tcons tulong Tnil))
                                           (tptr tvoid) cc_default))
                          ((Etempvar _buffer (tptr tuchar)) ::
                           (Etempvar _capacity tulong) :: nil))
                        (Sset _newbuf (Etempvar _t'4 (tptr tvoid))))
                      (Ssequence
                        (Sifthenelse (Eunop Onotbool
                                       (Etempvar _newbuf (tptr tuchar)) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'6
                                (Evar ___stdinp (tptr (Tstruct ___sFILE noattr))))
                              (Scall None
                                (Evar _ungetc (Tfunction
                                                (Tcons tint
                                                  (Tcons
                                                    (tptr (Tstruct ___sFILE noattr))
                                                    Tnil)) tint cc_default))
                                ((Etempvar _c tint) ::
                                 (Etempvar _t'6 (tptr (Tstruct ___sFILE noattr))) ::
                                 nil)))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _buffer (tptr tuchar))
                                    (Etempvar _i tulong) (tptr tuchar))
                                  tuchar) (Econst_int (Int.repr 0) tint))
                              (Sreturn (Some (Etempvar _buffer (tptr tuchar))))))
                          Sskip)
                        (Sset _buffer (Etempvar _newbuf (tptr tuchar))))))
                  Sskip)
                (Ssequence
                  (Sifthenelse (Ebinop Oeq (Etempvar _c tint)
                                 (Econst_int (Int.repr 10) tint) tint)
                    Sbreak
                    Sskip)
                  (Ssequence
                    (Ssequence
                      (Sset _t'5 (Etempvar _i tulong))
                      (Sset _i
                        (Ebinop Oadd (Etempvar _t'5 tulong)
                          (Econst_int (Int.repr 1) tint) tulong)))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _buffer (tptr tuchar))
                          (Etempvar _t'5 tulong) (tptr tuchar)) tuchar)
                      (Ecast (Etempvar _c tint) tuchar))))))
            Sskip)
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _i tulong)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Etempvar _buffer (tptr tuchar)) :: nil))
                (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)))))
              Sskip)
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _buffer (tptr tuchar))
                    (Etempvar _i tulong) (tptr tuchar)) tuchar)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign (Ederef (Etempvar _length (tptr tulong)) tulong)
                  (Etempvar _i tulong))
                (Sreturn (Some (Etempvar _buffer (tptr tuchar))))))))))))
|}.

Definition f_scan_bytestring := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_save0, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := ((___ROOT__, (tarray (talignas 3%N (tptr tvoid)) 1)) ::
              (___FRAME__, (Tstruct _stack_frame noattr)) ::
              (_len, tulong) :: nil);
  fn_temps := ((__ALLOC, (tptr (talignas 3%N (tptr tvoid)))) ::
               (__LIMIT, (tptr (talignas 3%N (tptr tvoid)))) ::
               (___PREV__, (tptr (Tstruct _stack_frame noattr))) ::
               (_nalloc, tulong) ::
               (___RTEMP__, (talignas 3%N (tptr tvoid))) ::
               (_s, (tptr tuchar)) :: (_mod, tulong) ::
               (_pad_length, tulong) ::
               (_argv, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_ptr, (tptr tuchar)) :: (_t, (tptr tuchar)) ::
               (_i, tuchar) :: (_t'1, (tptr tuchar)) ::
               (_t'8, (tptr (Tstruct _stack_frame noattr))) ::
               (_t'7, tulong) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, tuchar) :: (_t'3, tuchar) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _next
      (tptr (talignas 3%N (tptr tvoid))))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sassign
      (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _root
        (tptr (talignas 3%N (tptr tvoid))))
      (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1)))
    (Ssequence
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _fp
            (tptr (Tstruct _stack_frame noattr))))
        (Sassign
          (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _prev
            (tptr (Tstruct _stack_frame noattr)))
          (Etempvar _t'8 (tptr (Tstruct _stack_frame noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _scan (Tfunction
                          (Tcons (tptr (Tstruct ___sFILE noattr))
                            (Tcons (tptr tulong) Tnil)) (tptr tuchar)
                          cc_default))
            ((Ecast (Etempvar _save0 (talignas 3%N (tptr tvoid)))
               (tptr (Tstruct ___sFILE noattr))) ::
             (Eaddrof (Evar _len tulong) (tptr tulong)) :: nil))
          (Sset _s (Etempvar _t'1 (tptr tuchar))))
        (Ssequence
          (Ssequence
            (Sset _t'7 (Evar _len tulong))
            (Sset _mod
              (Ebinop Omod (Etempvar _t'7 tulong)
                (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong)))
          (Ssequence
            (Ssequence
              (Sset _t'6 (Evar _len tulong))
              (Sset _pad_length
                (Ebinop Osub (Esizeof (talignas 3%N (tptr tvoid)) tulong)
                  (Ebinop Omod (Etempvar _t'6 tulong)
                    (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong)
                  tulong)))
            (Ssequence
              (Ssequence
                (Sset _t'5 (Evar _len tulong))
                (Sset _nalloc
                  (Ebinop Oadd
                    (Ebinop Odiv
                      (Ebinop Oadd (Etempvar _t'5 tulong)
                        (Etempvar _pad_length tulong) tulong)
                      (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong)
                    (Econst_int (Int.repr 1) tint) tulong)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset __LIMIT
                      (Efield
                        (Ederef
                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                          (Tstruct _thread_info noattr)) _limit
                        (tptr (talignas 3%N (tptr tvoid)))))
                    (Sset __ALLOC
                      (Efield
                        (Ederef
                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                          (Tstruct _thread_info noattr)) _alloc
                        (tptr (talignas 3%N (tptr tvoid))))))
                  (Sifthenelse (Eunop Onotbool
                                 (Ebinop Ole (Etempvar _nalloc tulong)
                                   (Ebinop Osub
                                     (Etempvar __LIMIT (tptr (talignas 3%N (tptr tvoid))))
                                     (Etempvar __ALLOC (tptr (talignas 3%N (tptr tvoid))))
                                     tlong) tint) tint)
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                            (Tstruct _thread_info noattr)) _nalloc tulong)
                        (Etempvar _nalloc tulong))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                          (Tstruct _thread_info noattr)) _fp
                                        (tptr (Tstruct _stack_frame noattr)))
                                      (Eaddrof
                                        (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                        (tptr (Tstruct _stack_frame noattr))))
                                    (Sassign
                                      (Efield
                                        (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                        _next
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (Ebinop Oadd
                                        (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr (talignas 3%N (tptr tvoid))))))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                        (Econst_int (Int.repr 0) tint)
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (talignas 3%N (tptr tvoid)))
                                    (Etempvar _save0 (talignas 3%N (tptr tvoid)))))
                                (Scall None
                                  (Evar _garbage_collect (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _thread_info noattr))
                                                             Tnil) tvoid
                                                           cc_default))
                                  ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                                   nil)))
                              (Sset ___RTEMP__
                                (Ecast
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    (tptr tvoid))
                                  (talignas 3%N (tptr tvoid)))))
                            (Sset _save0
                              (Ederef
                                (Ebinop Oadd
                                  (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr (talignas 3%N (tptr tvoid))))
                                (talignas 3%N (tptr tvoid)))))
                          (Sset ___PREV__
                            (Efield
                              (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                              _prev (tptr (Tstruct _stack_frame noattr)))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                              (Tstruct _thread_info noattr)) _fp
                            (tptr (Tstruct _stack_frame noattr)))
                          (Etempvar ___PREV__ (tptr (Tstruct _stack_frame noattr))))))
                    Sskip))
                (Ssequence
                  (Sset _argv
                    (Efield
                      (Ederef
                        (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                        (Tstruct _thread_info noattr)) _alloc
                      (tptr (talignas 3%N (tptr tvoid)))))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Ecast
                            (Etempvar _argv (tptr (talignas 3%N (tptr tvoid))))
                            (tptr (talignas 3%N (tptr tvoid))))
                          (Econst_long (Int64.repr 0) tulong)
                          (tptr (talignas 3%N (tptr tvoid))))
                        (talignas 3%N (tptr tvoid)))
                      (Ecast
                        (Ebinop Oadd
                          (Ebinop Oshl
                            (Ebinop Osub (Etempvar _nalloc tulong)
                              (Econst_int (Int.repr 1) tint) tulong)
                            (Econst_int (Int.repr 10) tint) tulong)
                          (Econst_long (Int64.repr 252) tulong) tulong)
                        (talignas 3%N (tptr tvoid))))
                    (Ssequence
                      (Sset _ptr
                        (Ecast
                          (Ebinop Oadd
                            (Etempvar _argv (tptr (talignas 3%N (tptr tvoid))))
                            (Econst_long (Int64.repr 1) tulong)
                            (tptr (talignas 3%N (tptr tvoid))))
                          (tptr tuchar)))
                      (Ssequence
                        (Sset _t
                          (Ecast (Etempvar _s (tptr tuchar)) (tptr tuchar)))
                        (Ssequence
                          (Sloop
                            (Ssequence
                              (Ssequence
                                (Sset _t'4
                                  (Ederef (Etempvar _t (tptr tuchar)) tuchar))
                                (Sifthenelse (Ebinop One
                                               (Etempvar _t'4 tuchar)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  Sskip
                                  Sbreak))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'3
                                    (Ederef (Etempvar _t (tptr tuchar))
                                      tuchar))
                                  (Sassign
                                    (Ederef (Etempvar _ptr (tptr tuchar))
                                      tuchar) (Etempvar _t'3 tuchar)))
                                (Ssequence
                                  (Sset _ptr
                                    (Ebinop Oadd
                                      (Etempvar _ptr (tptr tuchar))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr tuchar)))
                                  (Sset _t
                                    (Ebinop Oadd (Etempvar _t (tptr tuchar))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr tuchar))))))
                            Sskip)
                          (Ssequence
                            (Sset _i
                              (Ecast (Econst_int (Int.repr 0) tint) tuchar))
                            (Ssequence
                              (Swhile
                                (Ebinop Olt (Etempvar _i tuchar)
                                  (Ebinop Osub (Etempvar _pad_length tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)
                                  tint)
                                (Ssequence
                                  (Sassign
                                    (Ederef (Etempvar _ptr (tptr tuchar))
                                      tuchar) (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Sset _ptr
                                      (Ebinop Oadd
                                        (Etempvar _ptr (tptr tuchar))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuchar)))
                                    (Sset _i
                                      (Ecast
                                        (Ebinop Oadd (Etempvar _i tuchar)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) tuchar)))))
                              (Ssequence
                                (Sassign
                                  (Ederef (Etempvar _ptr (tptr tuchar))
                                    tuchar) (Etempvar _i tuchar))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'2
                                      (Efield
                                        (Ederef
                                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                          (Tstruct _thread_info noattr))
                                        _alloc
                                        (tptr (talignas 3%N (tptr tvoid)))))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                          (Tstruct _thread_info noattr))
                                        _alloc
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (Ebinop Oadd
                                        (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))
                                        (Etempvar _nalloc tulong)
                                        (tptr (talignas 3%N (tptr tvoid))))))
                                  (Sreturn (Some (Ecast
                                                   (Ebinop Oadd
                                                     (Etempvar _argv (tptr (talignas 3%N (tptr tvoid))))
                                                     (Econst_long (Int64.repr 1) tulong)
                                                     (tptr (talignas 3%N (tptr tvoid))))
                                                   (talignas 3%N (tptr tvoid))))))))))))))))))))))
|}.

Definition f_runM := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_a, (talignas 3%N (tptr tvoid))) ::
                (_instream, (talignas 3%N (tptr tvoid))) ::
                (_outstream, (talignas 3%N (tptr tvoid))) ::
                (_action, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := ((___ROOT__, (tarray (talignas 3%N (tptr tvoid)) 4)) ::
              (___FRAME__, (Tstruct _stack_frame noattr)) :: nil);
  fn_temps := ((_temp, (talignas 3%N (tptr tvoid))) ::
               (_arg0, (talignas 3%N (tptr tvoid))) ::
               (_arg1, (talignas 3%N (tptr tvoid))) ::
               (__ALLOC, (tptr (talignas 3%N (tptr tvoid)))) ::
               (__LIMIT, (tptr (talignas 3%N (tptr tvoid)))) ::
               (___PREV__, (tptr (Tstruct _stack_frame noattr))) ::
               (_nalloc, tulong) ::
               (___RTEMP__, (talignas 3%N (tptr tvoid))) ::
               (_s, (talignas 3%N (tptr tvoid))) :: (_len, tulong) ::
               (_i, tulong) :: (_t'9, (talignas 3%N (tptr tvoid))) ::
               (_t'8, tulong) :: (_t'7, (talignas 3%N (tptr tvoid))) ::
               (_t'6, (talignas 3%N (tptr tvoid))) ::
               (_t'5, (talignas 3%N (tptr tvoid))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) :: (_t'1, tint) ::
               (_t'12, (tptr (Tstruct _stack_frame noattr))) ::
               (_t'11, (talignas 3%N (tptr tvoid))) :: (_t'10, tuchar) ::
               nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _next
      (tptr (talignas 3%N (tptr tvoid))))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sassign
      (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _root
        (tptr (talignas 3%N (tptr tvoid))))
      (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4)))
    (Ssequence
      (Ssequence
        (Sset _t'12
          (Efield
            (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _fp
            (tptr (Tstruct _stack_frame noattr))))
        (Sassign
          (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _prev
            (tptr (Tstruct _stack_frame noattr)))
          (Etempvar _t'12 (tptr (Tstruct _stack_frame noattr)))))
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_prog_C_MI_tag (Tfunction
                                     (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                     tint cc_default))
          ((Etempvar _action (talignas 3%N (tptr tvoid))) :: nil))
        (Sswitch (Etempvar _t'1 tint)
          (LScons (Some 0)
            (Ssequence
              (Scall (Some _t'2)
                (Evar _get_args (Tfunction
                                  (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                  (tptr (talignas 3%N (tptr tvoid)))
                                  cc_default))
                ((Etempvar _action (talignas 3%N (tptr tvoid))) :: nil))
              (Ssequence
                (Sset _t'11
                  (Ederef
                    (Ebinop Oadd
                      (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))
                      (Econst_int (Int.repr 1) tint)
                      (tptr (talignas 3%N (tptr tvoid))))
                    (talignas 3%N (tptr tvoid))))
                (Sreturn (Some (Etempvar _t'11 (talignas 3%N (tptr tvoid)))))))
            (LScons (Some 1)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _get_args (Tfunction
                                      (Tcons (talignas 3%N (tptr tvoid))
                                        Tnil)
                                      (tptr (talignas 3%N (tptr tvoid)))
                                      cc_default))
                    ((Etempvar _action (talignas 3%N (tptr tvoid))) :: nil))
                  (Sset _arg0
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))
                        (Econst_int (Int.repr 2) tint)
                        (tptr (talignas 3%N (tptr tvoid))))
                      (talignas 3%N (tptr tvoid)))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _get_args (Tfunction
                                        (Tcons (talignas 3%N (tptr tvoid))
                                          Tnil)
                                        (tptr (talignas 3%N (tptr tvoid)))
                                        cc_default))
                      ((Etempvar _action (talignas 3%N (tptr tvoid))) :: nil))
                    (Sset _arg1
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid))))
                          (Econst_int (Int.repr 3) tint)
                          (tptr (talignas 3%N (tptr tvoid))))
                        (talignas 3%N (tptr tvoid)))))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                                  (Tstruct _thread_info noattr))
                                                _fp
                                                (tptr (Tstruct _stack_frame noattr)))
                                              (Eaddrof
                                                (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                                (tptr (Tstruct _stack_frame noattr))))
                                            (Sassign
                                              (Efield
                                                (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                                _next
                                                (tptr (talignas 3%N (tptr tvoid))))
                                              (Ebinop Oadd
                                                (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                                (Econst_int (Int.repr 3) tint)
                                                (tptr (talignas 3%N (tptr tvoid))))))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                                (Econst_int (Int.repr 0) tint)
                                                (tptr (talignas 3%N (tptr tvoid))))
                                              (talignas 3%N (tptr tvoid)))
                                            (Etempvar _arg1 (talignas 3%N (tptr tvoid)))))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr (talignas 3%N (tptr tvoid))))
                                            (talignas 3%N (tptr tvoid)))
                                          (Etempvar _instream (talignas 3%N (tptr tvoid)))))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                            (Econst_int (Int.repr 2) tint)
                                            (tptr (talignas 3%N (tptr tvoid))))
                                          (talignas 3%N (tptr tvoid)))
                                        (Etempvar _outstream (talignas 3%N (tptr tvoid)))))
                                    (Scall (Some _t'5)
                                      (Evar _runM (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _thread_info noattr))
                                                      (Tcons
                                                        (talignas 3%N (tptr tvoid))
                                                        (Tcons
                                                          (talignas 3%N (tptr tvoid))
                                                          (Tcons
                                                            (talignas 3%N (tptr tvoid))
                                                            (Tcons
                                                              (talignas 3%N (tptr tvoid))
                                                              Tnil)))))
                                                    (talignas 3%N (tptr tvoid))
                                                    cc_default))
                                      ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                                       (Ecast
                                         (Econst_long (Int64.repr 1) tulong)
                                         (talignas 3%N (tptr tvoid))) ::
                                       (Etempvar _instream (talignas 3%N (tptr tvoid))) ::
                                       (Etempvar _outstream (talignas 3%N (tptr tvoid))) ::
                                       (Etempvar _arg0 (talignas 3%N (tptr tvoid))) ::
                                       nil)))
                                  (Sset ___RTEMP__
                                    (Etempvar _t'5 (talignas 3%N (tptr tvoid)))))
                                (Sset _arg1
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                      (Econst_int (Int.repr 0) tint)
                                      (tptr (talignas 3%N (tptr tvoid))))
                                    (talignas 3%N (tptr tvoid)))))
                              (Sset _instream
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr (talignas 3%N (tptr tvoid))))
                                  (talignas 3%N (tptr tvoid)))))
                            (Sset _outstream
                              (Ederef
                                (Ebinop Oadd
                                  (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                  (Econst_int (Int.repr 2) tint)
                                  (tptr (talignas 3%N (tptr tvoid))))
                                (talignas 3%N (tptr tvoid)))))
                          (Sset ___PREV__
                            (Efield
                              (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                              _prev (tptr (Tstruct _stack_frame noattr)))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                              (Tstruct _thread_info noattr)) _fp
                            (tptr (Tstruct _stack_frame noattr)))
                          (Etempvar ___PREV__ (tptr (Tstruct _stack_frame noattr)))))
                      (Sset _temp
                        (Etempvar ___RTEMP__ (talignas 3%N (tptr tvoid)))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                                (Tstruct _thread_info noattr))
                                              _fp
                                              (tptr (Tstruct _stack_frame noattr)))
                                            (Eaddrof
                                              (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                              (tptr (Tstruct _stack_frame noattr))))
                                          (Sassign
                                            (Efield
                                              (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                              _next
                                              (tptr (talignas 3%N (tptr tvoid))))
                                            (Ebinop Oadd
                                              (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                              (Econst_int (Int.repr 2) tint)
                                              (tptr (talignas 3%N (tptr tvoid))))))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                              (Econst_int (Int.repr 0) tint)
                                              (tptr (talignas 3%N (tptr tvoid))))
                                            (talignas 3%N (tptr tvoid)))
                                          (Etempvar _instream (talignas 3%N (tptr tvoid)))))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr (talignas 3%N (tptr tvoid))))
                                          (talignas 3%N (tptr tvoid)))
                                        (Etempvar _outstream (talignas 3%N (tptr tvoid)))))
                                    (Scall (Some _t'6)
                                      (Evar _call (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _thread_info noattr))
                                                      (Tcons
                                                        (talignas 3%N (tptr tvoid))
                                                        (Tcons
                                                          (talignas 3%N (tptr tvoid))
                                                          Tnil)))
                                                    (talignas 3%N (tptr tvoid))
                                                    cc_default))
                                      ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                                       (Etempvar _arg1 (talignas 3%N (tptr tvoid))) ::
                                       (Etempvar _temp (talignas 3%N (tptr tvoid))) ::
                                       nil)))
                                  (Sset ___RTEMP__
                                    (Etempvar _t'6 (talignas 3%N (tptr tvoid)))))
                                (Sset _instream
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                      (Econst_int (Int.repr 0) tint)
                                      (tptr (talignas 3%N (tptr tvoid))))
                                    (talignas 3%N (tptr tvoid)))))
                              (Sset _outstream
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 4))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr (talignas 3%N (tptr tvoid))))
                                  (talignas 3%N (tptr tvoid)))))
                            (Sset ___PREV__
                              (Efield
                                (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                _prev (tptr (Tstruct _stack_frame noattr)))))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                (Tstruct _thread_info noattr)) _fp
                              (tptr (Tstruct _stack_frame noattr)))
                            (Etempvar ___PREV__ (tptr (Tstruct _stack_frame noattr)))))
                        (Sset _temp
                          (Etempvar ___RTEMP__ (talignas 3%N (tptr tvoid)))))
                      (Ssequence
                        (Scall (Some _t'7)
                          (Evar _runM (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _thread_info noattr))
                                          (Tcons (talignas 3%N (tptr tvoid))
                                            (Tcons
                                              (talignas 3%N (tptr tvoid))
                                              (Tcons
                                                (talignas 3%N (tptr tvoid))
                                                (Tcons
                                                  (talignas 3%N (tptr tvoid))
                                                  Tnil)))))
                                        (talignas 3%N (tptr tvoid))
                                        cc_default))
                          ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                           (Ecast (Econst_long (Int64.repr 1) tulong)
                             (talignas 3%N (tptr tvoid))) ::
                           (Etempvar _instream (talignas 3%N (tptr tvoid))) ::
                           (Etempvar _outstream (talignas 3%N (tptr tvoid))) ::
                           (Etempvar _temp (talignas 3%N (tptr tvoid))) ::
                           nil))
                        (Sreturn (Some (Etempvar _t'7 (talignas 3%N (tptr tvoid))))))))))
              (LScons (Some 2)
                (Ssequence
                  (Sset _s
                    (Ederef
                      (Ecast (Etempvar _action (talignas 3%N (tptr tvoid)))
                        (tptr (talignas 3%N (tptr tvoid))))
                      (talignas 3%N (tptr tvoid))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'8)
                        (Evar _bytestrlen (Tfunction
                                            (Tcons
                                              (talignas 3%N (tptr tvoid))
                                              Tnil) tulong cc_default))
                        ((Etempvar _s (talignas 3%N (tptr tvoid))) :: nil))
                      (Sset _len (Etempvar _t'8 tulong)))
                    (Ssequence
                      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
                      (Ssequence
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                           (Etempvar _len tulong) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _t'10
                                (Ederef
                                  (Ebinop Oadd
                                    (Ecast
                                      (Etempvar _s (talignas 3%N (tptr tvoid)))
                                      (tptr tuchar)) (Etempvar _i tulong)
                                    (tptr tuchar)) tuchar))
                              (Scall None
                                (Evar _fprintf (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct ___sFILE noattr))
                                                   (Tcons (tptr tschar) Tnil))
                                                 tint
                                                 {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                                ((Ecast
                                   (Etempvar _outstream (talignas 3%N (tptr tvoid)))
                                   (tptr (Tstruct ___sFILE noattr))) ::
                                 (Evar ___stringlit_1 (tarray tschar 3)) ::
                                 (Etempvar _t'10 tuchar) :: nil))))
                          (Sset _i
                            (Ebinop Oadd (Etempvar _i tulong)
                              (Econst_int (Int.repr 1) tint) tulong)))
                        (Ssequence
                          (Scall None
                            (Evar _fprintf (Tfunction
                                             (Tcons
                                               (tptr (Tstruct ___sFILE noattr))
                                               (Tcons (tptr tschar) Tnil))
                                             tint
                                             {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
                            ((Ecast
                               (Etempvar _outstream (talignas 3%N (tptr tvoid)))
                               (tptr (Tstruct ___sFILE noattr))) ::
                             (Evar ___stringlit_2 (tarray tschar 2)) :: nil))
                          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
                (LScons (Some 3)
                  (Ssequence
                    (Scall (Some _t'9)
                      (Evar _scan_bytestring (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _thread_info noattr))
                                                 (Tcons
                                                   (talignas 3%N (tptr tvoid))
                                                   Tnil))
                                               (talignas 3%N (tptr tvoid))
                                               cc_default))
                      ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                       (Etempvar _instream (talignas 3%N (tptr tvoid))) ::
                       nil))
                    (Sreturn (Some (Etempvar _t'9 (talignas 3%N (tptr tvoid))))))
                  (LScons None
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                    LSnil))))))))))
|}.

Definition f_get_stdin := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__tt, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct ___sFILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Evar ___stdinp (tptr (Tstruct ___sFILE noattr))))
  (Sreturn (Some (Ecast (Etempvar _t'1 (tptr (Tstruct ___sFILE noattr)))
                   (talignas 3%N (tptr tvoid))))))
|}.

Definition f_get_stdout := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__tt, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct ___sFILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Evar ___stdoutp (tptr (Tstruct ___sFILE noattr))))
  (Sreturn (Some (Ecast (Etempvar _t'1 (tptr (Tstruct ___sFILE noattr)))
                   (talignas 3%N (tptr tvoid))))))
|}.

Definition composites : list composite_definition :=
(Composite _space Struct
   (Member_plain _start (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _next (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _limit (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _rem_limit (tptr (talignas 3%N (tptr tvoid))) :: nil)
   noattr ::
 Composite _heap Struct
   (Member_plain _spaces (tarray (Tstruct _space noattr) 43) :: nil)
   noattr ::
 Composite _stack_frame Struct
   (Member_plain _next (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _root (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _prev (tptr (Tstruct _stack_frame noattr)) :: nil)
   noattr ::
 Composite _thread_info Struct
   (Member_plain _alloc (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _limit (tptr (talignas 3%N (tptr tvoid))) ::
    Member_plain _heap (tptr (Tstruct _heap noattr)) ::
    Member_plain _args (tarray (talignas 3%N (tptr tvoid)) 1024) ::
    Member_plain _fp (tptr (Tstruct _stack_frame noattr)) ::
    Member_plain _nalloc tulong :: Member_plain _odata (tptr tvoid) :: nil)
   noattr ::
 Composite ___sbuf Struct
   (Member_plain __base (tptr tuchar) :: Member_plain __size tint :: nil)
   noattr ::
 Composite ___sFILE Struct
   (Member_plain __p (tptr tuchar) :: Member_plain __r tint ::
    Member_plain __w tint :: Member_plain __flags tshort ::
    Member_plain __file tshort ::
    Member_plain __bf (Tstruct ___sbuf noattr) ::
    Member_plain __lbfsize tint :: Member_plain __cookie (tptr tvoid) ::
    Member_plain __close
      (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default)) ::
    Member_plain __read
      (tptr (Tfunction
              (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tint Tnil)))
              tint cc_default)) ::
    Member_plain __seek
      (tptr (Tfunction (Tcons (tptr tvoid) (Tcons tlong (Tcons tint Tnil)))
              tlong cc_default)) ::
    Member_plain __write
      (tptr (Tfunction
              (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tint Tnil)))
              tint cc_default)) ::
    Member_plain __ub (Tstruct ___sbuf noattr) ::
    Member_plain __extra (tptr (Tstruct ___sFILEX noattr)) ::
    Member_plain __ur tint :: Member_plain __ubuf (tarray tuchar 3) ::
    Member_plain __nbuf (tarray tuchar 1) ::
    Member_plain __lb (Tstruct ___sbuf noattr) ::
    Member_plain __blksize tint :: Member_plain __offset tlong :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fence,
   Gfun(External (EF_builtin "__builtin_fence"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_garbage_collect,
   Gfun(External (EF_external "garbage_collect"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _thread_info noattr)) Tnil) tvoid cc_default)) ::
 (___stdinp, Gvar v___stdinp) :: (___stdoutp, Gvar v___stdoutp) ::
 (_fgetc,
   Gfun(External (EF_external "fgetc"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct ___sFILE noattr)) Tnil) tint cc_default)) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct ___sFILE noattr)) (Tcons (tptr tschar) Tnil)) tint
     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|})) ::
 (_ungetc,
   Gfun(External (EF_external "ungetc"
                   (mksignature (AST.Tint :: AST.Tlong :: nil) AST.Tint
                     cc_default))
     (Tcons tint (Tcons (tptr (Tstruct ___sFILE noattr)) Tnil)) tint
     cc_default)) ::
 (_get_args,
   Gfun(External (EF_external "get_args"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (talignas 3%N (tptr tvoid)) Tnil)
     (tptr (talignas 3%N (tptr tvoid))) cc_default)) ::
 (_make_Coq_Init_Datatypes_bool_true,
   Gfun(External (EF_external "make_Coq_Init_Datatypes_bool_true"
                   (mksignature nil AST.Tlong cc_default)) Tnil
     (talignas 3%N (tptr tvoid)) cc_default)) ::
 (_make_Coq_Init_Datatypes_bool_false,
   Gfun(External (EF_external "make_Coq_Init_Datatypes_bool_false"
                   (mksignature nil AST.Tlong cc_default)) Tnil
     (talignas 3%N (tptr tvoid)) cc_default)) ::
 (_alloc_make_Coq_Strings_Ascii_ascii_Ascii,
   Gfun(External (EF_external "alloc_make_Coq_Strings_Ascii_ascii_Ascii"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _thread_info noattr))
       (Tcons (talignas 3%N (tptr tvoid))
         (Tcons (talignas 3%N (tptr tvoid))
           (Tcons (talignas 3%N (tptr tvoid))
             (Tcons (talignas 3%N (tptr tvoid))
               (Tcons (talignas 3%N (tptr tvoid))
                 (Tcons (talignas 3%N (tptr tvoid))
                   (Tcons (talignas 3%N (tptr tvoid))
                     (Tcons (talignas 3%N (tptr tvoid)) Tnil)))))))))
     (talignas 3%N (tptr tvoid)) cc_default)) ::
 (_make_Coq_Strings_String_string_EmptyString,
   Gfun(External (EF_external "make_Coq_Strings_String_string_EmptyString"
                   (mksignature nil AST.Tlong cc_default)) Tnil
     (talignas 3%N (tptr tvoid)) cc_default)) ::
 (_alloc_make_Coq_Strings_String_string_String,
   Gfun(External (EF_external "alloc_make_Coq_Strings_String_string_String"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _thread_info noattr))
       (Tcons (talignas 3%N (tptr tvoid))
         (Tcons (talignas 3%N (tptr tvoid)) Tnil)))
     (talignas 3%N (tptr tvoid)) cc_default)) ::
 (_get_Coq_Init_Datatypes_bool_tag,
   Gfun(External (EF_external "get_Coq_Init_Datatypes_bool_tag"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (talignas 3%N (tptr tvoid)) Tnil) tulong cc_default)) ::
 (_get_Coq_Strings_String_string_tag,
   Gfun(External (EF_external "get_Coq_Strings_String_string_tag"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (talignas 3%N (tptr tvoid)) Tnil) tulong cc_default)) ::
 (_call,
   Gfun(External (EF_external "call"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr (Tstruct _thread_info noattr))
       (Tcons (talignas 3%N (tptr tvoid))
         (Tcons (talignas 3%N (tptr tvoid)) Tnil)))
     (talignas 3%N (tptr tvoid)) cc_default)) ::
 (_strlen,
   Gfun(External (EF_external "strlen"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tschar) Tnil) tulong cc_default)) ::
 (_bytestrlen, Gfun(Internal f_bytestrlen)) ::
 (_ascii_to_char, Gfun(Internal f_ascii_to_char)) ::
 (_bool_to_value, Gfun(Internal f_bool_to_value)) ::
 (_char_to_value, Gfun(Internal f_char_to_value)) ::
 (_string_to_value, Gfun(Internal f_string_to_value)) ::
 (_append, Gfun(Internal f_append)) ::
 (_bump_allocptr, Gfun(Internal f_bump_allocptr)) ::
 (_pack, Gfun(Internal f_pack)) :: (_unpack, Gfun(Internal f_unpack)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_realloc,
   Gfun(External (EF_external "realloc"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_scan, Gfun(Internal f_scan)) ::
 (_scan_bytestring, Gfun(Internal f_scan_bytestring)) ::
 (_get_prog_C_MI_tag,
   Gfun(External (EF_external "get_prog_C_MI_tag"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (talignas 3%N (tptr tvoid)) Tnil) tint cc_default)) ::
 (_runM, Gfun(Internal f_runM)) ::
 (_get_stdin, Gfun(Internal f_get_stdin)) ::
 (_get_stdout, Gfun(Internal f_get_stdout)) :: nil).

Definition public_idents : list ident :=
(_get_stdout :: _get_stdin :: _runM :: _get_prog_C_MI_tag ::
 _scan_bytestring :: _scan :: _free :: _realloc :: _malloc :: _unpack ::
 _pack :: _bump_allocptr :: _append :: _string_to_value :: _char_to_value ::
 _bool_to_value :: _ascii_to_char :: _bytestrlen :: _strlen :: _call ::
 _get_Coq_Strings_String_string_tag :: _get_Coq_Init_Datatypes_bool_tag ::
 _alloc_make_Coq_Strings_String_string_String ::
 _make_Coq_Strings_String_string_EmptyString ::
 _alloc_make_Coq_Strings_Ascii_ascii_Ascii ::
 _make_Coq_Init_Datatypes_bool_false :: _make_Coq_Init_Datatypes_bool_true ::
 _get_args :: _ungetc :: _fprintf :: _fgetc :: ___stdoutp :: ___stdinp ::
 _garbage_collect :: ___builtin_debug :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_clsll ::
 ___builtin_clsl :: ___builtin_cls :: ___builtin_fence ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


