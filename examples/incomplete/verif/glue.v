From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "glue.c".
  Definition normalized := true.
End Info.

Definition _Coq_Init_Datatypes_O_args : ident := 6%positive.
Definition _Coq_Init_Datatypes_S_arg_0 : ident := 7%positive.
Definition _Coq_Init_Datatypes_S_args : ident := 8%positive.
Definition _Coq_Init_Datatypes_cons_arg_0 : ident := 10%positive.
Definition _Coq_Init_Datatypes_cons_arg_1 : ident := 11%positive.
Definition _Coq_Init_Datatypes_cons_args : ident := 12%positive.
Definition _Coq_Init_Datatypes_false_args : ident := 14%positive.
Definition _Coq_Init_Datatypes_nil_args : ident := 9%positive.
Definition _Coq_Init_Datatypes_true_args : ident := 13%positive.
Definition ___builtin_ais_annot : ident := 15%positive.
Definition ___builtin_annot : ident := 32%positive.
Definition ___builtin_annot_intval : ident := 33%positive.
Definition ___builtin_bswap : ident := 17%positive.
Definition ___builtin_bswap16 : ident := 19%positive.
Definition ___builtin_bswap32 : ident := 18%positive.
Definition ___builtin_bswap64 : ident := 16%positive.
Definition ___builtin_clz : ident := 20%positive.
Definition ___builtin_clzl : ident := 21%positive.
Definition ___builtin_clzll : ident := 22%positive.
Definition ___builtin_ctz : ident := 23%positive.
Definition ___builtin_ctzl : ident := 24%positive.
Definition ___builtin_ctzll : ident := 25%positive.
Definition ___builtin_debug : ident := 70%positive.
Definition ___builtin_expect : ident := 44%positive.
Definition ___builtin_fabs : ident := 26%positive.
Definition ___builtin_fabsf : ident := 27%positive.
Definition ___builtin_fmadd : ident := 62%positive.
Definition ___builtin_fmax : ident := 60%positive.
Definition ___builtin_fmin : ident := 61%positive.
Definition ___builtin_fmsub : ident := 63%positive.
Definition ___builtin_fnmadd : ident := 64%positive.
Definition ___builtin_fnmsub : ident := 65%positive.
Definition ___builtin_fsqrt : ident := 28%positive.
Definition ___builtin_membar : ident := 34%positive.
Definition ___builtin_memcpy_aligned : ident := 30%positive.
Definition ___builtin_read16_reversed : ident := 66%positive.
Definition ___builtin_read32_reversed : ident := 67%positive.
Definition ___builtin_sel : ident := 31%positive.
Definition ___builtin_sqrt : ident := 29%positive.
Definition ___builtin_unreachable : ident := 43%positive.
Definition ___builtin_va_arg : ident := 36%positive.
Definition ___builtin_va_copy : ident := 37%positive.
Definition ___builtin_va_end : ident := 38%positive.
Definition ___builtin_va_start : ident := 35%positive.
Definition ___builtin_write16_reversed : ident := 68%positive.
Definition ___builtin_write32_reversed : ident := 69%positive.
Definition ___compcert_i64_dtos : ident := 45%positive.
Definition ___compcert_i64_dtou : ident := 46%positive.
Definition ___compcert_i64_sar : ident := 57%positive.
Definition ___compcert_i64_sdiv : ident := 51%positive.
Definition ___compcert_i64_shl : ident := 55%positive.
Definition ___compcert_i64_shr : ident := 56%positive.
Definition ___compcert_i64_smod : ident := 53%positive.
Definition ___compcert_i64_smulh : ident := 58%positive.
Definition ___compcert_i64_stod : ident := 47%positive.
Definition ___compcert_i64_stof : ident := 49%positive.
Definition ___compcert_i64_udiv : ident := 52%positive.
Definition ___compcert_i64_umod : ident := 54%positive.
Definition ___compcert_i64_umulh : ident := 59%positive.
Definition ___compcert_i64_utod : ident := 48%positive.
Definition ___compcert_i64_utof : ident := 50%positive.
Definition ___compcert_va_composite : ident := 42%positive.
Definition ___compcert_va_float64 : ident := 41%positive.
Definition ___compcert_va_int32 : ident := 39%positive.
Definition ___compcert_va_int64 : ident := 40%positive.
Definition _alloc : ident := 1%positive.
Definition _alloc_make_Coq_Init_Datatypes_list_cons : ident := 96%positive.
Definition _alloc_make_Coq_Init_Datatypes_nat_S : ident := 92%positive.
Definition _arg : ident := 116%positive.
Definition _arg0 : ident := 88%positive.
Definition _arg1 : ident := 94%positive.
Definition _args : ident := 4%positive.
Definition _argv : ident := 89%positive.
Definition _b : ident := 99%positive.
Definition _call : ident := 123%positive.
Definition _clo : ident := 119%positive.
Definition _env : ident := 115%positive.
Definition _envi : ident := 121%positive.
Definition _exit : ident := 71%positive.
Definition _f : ident := 120%positive.
Definition _fun_lit : ident := 75%positive.
Definition _get_Coq_Init_Datatypes_O_args : ident := 104%positive.
Definition _get_Coq_Init_Datatypes_S_args : ident := 105%positive.
Definition _get_Coq_Init_Datatypes_bool_tag : ident := 103%positive.
Definition _get_Coq_Init_Datatypes_cons_args : ident := 107%positive.
Definition _get_Coq_Init_Datatypes_false_args : ident := 109%positive.
Definition _get_Coq_Init_Datatypes_list_tag : ident := 102%positive.
Definition _get_Coq_Init_Datatypes_nat_tag : ident := 101%positive.
Definition _get_Coq_Init_Datatypes_nil_args : ident := 106%positive.
Definition _get_Coq_Init_Datatypes_true_args : ident := 108%positive.
Definition _get_boxed_ordinal : ident := 83%positive.
Definition _get_unboxed_ordinal : ident := 82%positive.
Definition _halt : ident := 117%positive.
Definition _halt_clo : ident := 118%positive.
Definition _heap : ident := 3%positive.
Definition _is_ptr : ident := 80%positive.
Definition _limit : ident := 2%positive.
Definition _lparen_lit : ident := 72%positive.
Definition _main : ident := 124%positive.
Definition _make_Coq_Init_Datatypes_bool_false : ident := 98%positive.
Definition _make_Coq_Init_Datatypes_bool_true : ident := 97%positive.
Definition _make_Coq_Init_Datatypes_list_cons : ident := 95%positive.
Definition _make_Coq_Init_Datatypes_list_nil : ident := 93%positive.
Definition _make_Coq_Init_Datatypes_nat_O : ident := 87%positive.
Definition _make_Coq_Init_Datatypes_nat_S : ident := 90%positive.
Definition _names_of_Coq_Init_Datatypes_bool : ident := 86%positive.
Definition _names_of_Coq_Init_Datatypes_list : ident := 85%positive.
Definition _names_of_Coq_Init_Datatypes_nat : ident := 84%positive.
Definition _print_Coq_Init_Datatypes_bool : ident := 114%positive.
Definition _print_Coq_Init_Datatypes_list : ident := 113%positive.
Definition _print_Coq_Init_Datatypes_nat : ident := 111%positive.
Definition _print_param_A : ident := 112%positive.
Definition _printf : ident := 79%positive.
Definition _prop_lit : ident := 78%positive.
Definition _ret : ident := 122%positive.
Definition _rparen_lit : ident := 73%positive.
Definition _space_lit : ident := 74%positive.
Definition _t : ident := 100%positive.
Definition _tag : ident := 110%positive.
Definition _thread_info : ident := 5%positive.
Definition _tinfo : ident := 91%positive.
Definition _type_lit : ident := 76%positive.
Definition _unk_lit : ident := 77%positive.
Definition _v : ident := 81%positive.
Definition _t'1 : ident := 125%positive.
Definition _t'2 : ident := 126%positive.
Definition _t'3 : ident := 127%positive.
Definition _t'4 : ident := 128%positive.

Definition v_lparen_lit := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_rparen_lit := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_space_lit := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_fun_lit := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_type_lit := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_unk_lit := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_prop_lit := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_get_unboxed_ordinal := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oshr (Etempvar _v tulong)
                 (Econst_long (Int64.repr 1) tulong) tulong)))
|}.

Definition f_get_boxed_ordinal := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd (Ecast (Etempvar _v tulong) (tptr tulong))
        (Econst_long (Int64.repr (-1)) tulong) (tptr tulong)) tulong))
  (Sreturn (Some (Ebinop Oand (Etempvar _t'1 tulong)
                   (Econst_long (Int64.repr 255) tulong) tulong))))
|}.

Definition v_names_of_Coq_Init_Datatypes_nat := {|
  gvar_info := (tarray (tarray tschar 2) 2);
  gvar_init := (Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_names_of_Coq_Init_Datatypes_list := {|
  gvar_info := (tarray (tarray tschar 5) 2);
  gvar_init := (Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_names_of_Coq_Init_Datatypes_bool := {|
  gvar_info := (tarray (tarray tschar 6) 2);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_make_Coq_Init_Datatypes_nat_O := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 1) tint)))
|}.

Definition f_make_Coq_Init_Datatypes_nat_S := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_arg0, tulong) :: (_argv, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
        (Econst_long (Int64.repr 0) tulong) (tptr tulong)) tulong)
    (Econst_long (Int64.repr 1024) tulong))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
          (Econst_long (Int64.repr 1) tulong) (tptr tulong)) tulong)
      (Etempvar _arg0 tulong))
    (Sreturn (Some (Ebinop Oadd (Etempvar _argv (tptr tulong))
                     (Econst_long (Int64.repr 1) tulong) (tptr tulong))))))
|}.

Definition f_alloc_make_Coq_Init_Datatypes_nat_S := {|
  fn_return := (tptr tulong);
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_arg0, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_argv, (tptr tulong)) :: (_t'3, (tptr tulong)) ::
               (_t'2, (tptr tulong)) :: (_t'1, (tptr tulong)) :: nil);
  fn_body :=
(Ssequence
  (Sset _argv
    (Efield
      (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _limit (tptr tulong)))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
        (Sifthenelse (Ebinop Olt
                       (Ebinop Osub (Etempvar _t'2 (tptr tulong))
                         (Etempvar _t'3 (tptr tulong)) tlong)
                       (Econst_int (Int.repr 3) tint) tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
            (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong)
        (Econst_int (Int.repr 1024) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
              (Econst_int (Int.repr 1) tint) (tptr tulong)) tulong)
          (Etempvar _arg0 tulong))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef
                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc (tptr tulong))
              (Ebinop Oadd (Etempvar _t'1 (tptr tulong))
                (Econst_int (Int.repr 2) tint) (tptr tulong))))
          (Sreturn (Some (Ebinop Oadd (Etempvar _argv (tptr tulong))
                           (Econst_int (Int.repr 1) tint) (tptr tulong)))))))))
|}.

Definition f_make_Coq_Init_Datatypes_list_nil := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 1) tint)))
|}.

Definition f_make_Coq_Init_Datatypes_list_cons := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_arg0, tulong) :: (_arg1, tulong) ::
                (_argv, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
        (Econst_long (Int64.repr 0) tulong) (tptr tulong)) tulong)
    (Econst_long (Int64.repr 2048) tulong))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
          (Econst_long (Int64.repr 1) tulong) (tptr tulong)) tulong)
      (Etempvar _arg0 tulong))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
            (Econst_long (Int64.repr 2) tulong) (tptr tulong)) tulong)
        (Etempvar _arg1 tulong))
      (Sreturn (Some (Ebinop Oadd (Etempvar _argv (tptr tulong))
                       (Econst_long (Int64.repr 1) tulong) (tptr tulong)))))))
|}.

Definition f_alloc_make_Coq_Init_Datatypes_list_cons := {|
  fn_return := (tptr tulong);
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_arg0, tulong) :: (_arg1, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_argv, (tptr tulong)) :: (_t'3, (tptr tulong)) ::
               (_t'2, (tptr tulong)) :: (_t'1, (tptr tulong)) :: nil);
  fn_body :=
(Ssequence
  (Sset _argv
    (Efield
      (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _limit (tptr tulong)))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
        (Sifthenelse (Ebinop Olt
                       (Ebinop Osub (Etempvar _t'2 (tptr tulong))
                         (Etempvar _t'3 (tptr tulong)) tlong)
                       (Econst_int (Int.repr 4) tint) tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
            (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong)
        (Econst_int (Int.repr 2048) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
              (Econst_int (Int.repr 1) tint) (tptr tulong)) tulong)
          (Etempvar _arg0 tulong))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
                (Econst_int (Int.repr 2) tint) (tptr tulong)) tulong)
            (Etempvar _arg1 tulong))
          (Ssequence
            (Ssequence
              (Sset _t'1
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _alloc (tptr tulong))
                (Ebinop Oadd (Etempvar _t'1 (tptr tulong))
                  (Econst_int (Int.repr 3) tint) (tptr tulong))))
            (Sreturn (Some (Ebinop Oadd (Etempvar _argv (tptr tulong))
                             (Econst_int (Int.repr 1) tint) (tptr tulong))))))))))
|}.

Definition f_make_Coq_Init_Datatypes_bool_true := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 1) tint)))
|}.

Definition f_make_Coq_Init_Datatypes_bool_false := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 3) tint)))
|}.

Definition f_get_Coq_Init_Datatypes_nat_tag := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tbool) :: (_t, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _is_ptr (Tfunction (Tcons tulong Tnil) tbool cc_default))
      ((Etempvar _v tulong) :: nil))
    (Sset _b (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar _b tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_boxed_ordinal (Tfunction (Tcons tulong Tnil) tuint
                                     cc_default))
          ((Etempvar _v tulong) :: nil))
        (Sset _t (Etempvar _t'2 tuint)))
      (Sswitch (Etempvar _t tuint)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
          LSnil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_unboxed_ordinal (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
          ((Etempvar _v tulong) :: nil))
        (Sset _t (Etempvar _t'3 tuint)))
      (Sswitch (Etempvar _t tuint)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
          LSnil)))))
|}.

Definition f_get_Coq_Init_Datatypes_list_tag := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tbool) :: (_t, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _is_ptr (Tfunction (Tcons tulong Tnil) tbool cc_default))
      ((Etempvar _v tulong) :: nil))
    (Sset _b (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar _b tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_boxed_ordinal (Tfunction (Tcons tulong Tnil) tuint
                                     cc_default))
          ((Etempvar _v tulong) :: nil))
        (Sset _t (Etempvar _t'2 tuint)))
      (Sswitch (Etempvar _t tuint)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
          LSnil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_unboxed_ordinal (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
          ((Etempvar _v tulong) :: nil))
        (Sset _t (Etempvar _t'3 tuint)))
      (Sswitch (Etempvar _t tuint)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
          LSnil)))))
|}.

Definition f_get_Coq_Init_Datatypes_bool_tag := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_unboxed_ordinal (Tfunction (Tcons tulong Tnil) tuint
                                   cc_default))
      ((Etempvar _v tulong) :: nil))
    (Sset _t (Etempvar _t'1 tuint)))
  (Sreturn (Some (Etempvar _t tuint))))
|}.

Definition f_get_Coq_Init_Datatypes_O_args := {|
  fn_return := (tptr (Tstruct _Coq_Init_Datatypes_O_args noattr));
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                 (tptr (Tstruct _Coq_Init_Datatypes_O_args noattr)))))
|}.

Definition f_get_Coq_Init_Datatypes_S_args := {|
  fn_return := (tptr (Tstruct _Coq_Init_Datatypes_S_args noattr));
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _v tulong)
                 (tptr (Tstruct _Coq_Init_Datatypes_S_args noattr)))))
|}.

Definition f_get_Coq_Init_Datatypes_nil_args := {|
  fn_return := (tptr (Tstruct _Coq_Init_Datatypes_nil_args noattr));
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                 (tptr (Tstruct _Coq_Init_Datatypes_nil_args noattr)))))
|}.

Definition f_get_Coq_Init_Datatypes_cons_args := {|
  fn_return := (tptr (Tstruct _Coq_Init_Datatypes_cons_args noattr));
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _v tulong)
                 (tptr (Tstruct _Coq_Init_Datatypes_cons_args noattr)))))
|}.

Definition f_get_Coq_Init_Datatypes_true_args := {|
  fn_return := (tptr (Tstruct _Coq_Init_Datatypes_true_args noattr));
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                 (tptr (Tstruct _Coq_Init_Datatypes_true_args noattr)))))
|}.

Definition f_get_Coq_Init_Datatypes_false_args := {|
  fn_return := (tptr (Tstruct _Coq_Init_Datatypes_false_args noattr));
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                 (tptr (Tstruct _Coq_Init_Datatypes_false_args noattr)))))
|}.

Definition f_print_Coq_Init_Datatypes_nat := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_tag, tuint) :: (_args, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _Coq_Init_Datatypes_S_args noattr))) ::
               (_t'1, tuint) :: (_t'3, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_Coq_Init_Datatypes_nat_tag (Tfunction (Tcons tulong Tnil)
                                              tuint cc_default))
      ((Etempvar _v tulong) :: nil))
    (Sset _tag (Etempvar _t'1 tuint)))
  (Sswitch (Etempvar _tag tuint)
    (LScons (Some 0)
      (Ssequence
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          cc_default))
          ((Ederef
             (Ebinop Oadd
               (Evar _names_of_Coq_Init_Datatypes_nat (tarray (tarray tschar 2) 2))
               (Etempvar _tag tuint) (tptr (tarray tschar 2)))
             (tarray tschar 2)) :: nil))
        Sbreak)
      (LScons (Some 1)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _get_Coq_Init_Datatypes_S_args (Tfunction
                                                     (Tcons tulong Tnil)
                                                     (tptr (Tstruct _Coq_Init_Datatypes_S_args noattr))
                                                     cc_default))
              ((Etempvar _v tulong) :: nil))
            (Sset _args
              (Etempvar _t'2 (tptr (Tstruct _Coq_Init_Datatypes_S_args noattr)))))
          (Ssequence
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              cc_default))
              ((Evar _lparen_lit (tarray tschar 2)) :: nil))
            (Ssequence
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                cc_default))
                ((Ederef
                   (Ebinop Oadd
                     (Evar _names_of_Coq_Init_Datatypes_nat (tarray (tarray tschar 2) 2))
                     (Etempvar _tag tuint) (tptr (tarray tschar 2)))
                   (tarray tschar 2)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  cc_default))
                  ((Evar _space_lit (tarray tschar 2)) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Ederef
                        (Ebinop Oadd
                          (Ecast (Etempvar _args (tptr tvoid)) (tptr tulong))
                          (Econst_int (Int.repr 0) tint) (tptr tulong))
                        tulong))
                    (Scall None
                      (Evar _print_Coq_Init_Datatypes_nat (Tfunction
                                                            (Tcons tulong
                                                              Tnil) tvoid
                                                            cc_default))
                      ((Etempvar _t'3 tulong) :: nil)))
                  (Ssequence
                    (Scall None
                      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                      tint cc_default))
                      ((Evar _rparen_lit (tarray tschar 2)) :: nil))
                    Sbreak))))))
        LSnil))))
|}.

Definition f_print_Coq_Init_Datatypes_list := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) ::
                (_print_param_A,
                 (tptr (Tfunction (Tcons tulong Tnil) tvoid cc_default))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_tag, tuint) :: (_args, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _Coq_Init_Datatypes_cons_args noattr))) ::
               (_t'1, tuint) :: (_t'4, tulong) :: (_t'3, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_Coq_Init_Datatypes_list_tag (Tfunction (Tcons tulong Tnil)
                                               tuint cc_default))
      ((Etempvar _v tulong) :: nil))
    (Sset _tag (Etempvar _t'1 tuint)))
  (Sswitch (Etempvar _tag tuint)
    (LScons (Some 0)
      (Ssequence
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          cc_default))
          ((Ederef
             (Ebinop Oadd
               (Evar _names_of_Coq_Init_Datatypes_list (tarray (tarray tschar 5) 2))
               (Etempvar _tag tuint) (tptr (tarray tschar 5)))
             (tarray tschar 5)) :: nil))
        Sbreak)
      (LScons (Some 1)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _get_Coq_Init_Datatypes_cons_args (Tfunction
                                                        (Tcons tulong Tnil)
                                                        (tptr (Tstruct _Coq_Init_Datatypes_cons_args noattr))
                                                        cc_default))
              ((Etempvar _v tulong) :: nil))
            (Sset _args
              (Etempvar _t'2 (tptr (Tstruct _Coq_Init_Datatypes_cons_args noattr)))))
          (Ssequence
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              cc_default))
              ((Evar _lparen_lit (tarray tschar 2)) :: nil))
            (Ssequence
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                cc_default))
                ((Ederef
                   (Ebinop Oadd
                     (Evar _names_of_Coq_Init_Datatypes_list (tarray (tarray tschar 5) 2))
                     (Etempvar _tag tuint) (tptr (tarray tschar 5)))
                   (tarray tschar 5)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  cc_default))
                  ((Evar _space_lit (tarray tschar 2)) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _t'4
                      (Ederef
                        (Ebinop Oadd
                          (Ecast (Etempvar _args (tptr tvoid)) (tptr tulong))
                          (Econst_int (Int.repr 0) tint) (tptr tulong))
                        tulong))
                    (Scall None
                      (Etempvar _print_param_A (tptr (Tfunction
                                                       (Tcons tulong Tnil)
                                                       tvoid cc_default)))
                      ((Etempvar _t'4 tulong) :: nil)))
                  (Ssequence
                    (Scall None
                      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                      tint cc_default))
                      ((Evar _space_lit (tarray tschar 2)) :: nil))
                    (Ssequence
                      (Ssequence
                        (Sset _t'3
                          (Ederef
                            (Ebinop Oadd
                              (Ecast (Etempvar _args (tptr tvoid))
                                (tptr tulong)) (Econst_int (Int.repr 1) tint)
                              (tptr tulong)) tulong))
                        (Scall None
                          (Evar _print_Coq_Init_Datatypes_list (Tfunction
                                                                 (Tcons
                                                                   tulong
                                                                   (Tcons
                                                                    (tptr 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                                    Tnil))
                                                                 tvoid
                                                                 cc_default))
                          ((Etempvar _t'3 tulong) ::
                           (Etempvar _print_param_A (tptr (Tfunction
                                                            (Tcons tulong
                                                              Tnil) tvoid
                                                            cc_default))) ::
                           nil)))
                      (Ssequence
                        (Scall None
                          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                          tint cc_default))
                          ((Evar _rparen_lit (tarray tschar 2)) :: nil))
                        Sbreak))))))))
        LSnil))))
|}.

Definition f_print_Coq_Init_Datatypes_bool := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_tag, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_Coq_Init_Datatypes_bool_tag (Tfunction (Tcons tulong Tnil)
                                               tuint cc_default))
      ((Etempvar _v tulong) :: nil))
    (Sset _tag (Etempvar _t'1 tuint)))
  (Scall None
    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint cc_default))
    ((Ederef
       (Ebinop Oadd
         (Evar _names_of_Coq_Init_Datatypes_bool (tarray (tarray tschar 6) 2))
         (Etempvar _tag tuint) (tptr (tarray tschar 6))) (tarray tschar 6)) ::
     nil)))
|}.

Definition f_halt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_env, tulong) :: (_arg, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Ecast
          (Efield
            (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _args (tarray tulong 1024))
          (tptr tulong)) (Econst_long (Int64.repr 1) tulong) (tptr tulong))
      tulong) (Etempvar _arg tulong))
  (Sreturn None))
|}.

Definition v_halt_clo := {|
  gvar_info := (tarray (tptr tulong) 2);
  gvar_init := (Init_addrof _halt (Ptrofs.repr 0) ::
                Init_int64 (Int64.repr 1) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_call := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_clo, (tptr (tptr tulong))) :: (_arg, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_f, (tptr tulong)) :: (_envi, (tptr tulong)) ::
               (_ret, (tptr tulong)) :: nil);
  fn_body :=
(Ssequence
  (Sset _f
    (Ederef
      (Ebinop Oadd (Etempvar _clo (tptr (tptr tulong)))
        (Econst_int (Int.repr 0) tint) (tptr (tptr tulong))) (tptr tulong)))
  (Ssequence
    (Sset _envi
      (Ederef
        (Ebinop Oadd (Etempvar _clo (tptr (tptr tulong)))
          (Econst_int (Int.repr 1) tint) (tptr (tptr tulong))) (tptr tulong)))
    (Ssequence
      (Scall None
        (Ecast (Etempvar _f (tptr tulong))
          (tptr (Tfunction
                  (Tcons (tptr (Tstruct _thread_info noattr))
                    (Tcons (tptr tulong)
                      (Tcons (tptr tulong) (Tcons tulong Tnil)))) tvoid
                  cc_default)))
        ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
         (Etempvar _envi (tptr tulong)) ::
         (Ecast (Evar _halt_clo (tarray (tptr tulong) 2)) (tptr tulong)) ::
         (Etempvar _arg tulong) :: nil))
      (Ssequence
        (Sset _ret
          (Ederef
            (Ebinop Oadd
              (Ecast
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _args
                  (tarray tulong 1024)) (tptr tulong))
              (Econst_int (Int.repr 1) tint) (tptr tulong)) tulong))
        (Sreturn (Some (Etempvar _ret (tptr tulong))))))))
|}.

Definition composites : list composite_definition :=
(Composite _thread_info Struct
   ((_alloc, (tptr tulong)) :: (_limit, (tptr tulong)) ::
    (_heap, (tptr (Tstruct _heap noattr))) ::
    (_args, (tarray tulong 1024)) :: nil)
   noattr :: Composite _Coq_Init_Datatypes_O_args Struct nil noattr ::
 Composite _Coq_Init_Datatypes_S_args Struct
   ((_Coq_Init_Datatypes_S_arg_0, tulong) :: nil)
   noattr :: Composite _Coq_Init_Datatypes_nil_args Struct nil noattr ::
 Composite _Coq_Init_Datatypes_cons_args Struct
   ((_Coq_Init_Datatypes_cons_arg_0, tulong) ::
    (_Coq_Init_Datatypes_cons_arg_1, tulong) :: nil)
   noattr :: Composite _Coq_Init_Datatypes_true_args Struct nil noattr ::
 Composite _Coq_Init_Datatypes_false_args Struct nil noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
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
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
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
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_lparen_lit, Gvar v_lparen_lit) :: (_rparen_lit, Gvar v_rparen_lit) ::
 (_space_lit, Gvar v_space_lit) :: (_fun_lit, Gvar v_fun_lit) ::
 (_type_lit, Gvar v_type_lit) :: (_unk_lit, Gvar v_unk_lit) ::
 (_prop_lit, Gvar v_prop_lit) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tschar) Tnil) tint cc_default)) ::
 (_is_ptr,
   Gfun(External (EF_external "is_ptr"
                   (mksignature (AST.Tlong :: nil) AST.Tint8unsigned
                     cc_default)) (Tcons tulong Tnil) tbool cc_default)) ::
 (_get_unboxed_ordinal, Gfun(Internal f_get_unboxed_ordinal)) ::
 (_get_boxed_ordinal, Gfun(Internal f_get_boxed_ordinal)) ::
 (_names_of_Coq_Init_Datatypes_nat, Gvar v_names_of_Coq_Init_Datatypes_nat) ::
 (_names_of_Coq_Init_Datatypes_list, Gvar v_names_of_Coq_Init_Datatypes_list) ::
 (_names_of_Coq_Init_Datatypes_bool, Gvar v_names_of_Coq_Init_Datatypes_bool) ::
 (_make_Coq_Init_Datatypes_nat_O, Gfun(Internal f_make_Coq_Init_Datatypes_nat_O)) ::
 (_make_Coq_Init_Datatypes_nat_S, Gfun(Internal f_make_Coq_Init_Datatypes_nat_S)) ::
 (_alloc_make_Coq_Init_Datatypes_nat_S, Gfun(Internal f_alloc_make_Coq_Init_Datatypes_nat_S)) ::
 (_make_Coq_Init_Datatypes_list_nil, Gfun(Internal f_make_Coq_Init_Datatypes_list_nil)) ::
 (_make_Coq_Init_Datatypes_list_cons, Gfun(Internal f_make_Coq_Init_Datatypes_list_cons)) ::
 (_alloc_make_Coq_Init_Datatypes_list_cons, Gfun(Internal f_alloc_make_Coq_Init_Datatypes_list_cons)) ::
 (_make_Coq_Init_Datatypes_bool_true, Gfun(Internal f_make_Coq_Init_Datatypes_bool_true)) ::
 (_make_Coq_Init_Datatypes_bool_false, Gfun(Internal f_make_Coq_Init_Datatypes_bool_false)) ::
 (_get_Coq_Init_Datatypes_nat_tag, Gfun(Internal f_get_Coq_Init_Datatypes_nat_tag)) ::
 (_get_Coq_Init_Datatypes_list_tag, Gfun(Internal f_get_Coq_Init_Datatypes_list_tag)) ::
 (_get_Coq_Init_Datatypes_bool_tag, Gfun(Internal f_get_Coq_Init_Datatypes_bool_tag)) ::
 (_get_Coq_Init_Datatypes_O_args, Gfun(Internal f_get_Coq_Init_Datatypes_O_args)) ::
 (_get_Coq_Init_Datatypes_S_args, Gfun(Internal f_get_Coq_Init_Datatypes_S_args)) ::
 (_get_Coq_Init_Datatypes_nil_args, Gfun(Internal f_get_Coq_Init_Datatypes_nil_args)) ::
 (_get_Coq_Init_Datatypes_cons_args, Gfun(Internal f_get_Coq_Init_Datatypes_cons_args)) ::
 (_get_Coq_Init_Datatypes_true_args, Gfun(Internal f_get_Coq_Init_Datatypes_true_args)) ::
 (_get_Coq_Init_Datatypes_false_args, Gfun(Internal f_get_Coq_Init_Datatypes_false_args)) ::
 (_print_Coq_Init_Datatypes_nat, Gfun(Internal f_print_Coq_Init_Datatypes_nat)) ::
 (_print_Coq_Init_Datatypes_list, Gfun(Internal f_print_Coq_Init_Datatypes_list)) ::
 (_print_Coq_Init_Datatypes_bool, Gfun(Internal f_print_Coq_Init_Datatypes_bool)) ::
 (_halt, Gfun(Internal f_halt)) :: (_halt_clo, Gvar v_halt_clo) ::
 (_call, Gfun(Internal f_call)) :: nil).

Definition public_idents : list ident :=
(_call :: _halt_clo :: _halt :: _print_Coq_Init_Datatypes_bool ::
 _print_Coq_Init_Datatypes_list :: _print_Coq_Init_Datatypes_nat ::
 _get_Coq_Init_Datatypes_false_args :: _get_Coq_Init_Datatypes_true_args ::
 _get_Coq_Init_Datatypes_cons_args :: _get_Coq_Init_Datatypes_nil_args ::
 _get_Coq_Init_Datatypes_S_args :: _get_Coq_Init_Datatypes_O_args ::
 _get_Coq_Init_Datatypes_bool_tag :: _get_Coq_Init_Datatypes_list_tag ::
 _get_Coq_Init_Datatypes_nat_tag :: _make_Coq_Init_Datatypes_bool_false ::
 _make_Coq_Init_Datatypes_bool_true ::
 _alloc_make_Coq_Init_Datatypes_list_cons ::
 _make_Coq_Init_Datatypes_list_cons :: _make_Coq_Init_Datatypes_list_nil ::
 _alloc_make_Coq_Init_Datatypes_nat_S :: _make_Coq_Init_Datatypes_nat_S ::
 _make_Coq_Init_Datatypes_nat_O :: _names_of_Coq_Init_Datatypes_bool ::
 _names_of_Coq_Init_Datatypes_list :: _names_of_Coq_Init_Datatypes_nat ::
 _get_boxed_ordinal :: _get_unboxed_ordinal :: _is_ptr :: _printf ::
 _prop_lit :: _unk_lit :: _type_lit :: _fun_lit :: _space_lit ::
 _rparen_lit :: _lparen_lit :: _exit :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___builtin_expect :: ___builtin_unreachable :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


