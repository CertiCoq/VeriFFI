From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.11".
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

Definition __arg : ident := $"$arg".
Definition __arg0 : ident := $"$arg0".
Definition __arg1 : ident := $"$arg1".
Definition __args : ident := $"$args".
Definition __argv : ident := $"$argv".
Definition __b : ident := $"$b".
Definition __clo : ident := $"$clo".
Definition __env : ident := $"$env".
Definition __envi : ident := $"$envi".
Definition __f : ident := $"$f".
Definition __print_param_n : ident := $"$print_param_n".
Definition __t : ident := $"$t".
Definition __tag : ident := $"$tag".
Definition __tinfo : ident := $"$tinfo".
Definition __v : ident := $"$v".
Definition _Coq_Init_Datatypes_O_args : ident := $"Coq_Init_Datatypes_O_args".
Definition _Coq_Init_Datatypes_S_arg_0 : ident := $"Coq_Init_Datatypes_S_arg_0".
Definition _Coq_Init_Datatypes_S_args : ident := $"Coq_Init_Datatypes_S_args".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
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
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
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
Definition _alloc : ident := $"alloc".
Definition _alloc_make_Coq_Init_Datatypes_nat_S : ident := $"alloc_make_Coq_Init_Datatypes_nat_S".
Definition _alloc_make_prog_le_le_S : ident := $"alloc_make_prog_le_le_S".
Definition _args : ident := $"args".
Definition _call : ident := $"call".
Definition _fun_lit : ident := $"fun_lit".
Definition _get_Coq_Init_Datatypes_O_args : ident := $"get_Coq_Init_Datatypes_O_args".
Definition _get_Coq_Init_Datatypes_S_args : ident := $"get_Coq_Init_Datatypes_S_args".
Definition _get_Coq_Init_Datatypes_nat_tag : ident := $"get_Coq_Init_Datatypes_nat_tag".
Definition _get_boxed_ordinal : ident := $"get_boxed_ordinal".
Definition _get_prog_le_S_args : ident := $"get_prog_le_S_args".
Definition _get_prog_le_n_args : ident := $"get_prog_le_n_args".
Definition _get_prog_le_tag : ident := $"get_prog_le_tag".
Definition _get_unboxed_ordinal : ident := $"get_unboxed_ordinal".
Definition _halt : ident := $"halt".
Definition _halt_clo : ident := $"halt_clo".
Definition _heap : ident := $"heap".
Definition _is_ptr : ident := $"is_ptr".
Definition _limit : ident := $"limit".
Definition _lparen_lit : ident := $"lparen_lit".
Definition _main : ident := $"main".
Definition _make_Coq_Init_Datatypes_nat_O : ident := $"make_Coq_Init_Datatypes_nat_O".
Definition _make_Coq_Init_Datatypes_nat_S : ident := $"make_Coq_Init_Datatypes_nat_S".
Definition _make_prog_le_le_S : ident := $"make_prog_le_le_S".
Definition _make_prog_le_le_n : ident := $"make_prog_le_le_n".
Definition _names_of_Coq_Init_Datatypes_nat : ident := $"names_of_Coq_Init_Datatypes_nat".
Definition _names_of_prog_le : ident := $"names_of_prog_le".
Definition _print_Coq_Init_Datatypes_nat : ident := $"print_Coq_Init_Datatypes_nat".
Definition _print_prog_le : ident := $"print_prog_le".
Definition _printf : ident := $"printf".
Definition _prog_le_S_arg_0 : ident := $"prog_le_S_arg_0".
Definition _prog_le_S_arg_1 : ident := $"prog_le_S_arg_1".
Definition _prog_le_S_args : ident := $"prog_le_S_args".
Definition _prog_le_n_args : ident := $"prog_le_n_args".
Definition _prop_lit : ident := $"prop_lit".
Definition _rparen_lit : ident := $"rparen_lit".
Definition _space_lit : ident := $"space_lit".
Definition _thread_info : ident := $"thread_info".
Definition _type_lit : ident := $"type_lit".
Definition _unk_lit : ident := $"unk_lit".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.

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
  fn_params := ((__v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oshr (Etempvar __v tulong)
                 (Econst_long (Int64.repr 1) tulong) tulong)))
|}.

Definition f_get_boxed_ordinal := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((__v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd (Ecast (Etempvar __v tulong) (tptr tulong))
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

Definition v_names_of_prog_le := {|
  gvar_info := (tarray (tarray tschar 5) 2);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 0) :: nil);
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
  fn_params := ((__arg0, tulong) :: (__argv, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Ecast (Etempvar __argv (tptr tulong)) (tptr tulong))
        (Econst_long (Int64.repr 0) tulong) (tptr tulong)) tulong)
    (Econst_long (Int64.repr 1024) tulong))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar __argv (tptr tulong)) (tptr tulong))
          (Econst_long (Int64.repr 1) tulong) (tptr tulong)) tulong)
      (Etempvar __arg0 tulong))
    (Sreturn (Some (Ebinop Oadd (Etempvar __argv (tptr tulong))
                     (Econst_long (Int64.repr 1) tulong) (tptr tulong))))))
|}.

Definition f_alloc_make_Coq_Init_Datatypes_nat_S := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((__tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__arg0, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((__argv, (tptr tulong)) :: (_t'1, (tptr tulong)) :: nil);
  fn_body :=
(Ssequence
  (Sset __argv
    (Efield
      (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar __argv (tptr tulong)) (tptr tulong))
          (Econst_long (Int64.repr 0) tulong) (tptr tulong)) tulong)
      (Econst_long (Int64.repr 1024) tulong))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar __argv (tptr tulong)) (tptr tulong))
            (Econst_long (Int64.repr 1) tulong) (tptr tulong)) tulong)
        (Etempvar __arg0 tulong))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
          (Sassign
            (Efield
              (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc (tptr tulong))
            (Ebinop Oadd (Etempvar _t'1 (tptr tulong))
              (Econst_long (Int64.repr 2) tulong) (tptr tulong))))
        (Sreturn (Some (Ebinop Oadd (Etempvar __argv (tptr tulong))
                         (Econst_long (Int64.repr 1) tulong) (tptr tulong))))))))
|}.

Definition f_make_prog_le_le_n := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 1) tint)))
|}.

Definition f_make_prog_le_le_S := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((__arg0, tulong) :: (__arg1, tulong) ::
                (__argv, (tptr tulong)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Ecast (Etempvar __argv (tptr tulong)) (tptr tulong))
        (Econst_long (Int64.repr 0) tulong) (tptr tulong)) tulong)
    (Econst_long (Int64.repr 2048) tulong))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar __argv (tptr tulong)) (tptr tulong))
          (Econst_long (Int64.repr 1) tulong) (tptr tulong)) tulong)
      (Etempvar __arg0 tulong))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar __argv (tptr tulong)) (tptr tulong))
            (Econst_long (Int64.repr 2) tulong) (tptr tulong)) tulong)
        (Etempvar __arg1 tulong))
      (Sreturn (Some (Ebinop Oadd (Etempvar __argv (tptr tulong))
                       (Econst_long (Int64.repr 1) tulong) (tptr tulong)))))))
|}.

Definition f_alloc_make_prog_le_le_S := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((__tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__arg0, tulong) :: (__arg1, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((__argv, (tptr tulong)) :: (_t'1, (tptr tulong)) :: nil);
  fn_body :=
(Ssequence
  (Sset __argv
    (Efield
      (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar __argv (tptr tulong)) (tptr tulong))
          (Econst_long (Int64.repr 0) tulong) (tptr tulong)) tulong)
      (Econst_long (Int64.repr 2048) tulong))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar __argv (tptr tulong)) (tptr tulong))
            (Econst_long (Int64.repr 1) tulong) (tptr tulong)) tulong)
        (Etempvar __arg0 tulong))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Ecast (Etempvar __argv (tptr tulong)) (tptr tulong))
              (Econst_long (Int64.repr 2) tulong) (tptr tulong)) tulong)
          (Etempvar __arg1 tulong))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef
                  (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc (tptr tulong))
              (Ebinop Oadd (Etempvar _t'1 (tptr tulong))
                (Econst_long (Int64.repr 3) tulong) (tptr tulong))))
          (Sreturn (Some (Ebinop Oadd (Etempvar __argv (tptr tulong))
                           (Econst_long (Int64.repr 1) tulong) (tptr tulong)))))))))
|}.

Definition f_get_Coq_Init_Datatypes_nat_tag := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((__v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((__b, tbool) :: (__t, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _is_ptr (Tfunction (Tcons tulong Tnil) tbool cc_default))
      ((Etempvar __v tulong) :: nil))
    (Sset __b (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar __b tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_boxed_ordinal (Tfunction (Tcons tulong Tnil) tuint
                                     cc_default))
          ((Etempvar __v tulong) :: nil))
        (Sset __t (Etempvar _t'2 tuint)))
      (Sswitch (Etempvar __t tuint)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
          LSnil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_unboxed_ordinal (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
          ((Etempvar __v tulong) :: nil))
        (Sset __t (Etempvar _t'3 tuint)))
      (Sswitch (Etempvar __t tuint)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
          LSnil)))))
|}.

Definition f_get_prog_le_tag := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((__v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((__b, tbool) :: (__t, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _is_ptr (Tfunction (Tcons tulong Tnil) tbool cc_default))
      ((Etempvar __v tulong) :: nil))
    (Sset __b (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar __b tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_boxed_ordinal (Tfunction (Tcons tulong Tnil) tuint
                                     cc_default))
          ((Etempvar __v tulong) :: nil))
        (Sset __t (Etempvar _t'2 tuint)))
      (Sswitch (Etempvar __t tuint)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
          LSnil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_unboxed_ordinal (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
          ((Etempvar __v tulong) :: nil))
        (Sset __t (Etempvar _t'3 tuint)))
      (Sswitch (Etempvar __t tuint)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
          LSnil)))))
|}.

Definition f_get_Coq_Init_Datatypes_O_args := {|
  fn_return := (tptr (Tstruct _Coq_Init_Datatypes_O_args noattr));
  fn_callconv := cc_default;
  fn_params := ((__v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                 (tptr (Tstruct _Coq_Init_Datatypes_O_args noattr)))))
|}.

Definition f_get_Coq_Init_Datatypes_S_args := {|
  fn_return := (tptr (Tstruct _Coq_Init_Datatypes_S_args noattr));
  fn_callconv := cc_default;
  fn_params := ((__v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar __v tulong)
                 (tptr (Tstruct _Coq_Init_Datatypes_S_args noattr)))))
|}.

Definition f_get_prog_le_n_args := {|
  fn_return := (tptr (Tstruct _prog_le_n_args noattr));
  fn_callconv := cc_default;
  fn_params := ((__v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                 (tptr (Tstruct _prog_le_n_args noattr)))))
|}.

Definition f_get_prog_le_S_args := {|
  fn_return := (tptr (Tstruct _prog_le_S_args noattr));
  fn_callconv := cc_default;
  fn_params := ((__v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar __v tulong)
                 (tptr (Tstruct _prog_le_S_args noattr)))))
|}.

Definition f_print_Coq_Init_Datatypes_nat := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((__v, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((__tag, tuint) :: (__args, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _Coq_Init_Datatypes_S_args noattr))) ::
               (_t'1, tuint) :: (_t'3, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_Coq_Init_Datatypes_nat_tag (Tfunction (Tcons tulong Tnil)
                                              tuint cc_default))
      ((Etempvar __v tulong) :: nil))
    (Sset __tag (Etempvar _t'1 tuint)))
  (Sswitch (Etempvar __tag tuint)
    (LScons (Some 0)
      (Ssequence
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          cc_default))
          ((Ederef
             (Ebinop Oadd
               (Evar _names_of_Coq_Init_Datatypes_nat (tarray (tarray tschar 2) 2))
               (Etempvar __tag tuint) (tptr (tarray tschar 2)))
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
              ((Etempvar __v tulong) :: nil))
            (Sset __args
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
                     (Etempvar __tag tuint) (tptr (tarray tschar 2)))
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
                          (Ecast (Etempvar __args (tptr tvoid))
                            (tptr tulong)) (Econst_int (Int.repr 0) tint)
                          (tptr tulong)) tulong))
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

Definition f_print_prog_le := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((__v, tulong) ::
                (__print_param_n,
                 (tptr (Tfunction (Tcons tulong Tnil) tvoid cc_default))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((__tag, tuint) :: (__args, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _prog_le_S_args noattr))) ::
               (_t'1, tuint) :: (_t'4, tulong) :: (_t'3, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_prog_le_tag (Tfunction (Tcons tulong Tnil) tuint cc_default))
      ((Etempvar __v tulong) :: nil))
    (Sset __tag (Etempvar _t'1 tuint)))
  (Sswitch (Etempvar __tag tuint)
    (LScons (Some 0)
      (Ssequence
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          cc_default))
          ((Ederef
             (Ebinop Oadd
               (Evar _names_of_prog_le (tarray (tarray tschar 5) 2))
               (Etempvar __tag tuint) (tptr (tarray tschar 5)))
             (tarray tschar 5)) :: nil))
        Sbreak)
      (LScons (Some 1)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _get_prog_le_S_args (Tfunction (Tcons tulong Tnil)
                                          (tptr (Tstruct _prog_le_S_args noattr))
                                          cc_default))
              ((Etempvar __v tulong) :: nil))
            (Sset __args
              (Etempvar _t'2 (tptr (Tstruct _prog_le_S_args noattr)))))
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
                     (Evar _names_of_prog_le (tarray (tarray tschar 5) 2))
                     (Etempvar __tag tuint) (tptr (tarray tschar 5)))
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
                          (Ecast (Etempvar __args (tptr tvoid))
                            (tptr tulong)) (Econst_int (Int.repr 0) tint)
                          (tptr tulong)) tulong))
                    (Scall None
                      (Evar _print_Coq_Init_Datatypes_nat (Tfunction
                                                            (Tcons tulong
                                                              Tnil) tvoid
                                                            cc_default))
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
                              (Ecast (Etempvar __args (tptr tvoid))
                                (tptr tulong)) (Econst_int (Int.repr 1) tint)
                              (tptr tulong)) tulong))
                        (Scall None
                          (Evar _print_prog_le (Tfunction
                                                 (Tcons tulong
                                                   (Tcons
                                                     (tptr (Tfunction
                                                             (Tcons tulong
                                                               Tnil) tvoid
                                                             cc_default))
                                                     Tnil)) tvoid cc_default))
                          ((Etempvar _t'3 tulong) ::
                           (Etempvar __print_param_n (tptr (Tfunction
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

Definition f_halt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((__tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__env, tulong) :: (__arg, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Ecast
          (Efield
            (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _args (tarray tulong 1024))
          (tptr tulong)) (Econst_long (Int64.repr 1) tulong) (tptr tulong))
      tulong) (Etempvar __arg tulong))
  (Sreturn None))
|}.

Definition v_halt_clo := {|
  gvar_info := (tarray tulong 2);
  gvar_init := (Init_addrof _halt (Ptrofs.repr 0) ::
                Init_int64 (Int64.repr 1) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_call := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((__tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__clo, tulong) :: (__arg, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((__f, (tptr tulong)) :: (__envi, (tptr tulong)) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset __f
    (Ederef
      (Ebinop Oadd (Ecast (Etempvar __clo tulong) (tptr tulong))
        (Econst_long (Int64.repr 0) tulong) (tptr tulong)) tulong))
  (Ssequence
    (Sset __envi
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar __clo tulong) (tptr tulong))
          (Econst_long (Int64.repr 1) tulong) (tptr tulong)) tulong))
    (Ssequence
      (Scall None
        (Ecast (Etempvar __f (tptr tulong))
          (tptr (Tfunction
                  (Tcons (tptr (Tstruct _thread_info noattr))
                    (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid
                  cc_default)))
        ((Etempvar __tinfo (tptr (Tstruct _thread_info noattr))) ::
         (Etempvar __envi (tptr tulong)) ::
         (Evar _halt_clo (tarray tulong 2)) :: (Etempvar __arg tulong) ::
         nil))
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd
              (Ecast
                (Efield
                  (Ederef
                    (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _args
                  (tarray tulong 1024)) (tptr tulong))
              (Econst_long (Int64.repr 1) tulong) (tptr tulong)) tulong))
        (Sreturn (Some (Etempvar _t'1 tulong)))))))
|}.

Definition composites : list composite_definition :=
(Composite _thread_info Struct
   (Member_plain _alloc (tptr tulong) :: Member_plain _limit (tptr tulong) ::
    Member_plain _heap (tptr (Tstruct _heap noattr)) ::
    Member_plain _args (tarray tulong 1024) :: nil)
   noattr :: Composite _Coq_Init_Datatypes_O_args Struct nil noattr ::
 Composite _Coq_Init_Datatypes_S_args Struct
   (Member_plain _Coq_Init_Datatypes_S_arg_0 tulong :: nil)
   noattr :: Composite _prog_le_n_args Struct nil noattr ::
 Composite _prog_le_S_args Struct
   (Member_plain _prog_le_S_arg_0 tulong ::
    Member_plain _prog_le_S_arg_1 tulong :: nil)
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
     cc_default)) ::
 (___builtin_ais_annot,
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
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
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
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tschar) Tnil) tint cc_default)) ::
 (_is_ptr,
   Gfun(External (EF_external "is_ptr"
                   (mksignature (AST.Tlong :: nil) AST.Tint8unsigned
                     cc_default)) (Tcons tulong Tnil) tbool cc_default)) ::
 (_lparen_lit, Gvar v_lparen_lit) :: (_rparen_lit, Gvar v_rparen_lit) ::
 (_space_lit, Gvar v_space_lit) :: (_fun_lit, Gvar v_fun_lit) ::
 (_type_lit, Gvar v_type_lit) :: (_unk_lit, Gvar v_unk_lit) ::
 (_prop_lit, Gvar v_prop_lit) ::
 (_get_unboxed_ordinal, Gfun(Internal f_get_unboxed_ordinal)) ::
 (_get_boxed_ordinal, Gfun(Internal f_get_boxed_ordinal)) ::
 (_names_of_Coq_Init_Datatypes_nat, Gvar v_names_of_Coq_Init_Datatypes_nat) ::
 (_names_of_prog_le, Gvar v_names_of_prog_le) ::
 (_make_Coq_Init_Datatypes_nat_O, Gfun(Internal f_make_Coq_Init_Datatypes_nat_O)) ::
 (_make_Coq_Init_Datatypes_nat_S, Gfun(Internal f_make_Coq_Init_Datatypes_nat_S)) ::
 (_alloc_make_Coq_Init_Datatypes_nat_S, Gfun(Internal f_alloc_make_Coq_Init_Datatypes_nat_S)) ::
 (_make_prog_le_le_n, Gfun(Internal f_make_prog_le_le_n)) ::
 (_make_prog_le_le_S, Gfun(Internal f_make_prog_le_le_S)) ::
 (_alloc_make_prog_le_le_S, Gfun(Internal f_alloc_make_prog_le_le_S)) ::
 (_get_Coq_Init_Datatypes_nat_tag, Gfun(Internal f_get_Coq_Init_Datatypes_nat_tag)) ::
 (_get_prog_le_tag, Gfun(Internal f_get_prog_le_tag)) ::
 (_get_Coq_Init_Datatypes_O_args, Gfun(Internal f_get_Coq_Init_Datatypes_O_args)) ::
 (_get_Coq_Init_Datatypes_S_args, Gfun(Internal f_get_Coq_Init_Datatypes_S_args)) ::
 (_get_prog_le_n_args, Gfun(Internal f_get_prog_le_n_args)) ::
 (_get_prog_le_S_args, Gfun(Internal f_get_prog_le_S_args)) ::
 (_print_Coq_Init_Datatypes_nat, Gfun(Internal f_print_Coq_Init_Datatypes_nat)) ::
 (_print_prog_le, Gfun(Internal f_print_prog_le)) ::
 (_halt, Gfun(Internal f_halt)) :: (_halt_clo, Gvar v_halt_clo) ::
 (_call, Gfun(Internal f_call)) :: nil).

Definition public_idents : list ident :=
(_call :: _halt_clo :: _halt :: _print_prog_le ::
 _print_Coq_Init_Datatypes_nat :: _get_prog_le_S_args ::
 _get_prog_le_n_args :: _get_Coq_Init_Datatypes_S_args ::
 _get_Coq_Init_Datatypes_O_args :: _get_prog_le_tag ::
 _get_Coq_Init_Datatypes_nat_tag :: _alloc_make_prog_le_le_S ::
 _make_prog_le_le_S :: _make_prog_le_le_n ::
 _alloc_make_Coq_Init_Datatypes_nat_S :: _make_Coq_Init_Datatypes_nat_S ::
 _make_Coq_Init_Datatypes_nat_O :: _names_of_prog_le ::
 _names_of_Coq_Init_Datatypes_nat :: _get_boxed_ordinal ::
 _get_unboxed_ordinal :: _prop_lit :: _unk_lit :: _type_lit :: _fun_lit ::
 _space_lit :: _rparen_lit :: _lparen_lit :: _is_ptr :: _printf ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


