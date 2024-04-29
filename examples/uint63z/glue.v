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
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "examples/uint63z/glue.c".
  Definition normalized := true.
End Info.

Definition __arg : ident := $"$arg".
Definition __arg0 : ident := $"$arg0".
Definition __args : ident := $"$args".
Definition __argv : ident := $"$argv".
Definition __b : ident := $"$b".
Definition __clo : ident := $"$clo".
Definition __envi : ident := $"$envi".
Definition __f : ident := $"$f".
Definition __t : ident := $"$t".
Definition __tag : ident := $"$tag".
Definition __tinfo : ident := $"$tinfo".
Definition __tmp : ident := $"$tmp".
Definition __v : ident := $"$v".
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
Definition _alloc_make_Coq_Numbers_BinNums_Z_Zneg : ident := $"alloc_make_Coq_Numbers_BinNums_Z_Zneg".
Definition _alloc_make_Coq_Numbers_BinNums_Z_Zpos : ident := $"alloc_make_Coq_Numbers_BinNums_Z_Zpos".
Definition _alloc_make_Coq_Numbers_BinNums_positive_xI : ident := $"alloc_make_Coq_Numbers_BinNums_positive_xI".
Definition _alloc_make_Coq_Numbers_BinNums_positive_xO : ident := $"alloc_make_Coq_Numbers_BinNums_positive_xO".
Definition _args : ident := $"args".
Definition _call : ident := $"call".
Definition _closure : ident := $"closure".
Definition _env : ident := $"env".
Definition _fp : ident := $"fp".
Definition _fun_lit : ident := $"fun_lit".
Definition _func : ident := $"func".
Definition _get_Coq_Numbers_BinNums_Z_tag : ident := $"get_Coq_Numbers_BinNums_Z_tag".
Definition _get_Coq_Numbers_BinNums_positive_tag : ident := $"get_Coq_Numbers_BinNums_positive_tag".
Definition _get_args : ident := $"get_args".
Definition _get_boxed_ordinal : ident := $"get_boxed_ordinal".
Definition _get_unboxed_ordinal : ident := $"get_unboxed_ordinal".
Definition _heap : ident := $"heap".
Definition _is_ptr : ident := $"is_ptr".
Definition _limit : ident := $"limit".
Definition _lparen_lit : ident := $"lparen_lit".
Definition _main : ident := $"main".
Definition _make_Coq_Numbers_BinNums_Z_Z0 : ident := $"make_Coq_Numbers_BinNums_Z_Z0".
Definition _make_Coq_Numbers_BinNums_Z_Zneg : ident := $"make_Coq_Numbers_BinNums_Z_Zneg".
Definition _make_Coq_Numbers_BinNums_Z_Zpos : ident := $"make_Coq_Numbers_BinNums_Z_Zpos".
Definition _make_Coq_Numbers_BinNums_positive_xH : ident := $"make_Coq_Numbers_BinNums_positive_xH".
Definition _make_Coq_Numbers_BinNums_positive_xI : ident := $"make_Coq_Numbers_BinNums_positive_xI".
Definition _make_Coq_Numbers_BinNums_positive_xO : ident := $"make_Coq_Numbers_BinNums_positive_xO".
Definition _nalloc : ident := $"nalloc".
Definition _names_of_Coq_Numbers_BinNums_Z : ident := $"names_of_Coq_Numbers_BinNums_Z".
Definition _names_of_Coq_Numbers_BinNums_positive : ident := $"names_of_Coq_Numbers_BinNums_positive".
Definition _next : ident := $"next".
Definition _odata : ident := $"odata".
Definition _prev : ident := $"prev".
Definition _print_Coq_Numbers_BinNums_Z : ident := $"print_Coq_Numbers_BinNums_Z".
Definition _print_Coq_Numbers_BinNums_positive : ident := $"print_Coq_Numbers_BinNums_positive".
Definition _printf : ident := $"printf".
Definition _prop_lit : ident := $"prop_lit".
Definition _rem_limit : ident := $"rem_limit".
Definition _root : ident := $"root".
Definition _rparen_lit : ident := $"rparen_lit".
Definition _space : ident := $"space".
Definition _space_lit : ident := $"space_lit".
Definition _spaces : ident := $"spaces".
Definition _stack_frame : ident := $"stack_frame".
Definition _start : ident := $"start".
Definition _thread_info : ident := $"thread_info".
Definition _type_lit : ident := $"type_lit".
Definition _unk_lit : ident := $"unk_lit".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.

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
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((__v, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oshr
                 (Ecast (Etempvar __v (talignas 3%N (tptr tvoid))) tulong)
                 (Econst_long (Int64.repr 1) tlong) tulong)))
|}.

Definition f_get_boxed_ordinal := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((__v, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd
        (Ecast (Etempvar __v (talignas 3%N (tptr tvoid))) (tptr tulong))
        (Eunop Oneg (Econst_long (Int64.repr 1) tlong) tlong) (tptr tulong))
      tulong))
  (Sreturn (Some (Ebinop Oand (Ecast (Etempvar _t'1 tulong) tulong)
                   (Econst_long (Int64.repr 255) tlong) tulong))))
|}.

Definition f_get_args := {|
  fn_return := (tptr (talignas 3%N (tptr tvoid)));
  fn_callconv := cc_default;
  fn_params := ((__v, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar __v (talignas 3%N (tptr tvoid)))
                 (tptr (talignas 3%N (tptr tvoid))))))
|}.

Definition v_names_of_Coq_Numbers_BinNums_positive := {|
  gvar_info := (tarray (tarray tschar 3) 3);
  gvar_init := (Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 72) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_names_of_Coq_Numbers_BinNums_Z := {|
  gvar_info := (tarray (tarray tschar 5) 3);
  gvar_init := (Init_int8 (Int.repr 90) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 90) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 90) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_make_Coq_Numbers_BinNums_positive_xI := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((__arg0, (talignas 3%N (tptr tvoid))) ::
                (__argv, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
        (Econst_long (Int64.repr 0) tlong)
        (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
    (Ecast (Econst_long (Int64.repr 1024) tlong) (talignas 3%N (tptr tvoid))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
          (Econst_long (Int64.repr 1) tlong)
          (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
      (Etempvar __arg0 (talignas 3%N (tptr tvoid))))
    (Sreturn (Some (Ebinop Oadd
                     (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
                     (Econst_long (Int64.repr 1) tlong)
                     (tptr (talignas 3%N (tptr tvoid))))))))
|}.

Definition f_alloc_make_Coq_Numbers_BinNums_positive_xI := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((__tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__arg0, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((__argv, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset __argv
    (Efield
      (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc
      (tptr (talignas 3%N (tptr tvoid)))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
          (Econst_long (Int64.repr 0) tlong)
          (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
      (Econst_long (Int64.repr 1024) tlong))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
            (Econst_long (Int64.repr 1) tlong)
            (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
        (Etempvar __arg0 (talignas 3%N (tptr tvoid))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc
              (tptr (talignas 3%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc
              (tptr (talignas 3%N (tptr tvoid))))
            (Ebinop Oadd (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))
              (Econst_long (Int64.repr 2) tlong)
              (tptr (talignas 3%N (tptr tvoid))))))
        (Sreturn (Some (Ebinop Oadd
                         (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
                         (Econst_long (Int64.repr 1) tlong)
                         (tptr (talignas 3%N (tptr tvoid))))))))))
|}.

Definition f_make_Coq_Numbers_BinNums_positive_xO := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((__arg0, (talignas 3%N (tptr tvoid))) ::
                (__argv, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
        (Econst_long (Int64.repr 0) tlong)
        (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
    (Ecast (Econst_long (Int64.repr 1025) tlong) (talignas 3%N (tptr tvoid))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
          (Econst_long (Int64.repr 1) tlong)
          (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
      (Etempvar __arg0 (talignas 3%N (tptr tvoid))))
    (Sreturn (Some (Ebinop Oadd
                     (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
                     (Econst_long (Int64.repr 1) tlong)
                     (tptr (talignas 3%N (tptr tvoid))))))))
|}.

Definition f_alloc_make_Coq_Numbers_BinNums_positive_xO := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((__tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__arg0, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((__argv, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset __argv
    (Efield
      (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc
      (tptr (talignas 3%N (tptr tvoid)))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
          (Econst_long (Int64.repr 0) tlong)
          (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
      (Econst_long (Int64.repr 1025) tlong))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
            (Econst_long (Int64.repr 1) tlong)
            (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
        (Etempvar __arg0 (talignas 3%N (tptr tvoid))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc
              (tptr (talignas 3%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc
              (tptr (talignas 3%N (tptr tvoid))))
            (Ebinop Oadd (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))
              (Econst_long (Int64.repr 2) tlong)
              (tptr (talignas 3%N (tptr tvoid))))))
        (Sreturn (Some (Ebinop Oadd
                         (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
                         (Econst_long (Int64.repr 1) tlong)
                         (tptr (talignas 3%N (tptr tvoid))))))))))
|}.

Definition f_make_Coq_Numbers_BinNums_positive_xH := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Econst_int (Int.repr 1) tint)
                 (talignas 3%N (tptr tvoid)))))
|}.

Definition f_make_Coq_Numbers_BinNums_Z_Z0 := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Econst_int (Int.repr 1) tint)
                 (talignas 3%N (tptr tvoid)))))
|}.

Definition f_make_Coq_Numbers_BinNums_Z_Zpos := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((__arg0, (talignas 3%N (tptr tvoid))) ::
                (__argv, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
        (Econst_long (Int64.repr 0) tlong)
        (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
    (Ecast (Econst_long (Int64.repr 1024) tlong) (talignas 3%N (tptr tvoid))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
          (Econst_long (Int64.repr 1) tlong)
          (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
      (Etempvar __arg0 (talignas 3%N (tptr tvoid))))
    (Sreturn (Some (Ebinop Oadd
                     (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
                     (Econst_long (Int64.repr 1) tlong)
                     (tptr (talignas 3%N (tptr tvoid))))))))
|}.

Definition f_alloc_make_Coq_Numbers_BinNums_Z_Zpos := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((__tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__arg0, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((__argv, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset __argv
    (Efield
      (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc
      (tptr (talignas 3%N (tptr tvoid)))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
          (Econst_long (Int64.repr 0) tlong)
          (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
      (Econst_long (Int64.repr 1024) tlong))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
            (Econst_long (Int64.repr 1) tlong)
            (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
        (Etempvar __arg0 (talignas 3%N (tptr tvoid))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc
              (tptr (talignas 3%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc
              (tptr (talignas 3%N (tptr tvoid))))
            (Ebinop Oadd (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))
              (Econst_long (Int64.repr 2) tlong)
              (tptr (talignas 3%N (tptr tvoid))))))
        (Sreturn (Some (Ebinop Oadd
                         (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
                         (Econst_long (Int64.repr 1) tlong)
                         (tptr (talignas 3%N (tptr tvoid))))))))))
|}.

Definition f_make_Coq_Numbers_BinNums_Z_Zneg := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((__arg0, (talignas 3%N (tptr tvoid))) ::
                (__argv, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
        (Econst_long (Int64.repr 0) tlong)
        (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
    (Ecast (Econst_long (Int64.repr 1025) tlong) (talignas 3%N (tptr tvoid))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
          (Econst_long (Int64.repr 1) tlong)
          (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
      (Etempvar __arg0 (talignas 3%N (tptr tvoid))))
    (Sreturn (Some (Ebinop Oadd
                     (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
                     (Econst_long (Int64.repr 1) tlong)
                     (tptr (talignas 3%N (tptr tvoid))))))))
|}.

Definition f_alloc_make_Coq_Numbers_BinNums_Z_Zneg := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((__tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__arg0, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((__argv, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset __argv
    (Efield
      (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc
      (tptr (talignas 3%N (tptr tvoid)))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
          (Econst_long (Int64.repr 0) tlong)
          (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
      (Econst_long (Int64.repr 1025) tlong))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
            (Econst_long (Int64.repr 1) tlong)
            (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
        (Etempvar __arg0 (talignas 3%N (tptr tvoid))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc
              (tptr (talignas 3%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef (Etempvar __tinfo (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _alloc
              (tptr (talignas 3%N (tptr tvoid))))
            (Ebinop Oadd (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))
              (Econst_long (Int64.repr 2) tlong)
              (tptr (talignas 3%N (tptr tvoid))))))
        (Sreturn (Some (Ebinop Oadd
                         (Etempvar __argv (tptr (talignas 3%N (tptr tvoid))))
                         (Econst_long (Int64.repr 1) tlong)
                         (tptr (talignas 3%N (tptr tvoid))))))))))
|}.

Definition f_get_Coq_Numbers_BinNums_positive_tag := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((__v, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((__b, tbool) :: (__t, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _is_ptr (Tfunction (Tcons (talignas 3%N (tptr tvoid)) Tnil) tint
                      cc_default))
      ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
    (Sset __b (Ecast (Etempvar _t'1 tint) tbool)))
  (Sifthenelse (Etempvar __b tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_boxed_ordinal (Tfunction
                                     (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                     tulong cc_default))
          ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
        (Sset __t (Etempvar _t'2 tulong)))
      (Sswitch (Etempvar __t tulong)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          (LScons (Some 1)
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            LSnil))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_unboxed_ordinal (Tfunction
                                       (Tcons (talignas 3%N (tptr tvoid))
                                         Tnil) tulong cc_default))
          ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
        (Sset __t (Etempvar _t'3 tulong)))
      (Sswitch (Etempvar __t tulong)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 2) tint)))
          LSnil)))))
|}.

Definition f_get_Coq_Numbers_BinNums_Z_tag := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((__v, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((__b, tbool) :: (__t, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _is_ptr (Tfunction (Tcons (talignas 3%N (tptr tvoid)) Tnil) tint
                      cc_default))
      ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
    (Sset __b (Ecast (Etempvar _t'1 tint) tbool)))
  (Sifthenelse (Etempvar __b tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_boxed_ordinal (Tfunction
                                     (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                     tulong cc_default))
          ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
        (Sset __t (Etempvar _t'2 tulong)))
      (Sswitch (Etempvar __t tulong)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          (LScons (Some 1)
            (Sreturn (Some (Econst_int (Int.repr 2) tint)))
            LSnil))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_unboxed_ordinal (Tfunction
                                       (Tcons (talignas 3%N (tptr tvoid))
                                         Tnil) tulong cc_default))
          ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
        (Sset __t (Etempvar _t'3 tulong)))
      (Sswitch (Etempvar __t tulong)
        (LScons (Some 0)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          LSnil)))))
|}.

Definition f_print_Coq_Numbers_BinNums_positive := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((__v, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((__tag, tuint) :: (__args, (tptr tvoid)) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, tulong) :: (_t'5, (talignas 3%N (tptr tvoid))) ::
               (_t'4, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_Coq_Numbers_BinNums_positive_tag (Tfunction
                                                    (Tcons
                                                      (talignas 3%N (tptr tvoid))
                                                      Tnil) tulong
                                                    cc_default))
      ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
    (Sset __tag (Ecast (Etempvar _t'1 tulong) tuint)))
  (Sswitch (Etempvar __tag tuint)
    (LScons (Some 0)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _get_args (Tfunction
                              (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                              (tptr (talignas 3%N (tptr tvoid))) cc_default))
            ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
          (Sset __args (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))))
        (Ssequence
          (Scall None
            (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                            {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
            ((Evar _lparen_lit (tarray tschar 2)) :: nil))
          (Ssequence
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Ederef
                 (Ebinop Oadd
                   (Evar _names_of_Coq_Numbers_BinNums_positive (tarray (tarray tschar 3) 3))
                   (Etempvar __tag tuint) (tptr (tarray tschar 3)))
                 (tarray tschar 3)) :: nil))
            (Ssequence
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                ((Evar _space_lit (tarray tschar 2)) :: nil))
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Ederef
                      (Ebinop Oadd
                        (Ecast (Etempvar __args (tptr tvoid))
                          (tptr (talignas 3%N (tptr tvoid))))
                        (Econst_int (Int.repr 0) tint)
                        (tptr (talignas 3%N (tptr tvoid))))
                      (talignas 3%N (tptr tvoid))))
                  (Scall None
                    (Evar _print_Coq_Numbers_BinNums_positive (Tfunction
                                                                (Tcons
                                                                  (talignas 3%N (tptr tvoid))
                                                                  Tnil) tvoid
                                                                cc_default))
                    ((Etempvar _t'5 (talignas 3%N (tptr tvoid))) :: nil)))
                (Ssequence
                  (Scall None
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                    ((Evar _rparen_lit (tarray tschar 2)) :: nil))
                  Sbreak))))))
      (LScons (Some 1)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _get_args (Tfunction
                                (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                (tptr (talignas 3%N (tptr tvoid)))
                                cc_default))
              ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
            (Sset __args (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))))
          (Ssequence
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Evar _lparen_lit (tarray tschar 2)) :: nil))
            (Ssequence
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                ((Ederef
                   (Ebinop Oadd
                     (Evar _names_of_Coq_Numbers_BinNums_positive (tarray (tarray tschar 3) 3))
                     (Etempvar __tag tuint) (tptr (tarray tschar 3)))
                   (tarray tschar 3)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar _space_lit (tarray tschar 2)) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _t'4
                      (Ederef
                        (Ebinop Oadd
                          (Ecast (Etempvar __args (tptr tvoid))
                            (tptr (talignas 3%N (tptr tvoid))))
                          (Econst_int (Int.repr 0) tint)
                          (tptr (talignas 3%N (tptr tvoid))))
                        (talignas 3%N (tptr tvoid))))
                    (Scall None
                      (Evar _print_Coq_Numbers_BinNums_positive (Tfunction
                                                                  (Tcons
                                                                    (talignas 3%N (tptr tvoid))
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                      ((Etempvar _t'4 (talignas 3%N (tptr tvoid))) :: nil)))
                  (Ssequence
                    (Scall None
                      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                      tint
                                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                      ((Evar _rparen_lit (tarray tschar 2)) :: nil))
                    Sbreak))))))
        (LScons (Some 2)
          (Ssequence
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Ederef
                 (Ebinop Oadd
                   (Evar _names_of_Coq_Numbers_BinNums_positive (tarray (tarray tschar 3) 3))
                   (Etempvar __tag tuint) (tptr (tarray tschar 3)))
                 (tarray tschar 3)) :: nil))
            Sbreak)
          LSnil)))))
|}.

Definition f_print_Coq_Numbers_BinNums_Z := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((__v, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((__tag, tuint) :: (__args, (tptr tvoid)) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, tulong) :: (_t'5, (talignas 3%N (tptr tvoid))) ::
               (_t'4, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_Coq_Numbers_BinNums_Z_tag (Tfunction
                                             (Tcons
                                               (talignas 3%N (tptr tvoid))
                                               Tnil) tulong cc_default))
      ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
    (Sset __tag (Ecast (Etempvar _t'1 tulong) tuint)))
  (Sswitch (Etempvar __tag tuint)
    (LScons (Some 0)
      (Ssequence
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
          ((Ederef
             (Ebinop Oadd
               (Evar _names_of_Coq_Numbers_BinNums_Z (tarray (tarray tschar 5) 3))
               (Etempvar __tag tuint) (tptr (tarray tschar 5)))
             (tarray tschar 5)) :: nil))
        Sbreak)
      (LScons (Some 1)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _get_args (Tfunction
                                (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                (tptr (talignas 3%N (tptr tvoid)))
                                cc_default))
              ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
            (Sset __args (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))))
          (Ssequence
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
              ((Evar _lparen_lit (tarray tschar 2)) :: nil))
            (Ssequence
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                ((Ederef
                   (Ebinop Oadd
                     (Evar _names_of_Coq_Numbers_BinNums_Z (tarray (tarray tschar 5) 3))
                     (Etempvar __tag tuint) (tptr (tarray tschar 5)))
                   (tarray tschar 5)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Evar _space_lit (tarray tschar 2)) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Ederef
                        (Ebinop Oadd
                          (Ecast (Etempvar __args (tptr tvoid))
                            (tptr (talignas 3%N (tptr tvoid))))
                          (Econst_int (Int.repr 0) tint)
                          (tptr (talignas 3%N (tptr tvoid))))
                        (talignas 3%N (tptr tvoid))))
                    (Scall None
                      (Evar _print_Coq_Numbers_BinNums_positive (Tfunction
                                                                  (Tcons
                                                                    (talignas 3%N (tptr tvoid))
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                      ((Etempvar _t'5 (talignas 3%N (tptr tvoid))) :: nil)))
                  (Ssequence
                    (Scall None
                      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                      tint
                                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                      ((Evar _rparen_lit (tarray tschar 2)) :: nil))
                    Sbreak))))))
        (LScons (Some 2)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _get_args (Tfunction
                                  (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                  (tptr (talignas 3%N (tptr tvoid)))
                                  cc_default))
                ((Etempvar __v (talignas 3%N (tptr tvoid))) :: nil))
              (Sset __args
                (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))))
            (Ssequence
              (Scall None
                (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                ((Evar _lparen_lit (tarray tschar 2)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                  {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                  ((Ederef
                     (Ebinop Oadd
                       (Evar _names_of_Coq_Numbers_BinNums_Z (tarray (tarray tschar 5) 3))
                       (Etempvar __tag tuint) (tptr (tarray tschar 5)))
                     (tarray tschar 5)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                    ((Evar _space_lit (tarray tschar 2)) :: nil))
                  (Ssequence
                    (Ssequence
                      (Sset _t'4
                        (Ederef
                          (Ebinop Oadd
                            (Ecast (Etempvar __args (tptr tvoid))
                              (tptr (talignas 3%N (tptr tvoid))))
                            (Econst_int (Int.repr 0) tint)
                            (tptr (talignas 3%N (tptr tvoid))))
                          (talignas 3%N (tptr tvoid))))
                      (Scall None
                        (Evar _print_Coq_Numbers_BinNums_positive (Tfunction
                                                                    (Tcons
                                                                    (talignas 3%N (tptr tvoid))
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                        ((Etempvar _t'4 (talignas 3%N (tptr tvoid))) :: nil)))
                    (Ssequence
                      (Scall None
                        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                        tint
                                        {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
                        ((Evar _rparen_lit (tarray tschar 2)) :: nil))
                      Sbreak))))))
          LSnil)))))
|}.

Definition f_call := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((__tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (__clo, (talignas 3%N (tptr tvoid))) ::
                (__arg, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((__f, (talignas 3%N (tptr tvoid))) ::
               (__envi, (talignas 3%N (tptr tvoid))) ::
               (__tmp, (talignas 3%N (tptr tvoid))) ::
               (_t'1, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sset __f
    (Efield
      (Ederef
        (Ecast (Etempvar __clo (talignas 3%N (tptr tvoid)))
          (tptr (Tstruct _closure noattr))) (Tstruct _closure noattr)) _func
      (tptr (Tfunction
              (Tcons (tptr (Tstruct _thread_info noattr))
                (Tcons (talignas 3%N (tptr tvoid))
                  (Tcons (talignas 3%N (tptr tvoid)) Tnil)))
              (talignas 3%N (tptr tvoid)) cc_default))))
  (Ssequence
    (Sset __envi
      (Efield
        (Ederef
          (Ecast (Etempvar __clo (talignas 3%N (tptr tvoid)))
            (tptr (Tstruct _closure noattr))) (Tstruct _closure noattr)) _env
        (talignas 3%N (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Ecast (Etempvar __f (talignas 3%N (tptr tvoid)))
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _thread_info noattr))
                      (Tcons (talignas 3%N (tptr tvoid))
                        (Tcons (talignas 3%N (tptr tvoid)) Tnil)))
                    (talignas 3%N (tptr tvoid)) cc_default)))
          ((Etempvar __tinfo (tptr (Tstruct _thread_info noattr))) ::
           (Etempvar __envi (talignas 3%N (tptr tvoid))) ::
           (Etempvar __arg (talignas 3%N (tptr tvoid))) :: nil))
        (Sset __tmp (Etempvar _t'1 (talignas 3%N (tptr tvoid)))))
      (Sreturn (Some (Etempvar __tmp (talignas 3%N (tptr tvoid))))))))
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
 Composite _closure Struct
   (Member_plain _func
      (tptr (Tfunction
              (Tcons (tptr (Tstruct _thread_info noattr))
                (Tcons (talignas 3%N (tptr tvoid))
                  (Tcons (talignas 3%N (tptr tvoid)) Tnil)))
              (talignas 3%N (tptr tvoid)) cc_default)) ::
    Member_plain _env (talignas 3%N (tptr tvoid)) :: nil)
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
                   (mksignature (AST.Tlong :: nil) AST.Tint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_is_ptr,
   Gfun(External (EF_external "is_ptr"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (talignas 3%N (tptr tvoid)) Tnil) tint cc_default)) ::
 (_lparen_lit, Gvar v_lparen_lit) :: (_rparen_lit, Gvar v_rparen_lit) ::
 (_space_lit, Gvar v_space_lit) :: (_fun_lit, Gvar v_fun_lit) ::
 (_type_lit, Gvar v_type_lit) :: (_unk_lit, Gvar v_unk_lit) ::
 (_prop_lit, Gvar v_prop_lit) ::
 (_get_unboxed_ordinal, Gfun(Internal f_get_unboxed_ordinal)) ::
 (_get_boxed_ordinal, Gfun(Internal f_get_boxed_ordinal)) ::
 (_get_args, Gfun(Internal f_get_args)) ::
 (_names_of_Coq_Numbers_BinNums_positive, Gvar v_names_of_Coq_Numbers_BinNums_positive) ::
 (_names_of_Coq_Numbers_BinNums_Z, Gvar v_names_of_Coq_Numbers_BinNums_Z) ::
 (_make_Coq_Numbers_BinNums_positive_xI, Gfun(Internal f_make_Coq_Numbers_BinNums_positive_xI)) ::
 (_alloc_make_Coq_Numbers_BinNums_positive_xI, Gfun(Internal f_alloc_make_Coq_Numbers_BinNums_positive_xI)) ::
 (_make_Coq_Numbers_BinNums_positive_xO, Gfun(Internal f_make_Coq_Numbers_BinNums_positive_xO)) ::
 (_alloc_make_Coq_Numbers_BinNums_positive_xO, Gfun(Internal f_alloc_make_Coq_Numbers_BinNums_positive_xO)) ::
 (_make_Coq_Numbers_BinNums_positive_xH, Gfun(Internal f_make_Coq_Numbers_BinNums_positive_xH)) ::
 (_make_Coq_Numbers_BinNums_Z_Z0, Gfun(Internal f_make_Coq_Numbers_BinNums_Z_Z0)) ::
 (_make_Coq_Numbers_BinNums_Z_Zpos, Gfun(Internal f_make_Coq_Numbers_BinNums_Z_Zpos)) ::
 (_alloc_make_Coq_Numbers_BinNums_Z_Zpos, Gfun(Internal f_alloc_make_Coq_Numbers_BinNums_Z_Zpos)) ::
 (_make_Coq_Numbers_BinNums_Z_Zneg, Gfun(Internal f_make_Coq_Numbers_BinNums_Z_Zneg)) ::
 (_alloc_make_Coq_Numbers_BinNums_Z_Zneg, Gfun(Internal f_alloc_make_Coq_Numbers_BinNums_Z_Zneg)) ::
 (_get_Coq_Numbers_BinNums_positive_tag, Gfun(Internal f_get_Coq_Numbers_BinNums_positive_tag)) ::
 (_get_Coq_Numbers_BinNums_Z_tag, Gfun(Internal f_get_Coq_Numbers_BinNums_Z_tag)) ::
 (_print_Coq_Numbers_BinNums_positive, Gfun(Internal f_print_Coq_Numbers_BinNums_positive)) ::
 (_print_Coq_Numbers_BinNums_Z, Gfun(Internal f_print_Coq_Numbers_BinNums_Z)) ::
 (_call, Gfun(Internal f_call)) :: nil).

Definition public_idents : list ident :=
(_call :: _print_Coq_Numbers_BinNums_Z ::
 _print_Coq_Numbers_BinNums_positive :: _get_Coq_Numbers_BinNums_Z_tag ::
 _get_Coq_Numbers_BinNums_positive_tag ::
 _alloc_make_Coq_Numbers_BinNums_Z_Zneg ::
 _make_Coq_Numbers_BinNums_Z_Zneg ::
 _alloc_make_Coq_Numbers_BinNums_Z_Zpos ::
 _make_Coq_Numbers_BinNums_Z_Zpos :: _make_Coq_Numbers_BinNums_Z_Z0 ::
 _make_Coq_Numbers_BinNums_positive_xH ::
 _alloc_make_Coq_Numbers_BinNums_positive_xO ::
 _make_Coq_Numbers_BinNums_positive_xO ::
 _alloc_make_Coq_Numbers_BinNums_positive_xI ::
 _make_Coq_Numbers_BinNums_positive_xI :: _names_of_Coq_Numbers_BinNums_Z ::
 _names_of_Coq_Numbers_BinNums_positive :: _get_args :: _get_boxed_ordinal ::
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


