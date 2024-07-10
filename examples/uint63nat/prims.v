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
  Definition source_file := "examples/uint63nat/prims.c".
  Definition normalized := true.
End Info.

Definition __ALLOC : ident := $"_ALLOC".
Definition __LIMIT : ident := $"_LIMIT".
Definition ___FRAME__ : ident := $"__FRAME__".
Definition ___PREV__ : ident := $"__PREV__".
Definition ___ROOT__ : ident := $"__ROOT__".
Definition ___RTEMP__ : ident := $"__RTEMP__".
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
Definition _args : ident := $"args".
Definition _fp : ident := $"fp".
Definition _garbage_collect : ident := $"garbage_collect".
Definition _get_Coq_Init_Datatypes_nat_tag : ident := $"get_Coq_Init_Datatypes_nat_tag".
Definition _get_args : ident := $"get_args".
Definition _heap : ident := $"heap".
Definition _i : ident := $"i".
Definition _limit : ident := $"limit".
Definition _main : ident := $"main".
Definition _make_Coq_Init_Datatypes_nat_O : ident := $"make_Coq_Init_Datatypes_nat_O".
Definition _n : ident := $"n".
Definition _nalloc : ident := $"nalloc".
Definition _next : ident := $"next".
Definition _odata : ident := $"odata".
Definition _prev : ident := $"prev".
Definition _rem_limit : ident := $"rem_limit".
Definition _root : ident := $"root".
Definition _save0 : ident := $"save0".
Definition _space : ident := $"space".
Definition _spaces : ident := $"spaces".
Definition _stack_frame : ident := $"stack_frame".
Definition _start : ident := $"start".
Definition _t : ident := $"t".
Definition _temp : ident := $"temp".
Definition _thread_info : ident := $"thread_info".
Definition _tinfo : ident := $"tinfo".
Definition _uint63_add : ident := $"uint63_add".
Definition _uint63_from_nat : ident := $"uint63_from_nat".
Definition _uint63_mul : ident := $"uint63_mul".
Definition _uint63_to_nat : ident := $"uint63_to_nat".
Definition _uint63_to_nat_no_gc : ident := $"uint63_to_nat_no_gc".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Definition f_uint63_from_nat := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_n, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_temp, (talignas 3%N (tptr tvoid))) :: (_i, tulong) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _temp (Etempvar _n (talignas 3%N (tptr tvoid))))
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Sloop
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _get_Coq_Init_Datatypes_nat_tag (Tfunction
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
            (Sset _i
              (Ebinop Oadd (Etempvar _i tulong)
                (Econst_int (Int.repr 1) tint) tulong))
            (Ssequence
              (Scall (Some _t'2)
                (Evar _get_args (Tfunction
                                  (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                  (tptr (talignas 3%N (tptr tvoid)))
                                  cc_default))
                ((Etempvar _temp (talignas 3%N (tptr tvoid))) :: nil))
              (Sset _temp
                (Ederef
                  (Ebinop Oadd
                    (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (talignas 3%N (tptr tvoid))))
                  (talignas 3%N (tptr tvoid)))))))
        Sskip)
      (Sreturn (Some (Ecast
                       (Ebinop Oadd
                         (Ebinop Oshl (Etempvar _i tulong)
                           (Econst_int (Int.repr 1) tint) tulong)
                         (Econst_int (Int.repr 1) tint) tulong)
                       (talignas 3%N (tptr tvoid))))))))
|}.

Definition f_uint63_to_nat_no_gc := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_t, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_temp, (talignas 3%N (tptr tvoid))) ::
               (_t'2, (talignas 3%N (tptr tvoid))) ::
               (_t'1, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sset _i
    (Ecast
      (Ebinop Oshr (Ecast (Etempvar _t (talignas 3%N (tptr tvoid))) tulong)
        (Econst_int (Int.repr 1) tint) tulong) tulong))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _make_Coq_Init_Datatypes_nat_O (Tfunction Tnil
                                               (talignas 3%N (tptr tvoid))
                                               cc_default)) nil)
      (Sset _temp (Etempvar _t'1 (talignas 3%N (tptr tvoid)))))
    (Ssequence
      (Swhile
        (Etempvar _i tulong)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _alloc_make_Coq_Init_Datatypes_nat_S (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _thread_info noattr))
                                                             (Tcons
                                                               (talignas 3%N (tptr tvoid))
                                                               Tnil))
                                                           (talignas 3%N (tptr tvoid))
                                                           cc_default))
              ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
               (Etempvar _temp (talignas 3%N (tptr tvoid))) :: nil))
            (Sset _temp (Etempvar _t'2 (talignas 3%N (tptr tvoid)))))
          (Sset _i
            (Ebinop Osub (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      (Sreturn (Some (Etempvar _temp (talignas 3%N (tptr tvoid))))))))
|}.

Definition f_uint63_to_nat := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_t, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := ((___ROOT__, (tarray (talignas 3%N (tptr tvoid)) 1)) ::
              (___FRAME__, (Tstruct _stack_frame noattr)) :: nil);
  fn_temps := ((_i, tulong) :: (_save0, (talignas 3%N (tptr tvoid))) ::
               (__ALLOC, (tptr (talignas 3%N (tptr tvoid)))) ::
               (__LIMIT, (tptr (talignas 3%N (tptr tvoid)))) ::
               (___PREV__, (tptr (Tstruct _stack_frame noattr))) ::
               (_nalloc, tulong) ::
               (___RTEMP__, (talignas 3%N (tptr tvoid))) ::
               (_t'2, (talignas 3%N (tptr tvoid))) ::
               (_t'1, (talignas 3%N (tptr tvoid))) ::
               (_t'3, (tptr (Tstruct _stack_frame noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _i
    (Ecast
      (Ebinop Oshr (Ecast (Etempvar _t (talignas 3%N (tptr tvoid))) tulong)
        (Econst_int (Int.repr 1) tint) tulong) tulong))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _make_Coq_Init_Datatypes_nat_O (Tfunction Tnil
                                               (talignas 3%N (tptr tvoid))
                                               cc_default)) nil)
      (Sset _save0 (Etempvar _t'1 (talignas 3%N (tptr tvoid)))))
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
            (Sset _t'3
              (Efield
                (Ederef
                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _fp
                (tptr (Tstruct _stack_frame noattr))))
            (Sassign
              (Efield (Evar ___FRAME__ (Tstruct _stack_frame noattr)) _prev
                (tptr (Tstruct _stack_frame noattr)))
              (Etempvar _t'3 (tptr (Tstruct _stack_frame noattr)))))
          (Ssequence
            (Swhile
              (Etempvar _i tulong)
              (Ssequence
                (Sset _nalloc (Ecast (Econst_int (Int.repr 2) tint) tulong))
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
                      (Scall (Some _t'2)
                        (Evar _alloc_make_Coq_Init_Datatypes_nat_S (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _thread_info noattr))
                                                                    (Tcons
                                                                    (talignas 3%N (tptr tvoid))
                                                                    Tnil))
                                                                    (talignas 3%N (tptr tvoid))
                                                                    cc_default))
                        ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                         (Etempvar _save0 (talignas 3%N (tptr tvoid))) ::
                         nil))
                      (Sset _save0
                        (Etempvar _t'2 (talignas 3%N (tptr tvoid)))))
                    (Sset _i
                      (Ebinop Osub (Etempvar _i tulong)
                        (Econst_int (Int.repr 1) tint) tulong))))))
            (Sreturn (Some (Etempvar _save0 (talignas 3%N (tptr tvoid)))))))))))
|}.

Definition f_uint63_add := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                (_x, (talignas 3%N (tptr tvoid))) ::
                (_y, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oadd
                   (Ebinop Oshl
                     (Ebinop Oadd
                       (Ebinop Oshr
                         (Ecast (Etempvar _x (talignas 3%N (tptr tvoid)))
                           tulong) (Econst_int (Int.repr 1) tint) tulong)
                       (Ebinop Oshr
                         (Ecast (Etempvar _y (talignas 3%N (tptr tvoid)))
                           tulong) (Econst_int (Int.repr 1) tint) tulong)
                       tulong) (Econst_int (Int.repr 1) tint) tulong)
                   (Econst_int (Int.repr 1) tint) tulong)
                 (talignas 3%N (tptr tvoid)))))
|}.

Definition f_uint63_mul := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 3%N (tptr tvoid))) ::
                (_y, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oadd
                   (Ebinop Oshl
                     (Ebinop Omul
                       (Ebinop Oshr
                         (Ecast (Etempvar _x (talignas 3%N (tptr tvoid)))
                           tulong) (Econst_int (Int.repr 1) tint) tulong)
                       (Ebinop Oshr
                         (Ecast (Etempvar _y (talignas 3%N (tptr tvoid)))
                           tulong) (Econst_int (Int.repr 1) tint) tulong)
                       tulong) (Econst_int (Int.repr 1) tint) tulong)
                   (Econst_int (Int.repr 1) tint) tulong)
                 (talignas 3%N (tptr tvoid)))))
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
 (_garbage_collect,
   Gfun(External (EF_external "garbage_collect"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _thread_info noattr)) Tnil) tvoid cc_default)) ::
 (_get_args,
   Gfun(External (EF_external "get_args"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (talignas 3%N (tptr tvoid)) Tnil)
     (tptr (talignas 3%N (tptr tvoid))) cc_default)) ::
 (_make_Coq_Init_Datatypes_nat_O,
   Gfun(External (EF_external "make_Coq_Init_Datatypes_nat_O"
                   (mksignature nil AST.Tlong cc_default)) Tnil
     (talignas 3%N (tptr tvoid)) cc_default)) ::
 (_alloc_make_Coq_Init_Datatypes_nat_S,
   Gfun(External (EF_external "alloc_make_Coq_Init_Datatypes_nat_S"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default))
     (Tcons (tptr (Tstruct _thread_info noattr))
       (Tcons (talignas 3%N (tptr tvoid)) Tnil)) (talignas 3%N (tptr tvoid))
     cc_default)) ::
 (_get_Coq_Init_Datatypes_nat_tag,
   Gfun(External (EF_external "get_Coq_Init_Datatypes_nat_tag"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (talignas 3%N (tptr tvoid)) Tnil) tulong cc_default)) ::
 (_uint63_from_nat, Gfun(Internal f_uint63_from_nat)) ::
 (_uint63_to_nat_no_gc, Gfun(Internal f_uint63_to_nat_no_gc)) ::
 (_uint63_to_nat, Gfun(Internal f_uint63_to_nat)) ::
 (_uint63_add, Gfun(Internal f_uint63_add)) ::
 (_uint63_mul, Gfun(Internal f_uint63_mul)) :: nil).

Definition public_idents : list ident :=
(_uint63_mul :: _uint63_add :: _uint63_to_nat :: _uint63_to_nat_no_gc ::
 _uint63_from_nat :: _get_Coq_Init_Datatypes_nat_tag ::
 _alloc_make_Coq_Init_Datatypes_nat_S :: _make_Coq_Init_Datatypes_nat_O ::
 _get_args :: _garbage_collect :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


