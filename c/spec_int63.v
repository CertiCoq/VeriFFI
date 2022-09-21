From VST Require Import floyd.proofauto.
From VeriFFI Require Import c.int63.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

From VeriFFI Require Import library.modelled.

(*

Definition encode_Z (x: Z): Z := x * 2 + 1.

Module encode_Z.
    Definition min_signed: Z := - 2^62.
    Definition max_signed: Z := 2^62 - 1.

    Lemma bound_iff (x: Z):
        Int64.min_signed <= encode_Z x <= Int64.max_signed <-> min_signed <= x <= max_signed.
    Proof.
        unfold encode_Z.
        unfold min_signed.
        unfold max_signed.
        assert (E: Int64.min_signed = - 2^63). { reflexivity. } rewrite E in * ; clear E.
        assert (E: Int64.max_signed = 2^63 - 1). { reflexivity. } rewrite E in * ; clear E.
        constructor ; lia.
    Qed.

    Lemma bitwise (x: Z):
        encode_Z x = Z.lor 1 (Z.shiftl x 1).
    Proof.
        unfold encode_Z.
        rewrite Z.shiftl_mul_pow2 ; try lia.
        assert (E: 2 ^ 1 = 2). { lia. } rewrite E ; clear E.
        assert (E: x * 2 = 2 * x). { lia. } repeat rewrite E ; clear E.
        assert (E: 2 * x + 1 = 1 + 2 * x). { lia. } repeat rewrite E ; clear E.
        destruct x as [ | x' | x' ] ; try reflexivity.
        destruct x' ; try reflexivity.
    Qed.

    Lemma bound (x: Z) (H: Int64.min_signed <= encode_Z x <= Int64.max_signed):
        Int64.min_signed <= x <= Int64.max_signed.
    Proof.
        unfold encode_Z in *.
        unfold Int64.min_signed in *.
        unfold Int64.max_signed in *.
        constructor ; try lia.
    Qed.

    Lemma tight_bound (x: Z) (Hx: Int64.min_signed <= encode_Z x <= Int64.max_signed):
        Int64.min_signed < encode_Z x <= Int64.max_signed.
    Proof.
        constructor ; try lia.

        destruct Hx as [ Hx_l Hx_h ]. clear Hx_h.
        assert (Hx_l': Int64.min_signed < encode_Z x \/ Int64.min_signed = encode_Z x). { lia. } clear Hx_l. rename Hx_l' into Hx_l.
        destruct Hx_l as [ Hx_l | Hx_l ] ; try assumption.
        unfold encode_Z in *.

        assert (E: x * 2 + 1 = 1 + 2 * x). { lia. } rewrite E in * ; clear E.
        assert (F: Z.even Int64.min_signed = Z.even (1 + 2 * x)). {  congruence. } clear Hx_l.
        rewrite Z.even_add_mul_2 in F.
        inversion F.
    Qed.
End encode_Z.

Definition certicoq_encode_int63_spec: ident * funspec :=
    DECLARE _certicoq_encode_int63
    WITH x: Z, gv: globals
    PRE [ tlong ]
        PROP ( )
        PARAMS (Vlong (Int64.repr x))
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z x)))
        SEP ( ).

Definition certicoq_decode_int63_spec: ident * funspec :=
    DECLARE _certicoq_decode_int63
    WITH x: Z, gv: globals
    PRE [ tlong ]
        PROP (Int64.min_signed <= encode_Z x <= Int64.max_signed)
        PARAMS (Vlong (Int64.repr (encode_Z x)))
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr x))
        SEP ( ).
*)

Definition tvalue := Tlong Signed noattr.
Definition threadinfo := Tstruct _thread_info noattr.

(*
Definition certicoq_prim__int63_zero_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_zero
    WITH tinfo: val
    PRE [ tptr threadinfo ]
        PROP ()
        PARAMS ( tinfo )
        GLOBALS()
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr 0))
        SEP ( ).

Definition certicoq_prim__int63_one_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_one
    WITH tinfo: val
    PRE [ tptr threadinfo ]
        PROP ()
        PARAMS ( tinfo )
        GLOBALS()
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr 1))
        SEP ( ).

Definition certicoq_prim__int63_neg_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_neg
    WITH x: Z, gv: globals
    PRE [ tlong ]
        PROP (
            Int64.min_signed <= encode_Z x <= Int64.max_signed;
            Int64.min_signed <= encode_Z (- x) <= Int64.max_signed
        )
        PARAMS (Vlong (Int64.repr (encode_Z x)))
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z (- x))))
        SEP ( ).

Definition certicoq_prim__int63_abs_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_abs
    WITH x: Z, gv: globals
    PRE [ tlong ]
        PROP (
            Int64.min_signed <= encode_Z x <= Int64.max_signed;
            Int64.min_signed <= encode_Z (- x) <= Int64.max_signed
        )
        PARAMS (Vlong (Int64.repr (encode_Z x)))
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z (Z.abs x))))
        SEP ( ).
*)

Import IntVerification.

Definition tag63 (x: FM.t) := Vlong (Int64.repr (2*(proj1_sig x)+1)).

Definition certicoq_prim__int63_add_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_add
    WITH tinfo: val, x: FM.t, y:FM.t
    PRE [ tptr threadinfo, tlong, tlong ]
        PROP ()
        PARAMS (tinfo; tag63 x; tag63 y)
        GLOBALS()
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (tag63 (FM.add x y))
        SEP ( ).

(*
Definition certicoq_prim__int63_sub_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_add
    WITH x: FM.t, y:FM.t
    PRE [ tlong, tlong ]
        PROP ()
        PARAMS (tag63 x; tag63 y)
        GLOBALS()
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (tag63 (FMs.sub x y))
        SEP ( ).
*)

Definition certicoq_prim__int63_mul_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_mul
    WITH tinfo: val, x: FM.t, y:FM.t
    PRE [ tptr threadinfo, tlong, tlong ]
        PROP ()
        PARAMS (tinfo; tag63 x; tag63 y)
        GLOBALS()
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (tag63 (FM.mul x y))
        SEP ( ).
(*

Definition certicoq_prim__int63_div_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_div
    WITH x: Z, y: Z, gv: globals
    PRE [ tlong, tlong ]
        PROP (
            Int64.min_signed <= encode_Z x <= Int64.max_signed;
            Int64.min_signed <= encode_Z y <= Int64.max_signed;
            y <> 0
        )
        PARAMS (
            Vlong (Int64.repr (encode_Z x));
            Vlong (Int64.repr (encode_Z y))
        )
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z (Z.quot x y))))
        SEP ( ).

Definition certicoq_prim__int63_rem_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_rem
    WITH x: Z, y: Z, gv: globals
    PRE [ tlong, tlong ]
        PROP (
            Int64.min_signed <= encode_Z x <= Int64.max_signed;
            Int64.min_signed <= encode_Z y <= Int64.max_signed;
            y <> 0
        )
        PARAMS (
            Vlong (Int64.repr (encode_Z x));
            Vlong (Int64.repr (encode_Z y))
        )
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z (Z.rem x y))))
        SEP ( ).

Definition certicoq_prim__int63_shiftl_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_shiftl
    WITH x: Z, y: Z, gv: globals
    PRE [ tlong, tlong ]
        PROP (
            Int64.min_signed <= encode_Z x <= Int64.max_signed;
            Int64.min_signed <= encode_Z y <= Int64.max_signed;
            0 <= x;
            0 <= y < Int64.zwordsize
        )
        PARAMS (
            Vlong (Int64.repr (encode_Z x));
            Vlong (Int64.repr (encode_Z y))
        )
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z (Z.shiftl x y))))
        SEP ( ).

Definition certicoq_prim__int63_shiftr_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_shiftr
    WITH x: Z, y: Z, gv: globals
    PRE [ tlong, tlong ]
        PROP (
            Int64.min_signed <= encode_Z x <= Int64.max_signed;
            Int64.min_signed <= encode_Z y <= Int64.max_signed;
            0 <= y < Int64.zwordsize
        )
        PARAMS (
            Vlong (Int64.repr (encode_Z x));
            Vlong (Int64.repr (encode_Z y))
        )
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z (Z.shiftr x y))))
        SEP ( ).

Definition certicoq_prim__int63_or_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_or
    WITH x: Z, y: Z, gv: globals
    PRE [ tlong, tlong ]
        PROP (
            Int64.min_signed <= encode_Z x <= Int64.max_signed;
            Int64.min_signed <= encode_Z y <= Int64.max_signed
        )
        PARAMS (
            Vlong (Int64.repr (encode_Z x));
            Vlong (Int64.repr (encode_Z y))
        )
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z (Z.lor x y))))
        SEP ( ).

Definition certicoq_prim__int63_and_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_and
    WITH x: Z, y: Z, gv: globals
    PRE [ tlong, tlong ]
        PROP (
            Int64.min_signed <= encode_Z x <= Int64.max_signed;
            Int64.min_signed <= encode_Z y <= Int64.max_signed
        )
        PARAMS (
            Vlong (Int64.repr (encode_Z x));
            Vlong (Int64.repr (encode_Z y))
        )
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z (Z.land x y))))
        SEP ( ).

Definition certicoq_prim__int63_xor_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_xor
    WITH x: Z, y: Z, gv: globals
    PRE [ tlong, tlong ]
        PROP (
            Int64.min_signed <= encode_Z x <= Int64.max_signed;
            Int64.min_signed <= encode_Z y <= Int64.max_signed
        )
        PARAMS (
            Vlong (Int64.repr (encode_Z x));
            Vlong (Int64.repr (encode_Z y))
        )
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z (Z.lxor x y))))
        SEP ( ).

Definition certicoq_prim__int63_not_spec: ident * funspec :=
    DECLARE _certicoq_prim__int63_not
    WITH x: Z, gv: globals
    PRE [ tlong ]
        PROP (Int64.min_signed <= encode_Z x <= Int64.max_signed)
        PARAMS (Vlong (Int64.repr (encode_Z x)))
        GLOBALS(gv)
        SEP ( )
    POST [ tlong ]
        PROP ( )
        RETURN (Vlong (Int64.repr (encode_Z (Z.lnot x))))
        SEP ( ).
*)


Definition ASI: funspecs := [
(*
    certicoq_decode_int63_spec;
    certicoq_encode_int63_spec;
    certicoq_prim__int63_zero_spec;
    certicoq_prim__int63_one_spec;
    certicoq_prim__int63_neg_spec;
    certicoq_prim__int63_abs_spec;
*)
    certicoq_prim__int63_add_spec;
(*
    certicoq_prim__int63_sub_spec;
*)
    certicoq_prim__int63_mul_spec
(*
    certicoq_prim__int63_div_spec;
    certicoq_prim__int63_rem_spec;
    certicoq_prim__int63_shiftl_spec;
    certicoq_prim__int63_shiftr_spec;
    certicoq_prim__int63_or_spec;
    certicoq_prim__int63_and_spec;
    certicoq_prim__int63_xor_spec;
    certicoq_prim__int63_not_spec
*)
].

