Require Import ZArith.
Require Import Psatz.
Require Import String.
Open Scope string.

Require Import VeriFFI.library.modelled.
Require Import VeriFFI.library.isomorphism.
Require Import VeriFFI.library.meta.

Unset MetaCoq Strict Unquote Universe Mode.
Require Import VeriFFI.generator.Rep.
Local Obligation Tactic := gen.
MetaCoq Run (gen_for Z).

Require Import VeriFFI.examples.uint63z.prog.

Module FM <: UInt63.
  Definition t := {z : Z | 0 <= z < 2^63}%Z.
  Definition from_Z (z : Z) : t.
    exists (Z.modulo z (2^63)).
    apply Z_mod_lt.
    constructor.
  Defined.

  Definition to_Z (z : t) : Z := proj1_sig z.

  Lemma mod63_ok:
    forall z, (0 <= z mod (2^63) < 2^63)%Z.
  Proof.
    intro. apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
  Defined.

  Definition add (x y: t) : t :=
  let '(exist xz x_pf) := x in
  let '(exist yz y_pf) := y in
  let z := ((xz + yz) mod (2^63))%Z in
  exist _ z (mod63_ok _).

  Definition mul (x y: t) : t :=
  let '(exist xz x_pf) := x in
  let '(exist yz y_pf) := y in
  let z := ((xz * yz) mod (2^63))%Z in
  exist _ z (mod63_ok _).
End FM.

Module UInt63_Proofs.
  Axiom Isomorphism_t : Isomorphism FM.t C.t.
  #[local] Existing Instance Isomorphism_t.

  Definition GraphPredicate_t : GraphPredicate FM.t.
    constructor.
    intros g outlier [z H] p.
    apply (match p with repZ i => i=z | _ => False end).
  Defined.

  #[local] Instance ForeignInGraph_t : ForeignInGraph FM.t C.t.
   apply (Build_InGraph _ GraphPredicate_t).
   -  intros ? ? [z H] ? ?. hnf in H0. contradiction.
   - intros; auto.
   - intros ? ? [z H] ? ? ?. hnf in H1. contradiction.
  Defined.

  Definition from_Z_desc : fn_desc :=
    {| fn_type_reified :=
        @ARG _ Z transparent (fun _ =>
          @RES _ FM.t opaque)
     ; foreign_fn := C.from_Z
     ; model_fn := fun '(x; tt) => FM.from_Z x
     ; f_arity := 1
     ; c_name := "int63_from_Z"
    |}.

  Definition to_Z_desc : fn_desc :=
    {| fn_type_reified :=
        @ARG _ FM.t opaque (fun _ =>
          @RES _ Z transparent)
     ; foreign_fn := C.to_Z
     ; model_fn := fun '(x; tt) => FM.to_Z x
     ; f_arity := 1
     ; c_name := "int63_to_Z"
     |}.

  Definition add_desc : fn_desc :=
    {| fn_type_reified :=
        @ARG _ FM.t opaque (fun _ =>
          @ARG _ FM.t opaque (fun _ =>
            @RES _ FM.t opaque))
     ; foreign_fn := C.add
     ; model_fn := fun '(x; (y; tt)) => FM.add x y
     ; f_arity := 2
     ; c_name := "int63_add"
     |}.

  Definition mul_desc : fn_desc :=
    {| fn_type_reified :=
        @ARG _ FM.t opaque (fun _ =>
          @ARG _ FM.t opaque (fun _ =>
            @RES _ FM.t opaque))
     ; foreign_fn := C.mul
     ; model_fn := fun '(x; (y; tt)) => FM.mul x y
     ; f_arity := 2
     ; c_name := "int63_mul"
     |}.

  Axiom from_Z_spec : model_spec from_Z_desc.
  Axiom to_Z_spec : model_spec to_Z_desc.
  Axiom add_spec : model_spec add_desc.
  Axiom mul_spec : model_spec mul_desc.

  Lemma seven : C.to_Z (C.add (C.from_Z 3%Z) (C.from_Z 4%Z)) = 7%Z.
  Proof.
    props from_Z_spec.
    props add_spec.
    props to_Z_spec.
    foreign_rewrites.
    unfold FM.to_Z, FM.add, FM.from_Z.
    simpl.
    rewrite Z.mod_small.
    auto.
    lia.
  Qed.

  Lemma add_assoc : forall (x y z : Z),
    C.to_Z (C.add (C.from_Z x) (C.add (C.from_Z y) (C.from_Z z))) =
    C.to_Z (C.add (C.add (C.from_Z x) (C.from_Z y)) (C.from_Z z)).
  Proof.
    intros x y z.
    props from_Z_spec.
    props to_Z_spec.
    props add_spec.
    foreign_rewrites.
    unfold FM.add, FM.from_Z, FM.to_Z.
    simpl.
    rewrite <- !(Z.add_mod y z).
    rewrite <- !(Z.add_mod x y).
    rewrite <- !(Z.add_mod).
    f_equal.
    apply Z.add_assoc.
    all: lia.
  Qed.

  Lemma mul_add_distr_l : forall (x y z : Z),
    C.to_Z (C.mul (C.from_Z x) (C.add (C.from_Z y) (C.from_Z z))) =
    C.to_Z (C.add (C.mul (C.from_Z x) (C.from_Z y)) (C.mul (C.from_Z x) (C.from_Z z))).
  Proof.
    intros x y z.
    props from_Z_spec.
    props to_Z_spec.
    props add_spec.
    props mul_spec.
    foreign_rewrites.
    unfold FM.mul, FM.add, FM.from_Z, FM.to_Z.
    simpl.
    pose (y' := Z.modulo y (Z.pow_pos 2 63)); fold y'.
    pose (z' := Z.modulo z (Z.pow_pos 2 63)); fold z'.
    rewrite <- Zplus_mod.
    rewrite <- Z.mul_add_distr_l.
    rewrite Zmult_mod_idemp_r.
    auto.
  Qed.

  Lemma mul_add_distr_r : forall (x y z : Z),
    C.to_Z (C.mul (C.add (C.from_Z x) (C.from_Z y)) (C.from_Z z)) =
    C.to_Z (C.add (C.mul (C.from_Z x) (C.from_Z z)) (C.mul (C.from_Z y) (C.from_Z z))).
  Proof.
    intros x y z.
    props from_Z_spec.
    props to_Z_spec.
    props add_spec.
    props mul_spec.
    foreign_rewrites.
    unfold FM.mul, FM.add, FM.from_Z, FM.to_Z.
    simpl.
    pose (x' := Z.modulo y (Z.pow_pos 2 63)); fold x'.
    pose (y' := Z.modulo y (Z.pow_pos 2 63)); fold y'.
    pose (z' := Z.modulo z (Z.pow_pos 2 63)); fold z'.
    rewrite <- Zplus_mod.
    rewrite <- Z.mul_add_distr_r.
    rewrite Zmult_mod_idemp_l.
    auto.
  Qed.

End UInt63_Proofs.
