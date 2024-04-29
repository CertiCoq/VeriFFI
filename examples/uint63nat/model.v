Require Import ZArith.
Require Import Psatz.
Require Import String.
Open Scope string.

Require Import VeriFFI.library.modelled.
Require Import VeriFFI.library.isomorphism.
Require Import VeriFFI.library.meta.

Require Import VeriFFI.generator.Rep.
Local Obligation Tactic := gen.
MetaCoq Run (gen_for nat).
MetaCoq Run (desc_gen S).

Require Import VeriFFI.examples.uint63nat.prog.

Module FM <: UInt63.
  Definition t := {z : nat | z < 2^63}.
  Definition from_nat (z : nat) : t.
    exists (Nat.modulo z (2^63)).
    apply Nat.mod_upper_bound.
    apply Nat.pow_nonzero.
    auto.
  Defined.

  Definition to_nat (z : t) : nat := proj1_sig z.

  Lemma mod63_ok:
    forall z, (z mod (2^63) < 2^63)%nat.
  Proof. intro. apply Nat.mod_upper_bound, Nat.pow_nonzero. auto. Qed.

  Definition add (x y: t) : t :=
  let '(exist xz x_pf) := x in
  let '(exist yz y_pf) := y in
  let z := ((xz + yz) mod (2^63))%nat in
  exist _ z (mod63_ok _).

  Definition mul (x y: t) : t :=
  let '(exist xz x_pf) := x in
  let '(exist yz y_pf) := y in
  let z := ((xz * yz) mod (2^63))%nat in
  exist _ z (mod63_ok _).
End FM.

Module UInt63_Proofs.
  Axiom Isomorphism_t : Isomorphism FM.t C.t.
  #[local] Existing Instance Isomorphism_t.

  #[local] Instance GraphPredicate_t : GraphPredicate FM.t.
    constructor.
    intros g outlier [z H] p.
    apply (match p with repZ i => i= Z.of_nat z | _ => False end).
  Defined.

  #[local] Instance ForeignInGraph_t : ForeignInGraph FM.t C.t.
   apply (Build_InGraph _ GraphPredicate_t).
   -  intros ? ? [z H] ? ?. hnf in H0. contradiction.
   - intros; auto.
   - intros ? ? [z H] ? ? ?. hnf in H1. contradiction.
  Defined.

  Definition from_nat_desc : fn_desc :=
    {| type_desc :=
        @ARG _ nat transparent (fun _ =>
          @RES _ FM.t opaque)
     ; foreign_fn := C.from_nat
     ; model_fn := fun '(x; tt) => FM.from_nat x
     ; f_arity := 1
     ; c_name := "int63_from_nat"
    |}.

  Definition to_nat_desc : fn_desc :=
    {| type_desc :=
        @ARG _ FM.t opaque (fun _ =>
          @RES _ nat transparent)
     ; foreign_fn := C.to_nat
     ; model_fn := fun '(x; tt) => FM.to_nat x
     ; f_arity := 1
     ; c_name := "int63_to_nat"
     |}.

  Definition add_desc : fn_desc :=
    {| type_desc :=
        @ARG _ FM.t opaque (fun _ =>
          @ARG _ FM.t opaque (fun _ =>
            @RES _ FM.t opaque))
     ; foreign_fn := C.add
     ; model_fn := fun '(x; (y; tt)) => FM.add x y
     ; f_arity := 2
     ; c_name := "int63_add"
     |}.

  Definition mul_desc : fn_desc :=
    {| type_desc :=
        @ARG _ FM.t opaque (fun _ =>
          @ARG _ FM.t opaque (fun _ =>
            @RES _ FM.t opaque))
     ; foreign_fn := C.mul
     ; model_fn := fun '(x; (y; tt)) => FM.mul x y
     ; f_arity := 2
     ; c_name := "int63_mul"
     |}.

  Axiom from_nat_spec : model_spec from_nat_desc.
  Axiom to_nat_spec : model_spec to_nat_desc.
  Axiom add_spec : model_spec add_desc.
  Axiom mul_spec : model_spec mul_desc.

  (* Class HasSpec {A} (f : A) : Type := *)
  (*   { get_spec : {d : fn_desc & model_spec d} }. *)

  (* Instance HasSpec_from_nat : HasSpec C.from_nat := *)
  (*   {| get_spec := (from_nat_desc; from_nat_spec) |}. *)
  (* Instance HasSpec_to_nat : HasSpec C.to_nat := *)
  (*   {| get_spec := (to_nat_desc; to_nat_spec) |}. *)
  (* Instance HasSpec_add : HasSpec C.add := *)
  (*   {| get_spec := (add_desc; add_spec) |}. *)
  (* Instance HasSpec_mul : HasSpec C.mul := *)
  (*   {| get_spec := (mul_desc; mul_spec) |}. *)

(* commented out to reduce chatter in build
  Eval cbn in model_spec from_nat_desc.
  Eval cbn in model_spec to_nat_desc.
  Eval cbn in model_spec add_desc.
*)
  Lemma add_assoc : forall (x y z : nat),
    C.to_nat (C.add (C.from_nat x) (C.add (C.from_nat y) (C.from_nat z))) =
    C.to_nat (C.add (C.add (C.from_nat x) (C.from_nat y)) (C.from_nat z)).
  Proof.
    (* let o := open_constr:(HasSpec C.to_nat) in unshelve evar (x:o); [typeclasses eauto|]. *)
    intros x y z.
    props to_nat_spec.
    props add_spec.
    props from_nat_spec.
    foreign_rewrites.
    unfold FM.add, FM.from_nat, FM.to_nat.
    (* the rest is just a proof about the functional model *)
    unfold proj1_sig.
    rewrite <- !(Nat.Div0.add_mod y z).
    rewrite <- !(Nat.Div0.add_mod x y).
    rewrite <- !(Nat.Div0.add_mod).
    f_equal.
    apply Nat.add_assoc.
    all: apply Nat.pow_nonzero; auto.
  Qed.

End UInt63_Proofs.
