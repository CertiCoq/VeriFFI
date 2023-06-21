Require Import ZArith.
Require Import Psatz.
Require Import String.
Open Scope string.

Require Import VeriFFI.library.modelled.
Require Import VeriFFI.library.isomorphism.
Require Import VeriFFI.library.meta.

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
  Axiom Isomorphism_t : Isomorphism C.t FM.t.

  Definition from_nat_ep : extern_properties :=
    {| type_desc :=
        @TRANSPARENT nat Rep_nat
           (Some (fun n => @OPAQUE _ _ Isomorphism_t None))
     ; prim_fn := C.from_nat
     ; model_fn := FM.from_nat
     ; c_name := "int63_from_nat"
     |}.

  Definition to_nat_ep : extern_properties :=
    {| type_desc :=
        @OPAQUE _ _ Isomorphism_t
           (Some (fun n => @TRANSPARENT nat Rep_nat None))
     ; prim_fn := C.to_nat
     ; model_fn := FM.to_nat
     ; c_name := "int63_to_nat"
     |}.

  Definition add_ep : extern_properties :=
    {| type_desc :=
          @OPAQUE _ _ Isomorphism_t
            (Some (fun i =>
              @OPAQUE _ _ Isomorphism_t
                (Some (fun i => @OPAQUE _ _ Isomorphism_t None))))
     ; prim_fn := C.add
     ; model_fn := FM.add
     ; c_name := "int63_add"
     |}.

  Definition mul_ep : extern_properties :=
    {| type_desc :=
          @OPAQUE _ _ Isomorphism_t
            (Some (fun i =>
              @OPAQUE _ _ Isomorphism_t
                (Some (fun i => @OPAQUE _ _ Isomorphism_t None))))
     ; prim_fn := C.mul
     ; model_fn := FM.mul
     ; c_name := "int63_mul"
     |}.

  Axiom from_nat_properties : model_spec from_nat_ep.
  Axiom to_nat_properties : model_spec to_nat_ep.
  Axiom add_properties : model_spec add_ep.
  Axiom mul_properties : model_spec mul_ep.

  Eval cbn in model_spec from_nat_ep.
  Eval cbn in model_spec to_nat_ep.
  Eval cbn in model_spec add_ep.

  Lemma add_assoc : forall (x y z : nat),
    C.to_nat (C.add (C.from_nat x) (C.add (C.from_nat y) (C.from_nat z))) =
    C.to_nat (C.add (C.add (C.from_nat x) (C.from_nat y)) (C.from_nat z)).
  Proof.
    Check pair.
    intros x y z.
    props from_nat_properties.
    props to_nat_properties.
    props add_properties.
    repeat eq_refl_match.
    rewrite !from_to, !to_from.
    unfold FM.add, FM.from_nat, FM.to_nat.
    (* the rest is just a proof about the functional model *)
    unfold proj1_sig.
    rewrite <- !(Nat.add_mod y z).
    rewrite <- !(Nat.add_mod x y).
    rewrite <- !(Nat.add_mod).
    f_equal.
    apply Nat.add_assoc.
    all: apply Nat.pow_nonzero; auto.
  Qed.

End UInt63_Proofs.
