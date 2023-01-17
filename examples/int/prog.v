From CertiCoq.Plugin Require Import CertiCoq.

Require Import ZArith.
Require Import Psatz.

Module Type UInt63.
  Axiom t : Type.
  Axiom from_Z : Z -> t.
  Axiom to_Z : t -> Z.
  Axiom add : t -> t -> t.
  Axiom mul : t -> t -> t.
End UInt63.

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
   Qed.

  Definition add (x y: t) : t :=
  let '(exist _ xz x_pf) := x in
  let '(exist _ yz y_pf) := y in
  let z := ((xz + yz) mod (2^63))%Z in
  exist _ z (mod63_ok _).

  Definition mul (x y: t) : t :=
  let '(exist _ xz x_pf) := x in
  let '(exist _ yz y_pf) := y in
  let z := ((xz * yz) mod (2^63))%Z in
  exist _ z (mod63_ok _).

End FM.

Module C : UInt63.
  Axiom t : Type.
  Axiom from_Z : Z -> t.
  Axiom to_Z : t -> Z.
  Axiom add : t -> t -> t.
  Axiom mul : t -> t -> t.
End C.

Definition prog := C.to_Z (C.add (C.from_Z 3%Z) (C.from_Z 4%Z)).

CertiCoq Compile prog
  Extract Constants [
    C.from_Z => "uint63_from_Z",
    C.to_Z => "uint63_to_Z" with tinfo,
    C.add => "uint63_add"
  ]
  Include [ "prims.h" ].
