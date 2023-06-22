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

Module C : UInt63.
  Axiom t : Type.
  Axiom from_Z : Z -> t.
  Axiom to_Z : t -> Z.
  Axiom add : t -> t -> t.
  Axiom mul : t -> t -> t.
End C.

Definition prog := C.to_Z (C.add (C.from_Z 3%Z) (C.from_Z 4%Z)).

CertiCoq Compile -cps prog
  Extract Constants [
    C.from_Z => "uint63_from_Z",
    C.to_Z => "uint63_to_Z" with tinfo,
    C.add => "uint63_add"
  ]
  Include [ "prims.h" ].
CertiCoq Generate Glue -file "glue" -cps [ Z ].
