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

CertiCoq Register [
    C.from_Z => "uint63_from_Z",
    C.to_Z => "uint63_to_Z" with tinfo,
    C.add => "uint63_add"
  ] Include [ "prims.h" ].

Definition prog := C.to_Z (C.add (C.from_Z 1) (C.from_Z 2)).

CertiCoq Compile -build_dir "examples/uint63z/" -file "prog" prog.
CertiCoq Generate Glue -build_dir "examples/uint63z" -file "glue" [ Z ].
