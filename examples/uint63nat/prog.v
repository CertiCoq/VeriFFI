From CertiCoq.Plugin Require Import CertiCoq.

Require Import ZArith.
Require Import Psatz.

Module Type UInt63.
  Axiom t : Type.
  Axiom from_nat : nat -> t.
  Axiom to_nat : t -> nat.
  Axiom add : t -> t -> t.
  Axiom mul : t -> t -> t.
End UInt63.


Module C : UInt63.
  Axiom t : Type.
  Axiom from_nat : nat -> t.
  Axiom to_nat : t -> nat.
  Axiom add : t -> t -> t.
  Axiom mul : t -> t -> t.
End C.

Definition prog := C.to_nat (C.add (C.from_nat 1) (C.from_nat 2)).
CertiCoq Compile -cps prog
  Extract Constants [
    C.from_nat => "uint63_from_nat",
    C.to_nat => "uint63_to_nat" with tinfo,
    C.add => "uint63_add"
  ]
  Include [ "prims.h" ].
CertiCoq Generate Glue -file "glue" [ nat ].
<<<<<<< HEAD

Inductive exp : Type :=
| etrue
| efalse
| eand : exp -> exp
| eor : exp -> exp
| eif : exp -> exp -> exp -> exp.

Inductive T : Type :=
| mkT : nat -> bool -> unit -> T.

CertiCoq Generate Glue -file "glue" [ nat, bool, exp, T ].
*)
=======
>>>>>>> parent of b290b36 (Remove unnecessary files)
