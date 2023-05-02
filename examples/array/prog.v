From CertiCoq.Plugin Require Import CertiCoq.

Definition elt := bool.

Module Type Array.
  Axiom M : Type -> Type.
  Axiom pure : forall {A}, A -> M A.
  Axiom bind : forall {A B}, M A -> (A -> M B) -> M B.
  Axiom runM : forall {A} (len : nat) (init : elt), M A -> A.
  Axiom set : nat -> elt -> M unit.
  Axiom get : nat -> M (option elt).
End Array.

Module C <: Array.
  Inductive MI : Type -> Type :=
  | pureI : forall {A}, A -> MI A
  | bindI : forall {A B}, MI A -> (A -> MI B) -> MI B
  | setI : nat -> elt -> MI unit
  | getI : nat -> MI (option elt).

  Definition M := MI.
  Definition pure : forall {A}, A -> M A := @pureI.
  Definition bind : forall {A B}, M A -> (A -> M B) -> M B := @bindI.
  Definition set : nat -> elt -> M unit := @setI.
  Definition get : nat -> M (option elt) := @getI.
  Axiom runM : forall {A} (len : nat) (init : elt), M A -> A.
End C.

Definition prog := C.runM 3 true (C.bind (C.set 1 false) (fun _ => C.get 1)).
CertiCoq Compile -cps prog
  Extract Constants [
    C.runM => "array_runM" with tinfo
  ]
  Include [ "prims.h" ].
Inductive le (n : nat) : forall _ : nat, Type :=
    le_n : le n n  | le_S : forall (m : nat) (_ : le n m), le n (S m).

CertiCoq Generate Glue -file "glue" -cps [ le ].
(* CertiCoq Generate Glue -file "glue" -cps [ unit, nat, bool, pair, C.MI, le ]. *)
