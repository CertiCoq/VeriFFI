From CertiCoq.Plugin Require Import CertiCoq.

Require Import String.

Module Type Bytestring.
  Axiom bytestring : Type.
  Axiom append : bytestring -> bytestring -> bytestring.
  Axiom pack : string -> bytestring.
  Axiom unpack : bytestring -> string.

  Axiom M : Type -> Type.
  Axiom pure : forall {A}, A -> M A.
  Axiom bind : forall {A B}, M A -> (A -> M B) -> M B.
  Axiom print : bytestring -> M unit.
  Axiom scan : nat -> M bytestring.

  Axiom stream : Type.
  Axiom get_stdin : unit -> stream.
  Axiom get_stdout : unit -> stream.

  Axiom runM : forall {A} (instream outstream : stream), M A -> A.
End Bytestring.

Module C <: Bytestring.
  Axiom bytestring : Type.
  Axiom append : bytestring -> bytestring -> bytestring.
  Axiom pack : string -> bytestring.
  Axiom unpack : bytestring -> string.

  Inductive MI : Type -> Type :=
  | pureI : forall {A}, A -> MI A
  | bindI : forall {A B}, MI A -> (A -> MI B) -> MI B
  | printI : bytestring -> MI unit
  | scanI : nat -> MI bytestring.

  Definition M := MI.
  Definition pure : forall {A}, A -> M A := @pureI.
  Definition bind : forall {A B}, M A -> (A -> M B) -> M B := @bindI.
  Definition print : bytestring -> M unit := @printI.
  Definition scan : nat -> M bytestring := @scanI.

  Axiom stream : Type.
  Axiom get_stdin : unit -> stream.
  Axiom get_stdout : unit -> stream.

  Axiom runM : forall {A} (instream outstream : stream), M A -> A.
End C.

CertiCoq Register [
    C.append => "append" with tinfo,
    C.pack => "pack" with tinfo,
    C.unpack => "unpack" with tinfo,
    C.runM => "runM" with tinfo,
    C.get_stdin => "get_stdin" with tinfo,
    C.get_stdout => "get_stdout" with tinfo
  ] Include [ "prims.h" ].

Notation "e1 ;; e2" :=
  (@C.bind _ _ e1 (fun _ => e2)) (at level 61, right associativity).
Notation "x <- c1 ;; c2" :=
  (@C.bind _ _ c1 (fun x => c2)) (at level 61, c1 at next level, right associativity).
Notation "x ++ y" := (C.append x y) (right associativity, at level 60).

Definition prog : unit :=
  C.runM (C.get_stdin tt) (C.get_stdout tt)
    (x <- C.scan 10 ;;
     y <- C.scan 10 ;;
     C.print (C.pack "Hello, " ++ x ++ C.pack " " ++ y)).
