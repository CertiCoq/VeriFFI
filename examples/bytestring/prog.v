Require Import Coq.Numbers.Cyclic.Int63.Int63.
Require Import ExtLib.Structures.Monad.
Require Import String Ascii.

Axioms (word8 : Type)
       (word8_to_ascii : word8 -> ascii)
       (ascii_to_word8 : ascii -> word8)
       (to_upper : word8 -> word8)
       (bytestring : Type)
       (append : bytestring -> bytestring -> bytestring)
       (pack : string -> bytestring)
       (unpack : bytestring -> string)
       (map : (word8 -> word8) -> bytestring -> bytestring).

Inductive mytree (E : Type -> Type) (R : Type) : Type :=
| MyRet (r : R)
| MyVis {X : Type} (e : E X) (k : X -> mytree E R)
| MyTau (t : mytree E R).

Arguments MyRet [E R].
Arguments MyVis [E R] {X}.
Arguments MyTau [E R].

Definition trigger {E : Type -> Type} {A : Type} (e : E A) : mytree E A :=
  MyVis e (fun x => MyRet x).

Fixpoint ibind {E : Type -> Type} {A B : Type}
               (t : mytree E A) (k : A -> mytree E B) : mytree E B :=
  match t with
  | MyRet r => k r
  | MyVis e h => MyVis e (fun x => ibind (h x) k)
  | MyTau t' => MyTau (ibind t' k)
  end.

Instance Monad_mytree {E} : Monad (mytree E) :=
  {| ret := fun _ x => MyRet x ; bind := @ibind _ |}.

Inductive console : Type -> Type :=
| print_string : bytestring -> console unit
| scan_string : console bytestring.

Import MonadNotation.
Open Scope monad_scope.

Definition uppercase (b : bytestring) : bytestring :=
  map to_upper b.

Notation "x ++ y" := (append x y) (right associativity, at level 60).

Definition null : string :=
  String (Ascii false false false false false false false false) EmptyString.

Definition prog : mytree console unit :=
  (* trigger (print_string (pack "a" ++ pack null ++ pack "b")). *)
  trigger (print_string (pack "What's your name?")) ;;
  name <- trigger scan_string ;;
  trigger (print_string (pack "HELLO " ++ uppercase name ++ pack "!")).
