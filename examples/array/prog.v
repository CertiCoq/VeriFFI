From CertiCoq.Plugin Require Import CertiCoq.

Definition elt := nat.

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

(* Definition prog := C.runM 3 5 (C.bind (C.set 1 5) (fun _ => C.get 1)). *)

Require Import List.
Import ListNotations.
(* Find the mode of a list, i.e. the element with the highest frequency *)
Definition mode (xs : list nat) : option nat :=
  let len := 1 + List.list_max xs in
  let fix assign (xs : list nat) : C.M unit :=
    match xs with
    | [] => C.pure tt
    | y :: ys => C.bind (C.get y) (fun o =>
                 C.bind (C.set y (match o with Some i => 1 + i | None => 1 end)) (fun _ =>
                         assign ys))
    end in
  let fix get_max (index : nat) (current : option (nat * nat)) : C.M (option nat) :=
    match index with
    | O => C.pure (match current with None => None | Some (i, _) => Some i end)
    | S index' => C.bind (C.get index) (fun o =>
                          match o, current with
                          | Some e, Some (i, c) => get_max index' (Some (if Nat.leb e c then (i, c) else (index, e)))
                          | Some e, _ => get_max index' (Some (index, e))
                          | _, Some (i, c) => get_max index' (Some (i, c))
                          | _, _ => get_max index' None
                          end)
    end in
  C.runM len 0 (C.get 0).
  (* C.runM len 0 (C.bind (C.get 0) (fun i => C.pure i)). *)
  (* C.runM len 0 (C.bind (assign xs) (fun _ => C.pure (Some 5))). *)
  (* C.runM len 0 (C.bind (assign xs) (fun _ => get_max len None)). *)

(* Definition prog := mode [1;2;3;4;5;2]. *)
Definition prog := mode [1].

CertiCoq Compile -cps prog
  Extract Constants [
    C.runM => "array_runM" with tinfo
  ]
  Include [ "prims.h" ].
CertiCoq Generate Glue -file "glue" -cps [ option, nat, C.MI ].
