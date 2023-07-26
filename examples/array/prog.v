From CertiCoq.Plugin Require Import CertiCoq.

Definition elt := nat.

Module Type Array.
  Axiom M : Type -> Type.
  Axiom pure : forall {A}, A -> M A.
  Axiom bind : forall {A B}, M A -> (A -> M B) -> M B.
  Axiom runM : forall {A} (len : nat) (init : elt), M A -> A.
  Axiom set : nat -> elt -> M unit.
  Axiom get : nat -> M elt.
End Array.

Module C <: Array.
  Inductive MI : Type -> Type :=
  | pureI : forall {A}, A -> MI A
  | bindI : forall {A B}, MI A -> (A -> MI B) -> MI B
  | setI : nat -> elt -> MI unit
  | getI : nat -> MI elt.

  Definition M := MI.
  Definition pure : forall {A}, A -> M A := @pureI.
  Definition bind : forall {A B}, M A -> (A -> M B) -> M B := @bindI.
  Definition set : nat -> elt -> M unit := @setI.
  Definition get : nat -> M elt := @getI.
  Axiom runM : forall {A} (len : nat) (init : elt), M A -> A.
End C.

Notation "e1 ;; e2" :=
  (@C.bind _ _ e1 (fun _ => e2)) (at level 61, right associativity).
Notation "x <- c1 ;; c2" :=
  (@C.bind _ _ c1 (fun x => c2)) (at level 61, c1 at next level, right associativity).

(*
Module Array2D.
  Definition runM {A} (rows cols : nat) (init : elt) (m : C.M A) : A :=
    C.runM (rows * cols) init m.

  Definition get {cols : nat} (row col : nat) : C.M elt :=
    C.get (row * cols + col).

  Definition set {cols : nat} (row col : nat) (x : elt) : C.M unit :=
    C.set (row * cols + col) x.
End Array2D.

Check (Array2D.runM 3 3 0 (Array2D.set 0 0 1 ;; Array2D.get 0 0)).
*)

Require Import List.
Import ListNotations.

Definition incr (i : nat) : C.M unit :=
  v <- C.get i ;;
  C.set i (1 + v).

Definition index : Type := nat.

Definition higher_elt (x : option (index * elt)) (y : (index * elt)) : option (index * elt) :=
  match x, y with
  | Some (i1, x'), (i2, y') => if Nat.leb x' y' then Some y else x
  | None, _ => Some y
  end.

Definition mode (xs : list elt) : option elt :=
  let fix create (xs : list elt) : C.M unit :=
    match xs with
    | [] => C.pure tt
    | y :: ys => incr y ;; create ys
    end in
  let fix find (len : index) (highest : option (index * elt)) : C.M (option (index * elt)) :=
    match len with
    | S len' => e <- C.get len' ;;
                find len' (higher_elt highest (len', e))
    | O => C.pure highest
    end in
  let final (len : index) : C.M (option index) :=
    o <- find len None ;;
    match o with
    | Some (i, o) => C.pure (Some i)
    | None => C.pure None
    end in
  let len := match xs with [] => O | _ => S (List.list_max xs) end in
  C.runM len O (create xs ;; final len).

Definition prog := mode [1;2;3;2;3;2;4].

(*
Definition fib (len : nat) : nat :=
  let fix aux (n : nat) (fuel : nat) {struct fuel} : C.M unit :=
    match fuel with
    | O => C.pure tt
    | S fuel' =>
      x <- C.get (pred (pred n)) ;;
      y <- C.get (pred n) ;;
      C.set n (x + y) ;;
      aux (S n) fuel'
    end
  in C.runM (S len) 1 (aux 2 (pred len) ;; C.get len).

Definition prog := fib 7.
*)

CertiCoq Compile prog
  Extract Constants [
    C.runM => "array_runM" with tinfo
  ]
  Include [ "prims.h" ].

CertiCoq Generate Glue -file "glue" [ option, nat, C.MI ].


