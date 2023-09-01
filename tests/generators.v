(*
Require Import VeriFFI.generator.Rep.

MetaCoq Run (gen_for unit).
MetaCoq Run (gen_for bool).
MetaCoq Run (gen_for nat).
MetaCoq Run (gen_for option).
MetaCoq Run (gen_for prod).
MetaCoq Run (gen_for list).

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A O
| vcons : forall n, A -> vec A n -> vec A (S n).

MetaCoq Run (gen_for nat).

Inductive option_indexed : Type -> Type :=
| mysome : forall A, A -> option_indexed A.
(* This is supposed to fail because if the type argument is not a parameter,
   then knowing how to represent things of that type statically is tricky,
   and often impossible. *)
Fail MetaCoq Run (gen_for option_indexed).

Inductive mylist (A B : Type) : Type :=
| mynil : mylist A B
| mycons : A -> option A -> option B -> mylist A B.
MetaCoq Run (in_graph_gen mylist).

(* Testing mutually recursive inductive types: *)
Inductive T1 :=
| c1 : T2 -> T1
with T2 :=
| c2 : T1 -> T2.
MetaCoq Run (gen_for T1).

Inductive tree (A : Type) : Type :=
| tleaf : tree A
| tnode : nat -> forest A -> tree A
with forest (A : Type) : Type :=
| fnil : forest A
| fcons : tree A -> forest A -> forest A.
MetaCoq Run (gen_for tree)

(* Testing dependent types: *)
Inductive natty : nat -> nat -> Type :=
| mynatty : forall n m, natty n m.
MetaCoq Run (gen_for natty).

Inductive D1 : nat -> Type :=
| cd1 : forall n : nat, D1 n.
MetaCoq Run (gen_for D1).

Inductive D2 (n : nat) : Type :=
| cd2 : D2 n.
MetaCoq Run (gen_for D2).

Inductive indexed : nat -> Type :=
| bar : indexed O.
MetaCoq Run (gen_for indexed).

Inductive fin : nat -> Set :=
| F1 : forall {n}, fin (S n)
| FS : forall {n}, fin n -> fin (S n).
MetaCoq Run (gen_for fin).

Inductive param_and_index (a b : nat) : a < b -> Type :=
| foo : forall (pf : a < b), param_and_index a b pf.
MetaCoq Run (gen_for param_and_index).

(* Testing nested types: *)
(* "Haskell Programming with Nested Types: A Principled Approach", Johann and Ghani, 2009 *)
Inductive lam (A : Type) : Type :=
| variable : A -> lam A
| app : lam A -> lam A -> lam A
| abs : lam (option A) -> lam A.
MetaCoq Run (gen_for lam).

Inductive digit (A : Type) : Type :=
| one : A -> digit A
| two : A -> A -> digit A
| three : A -> A -> A -> digit A
| four : A -> A -> A -> A -> digit A.
Inductive node (A : Type) : Type :=
| node2 : nat -> A -> A -> node A
| node3 : nat -> A -> A -> A -> node A.
Inductive finger_tree (A : Type) : Type :=
| emptyT : finger_tree A
| single : A -> finger_tree A
| deep : nat -> digit A -> finger_tree (node A) -> digit A -> finger_tree A.
MetaCoq Run (gen_for finger_tree).

Inductive two (A : Type) :=
| mkTwo : A -> A -> two A.
Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : two (tree A) -> tree A.
Inductive ntree (A : Type) : Type :=
| nleaf : ntree A
| nnode : ntree (two A) -> ntree A.
MetaCoq Run (gen_for ntree).
*)
