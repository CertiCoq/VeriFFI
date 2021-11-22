(** Demo Glue File 
    
    Demo file on what ``rep.v`` generates.
*)

Require Import BinNums.

(* Variables of types for graph and how to describe elements in the graph/outside *)
Variable graph : Type.
Variable mtype : Type.

(* Taken from Olivier, needed to be fetched by CertiCoq. *)
Inductive cRep : Set := enum : N -> cRep | boxed : N -> N -> cRep.

(* Should be generated, here just to display what we want. *)
Variable tag_nat : nat -> cRep. 

(* This function can be general and independent of the generated code.
Note that we don't need the tag references after all - they can be put into fitting_index. *)
Variable fitting_index : graph -> mtype -> cRep -> list mtype -> Prop.

(* Example for nat. *)
Fixpoint nat_in_graph (g : graph) (n : nat) (p : mtype) : Prop :=
  match n with 
  | O => fitting_index g p (tag_nat 0) nil
  | S n' => exists p1, nat_in_graph g n' p1 /\ fitting_index g p (tag_nat (S n)) (p1 :: nil)
end.


(* Example for list *)

Variable tag_list : forall {X} (xs : list X), cRep. 

Fixpoint list_in_graph (X: Type) (X_in_graph : graph -> X -> mtype -> Prop) (g : graph) (xs : list X) (p : mtype) := 
match xs with 
| nil => fitting_index g p (tag_list (@nil X)) nil
| cons x xs' => exists p1 p2, X_in_graph g x p1 /\ list_in_graph X X_in_graph g xs' p2 /\ fitting_index g p (tag_list (cons x xs)) (p1 :: p2 :: nil)
end.

Inductive Y :=
| A : forall (X: Type) (x : X), Y. 

Variable tag_Y : Y -> cRep.

Fixpoint Y_in_graph (g : graph) (y : Y) (p : mtype) :=
match y with
| A X x => exists (X_in_graph : graph -> X -> mtype -> Prop), exists p1, X_in_graph g x p1 /\ fitting_index g p (tag_Y y) (p1 :: nil)
end. 








