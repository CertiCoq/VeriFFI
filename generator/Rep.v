Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Lists.List
               Coq.Lists.ListSet.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad
               ExtLib.Data.String.

Require Import VeriFFI.generator.gen_utils.
Require Import VeriFFI.library.base_representation.
Require Import VeriFFI.library.meta.
Require Import VeriFFI.generator.InGraph.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import ListNotations.

Unset Strict Unquote Universe Mode.

Ltac destruct_conj H :=
  match type of H with
  | @ex _ _ =>
    let p := fresh "p" in
    let m := fresh "M" in
    destruct H as [p m]; destruct_conj m
  | @and _ _ =>
    let m1 := fresh "M" in
    let m2 := fresh "M" in
    destruct H as [m1 m2]; destruct_conj m2
  | _ => idtac
  end.

Ltac prove_has_v :=
  intros g x v;
  destruct x; intros H; simpl in *;
  try contradiction ; try (destruct_conj H; intuition).

Ltac prove_monotone_with_IH :=
  match goal with
  | [IH : forall (_ : rep_type), _ |- _ ] =>
    eapply IH; simpl; eauto
  end.

Ltac prove_monotone_with_IH' :=
  match goal with
  | [IH : forall (_ : @eq _ _ _) (_ : rep_type), _ |- _ ] =>
    eapply IH; simpl; eauto
  end.

Axiom graph_cRep_add_node : forall g to lb e p ts ps,
  add_node_compatible g (GCGraph.new_copied_v g to) e
   -> GCGraph.graph_has_gen g to
   -> graph_cRep g p ts ps
   -> graph_cRep (add_node g to lb e) p ts ps.

Ltac mon n :=
  let i := fresh "i" in
  match goal with
  | [|- @is_in_graph _ _ _ n _] =>
    let t := type of n in
    epose (i := @is_monotone t _ _ _ _ _ _ _ _ _ _)
  end;
  eapply i.

Ltac loop_over_app C :=
  match C with
  | ?a ?b =>
    match a with
    | ?c ?d => loop_over_app a ; mon d
    | ?e => mon b
    end
  | _ => idtac
  end.

Ltac prove_monotone :=
  intros g to lb e x p C G; revert p;
  induction x;
  unshelve (match goal with
  | [|- forall _ _, @is_in_graph _ _ _ ?this _] =>
    intros p H;
    hnf in H;
    destruct_conj H;
    repeat eexists;
    repeat split;
    loop_over_app this;
    try prove_monotone_with_IH;
    try (eauto || (eapply graph_cRep_add_node; eauto))
  end); auto.

Ltac rep_gen :=
  intros;
  repeat (match goal with
          | [R : Rep _ |- _] => destruct R
          end);
  econstructor; [prove_has_v | prove_monotone].

(* MetaCoq Run (in_graph_gen list). *)
(* Instance Rep_list : forall A `{Rep_A: Rep A}, Rep (list A). *)
(*   rep_gen. *)
(* Defined. *)

(* MetaCoq Run (in_graph_gen nat). *)
(* Instance Rep_nat : Rep nat. *)
(*   rep_gen. *)
(* Defined. *)

(* MetaCoq Run (in_graph_gen bool). *)
(* Instance Rep_bool : Rep bool. *)
(* econstructor. *)
(* prove_has_v. *)
(* prove_monotone. *)
(* Defined. *)

(* Inductive T := *)
(* | C1 : T *)
(* | C2 : bool -> T *)
(* | C3 : bool -> bool -> T -> T. *)

(* MetaCoq Run (in_graph_gen T). *)
(* Instance Rep_T : Rep T. *)
(* econstructor. *)
(* prove_has_v. *)
(* prove_monotone. *)
(* Defined. *)


(* MetaCoq Run (in_graph_gen option). *)
(* Definition Rep_option : forall A `{Rep_A: Rep A}, Rep (option A). *)
(* intros. destruct Rep_A. *)
(* econstructor. *)
(* prove_has_v. *)
(* prove_monotone. *)
(* Defined. *)

(* MetaCoq Run (in_graph_gen prod). *)
(* Definition Rep_prod : forall A `{Rep_A: Rep A} B `{Rep_B : Rep B}, Rep (prod A B). *)
(* intros. destruct Rep_A. destruct Rep_B. *)
(* econstructor. *)
(* prove_has_v. *)
(* prove_monotone. *)
(* Defined. *)


(* Inductive vec (A : Type) : nat -> Type := *)
(* | vnil : vec A O *)
(* | vcons : forall n, A -> vec A n -> vec A (S n). *)
(* MetaCoq Run (in_graph_gen vec). *)

(* (* MetaCoq Run (in_graph_gen vec). *) *)
(* Instance InGraph_vec (A : Type) (InGraph_A : InGraph A) (n : nat) : InGraph (vec A n) := *)
(*   let fix is_in_graph_vec (n : nat) (g : graph) (x : vec A n) (p : rep_type) {struct x} : Prop := *)
(*     match x with *)
(*     | vnil => graph_cRep g p (enum 0) [] *)
(*     | vcons arg0 arg1 arg2 => *)
(*         exists p0 p1 p2 : rep_type, *)
(*           @is_in_graph nat InGraph_nat g arg0 p0 /\ *)
(*           @is_in_graph A InGraph_A g arg1 p1 /\ *)
(*           is_in_graph_vec arg0 g arg2 p2 /\ *)
(*           graph_cRep g p (boxed 0 3) [p0; p1; p2] *)
(*     end *)
(*     in @Build_InGraph (vec A n) (is_in_graph_vec n). *)

(* Definition Rep_vec : forall A `{Rep_A: Rep A} n, Rep (vec A n). *)

(* intros. destruct Rep_A. *)
(* econstructor. *)
(* prove_has_v. *)
(* prove_monotone. *)
(* Defined. *)
