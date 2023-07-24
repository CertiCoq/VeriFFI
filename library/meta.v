Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Lists.List
               Coq.Lists.ListSet.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad.

Require Import VeriFFI.library.base_representation.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
   therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import ListNotations.

From VeriFFI Require Export verification.graph_add.
Require Import CertiGraph.CertiGC.GCGraph.

Notation " ( x ; p ) " := (existT _ x p).

(* The type class to describe how a Coq type is represented in the CertiCoq heap graph.
   We also have some lemmas about this representation as a part of the type class. *)
(* GraphPredicate is only for internal use, just to make automatic generation easier *)
Class GraphPredicate (A : Type) :=
  { graph_predicate : graph -> A -> rep_type -> Prop }.
Class InGraph (A : Type) : Type :=
  { is_in_graph : graph -> A -> rep_type -> Prop
  ; has_v :
      forall (g : graph) (n : A) (v : VType), is_in_graph g n (repNode v) -> graph_has_v g v
  ; is_monotone :
      forall (g : graph) (to : nat) (lb : raw_vertex_block)
            (e : list (EType * (VType * VType))) (n : A) (p : rep_type),
      add_node_compatible g (new_copied_v g to) e ->
      graph_has_gen g to -> is_in_graph g n p -> is_in_graph (add_node g to lb e) n p
  }.

#[export] Instance InGraph_Prop : InGraph Prop.
Proof.
  refine (@Build_InGraph _ (fun g x p => graph_cRep g p (enum 0) []) _ _).
  intros; simpl in *. intuition. induction p; intuition.
Defined.
#[export] Instance InGraph_Set : InGraph Set.
Proof.
  refine (@Build_InGraph _ (fun g x p => graph_cRep g p (enum 0) []) _ _).
  intros; simpl in *. intuition. induction p; intuition.
Defined.
#[export] Instance InGraph_Type : InGraph Type.
Proof.
  refine (@Build_InGraph _ (fun g x p => graph_cRep g p (enum 0) []) _ _).
  intros; simpl in *. intuition. induction p; intuition.
Defined.

(* This is an unprovable but useful predicate about
   a Coq value being in the heap graph.
   Unprovable because it requires proving False.
   Useful because traversing HOAS-style annotations
   (like reified and annotated) requires a Rep instance.
   However, make sure you don't declare these as global instances.
   They should only be available in cases like this. *)
Theorem InGraph_any : forall {A : Type}, InGraph A.
Proof.
  intros.
  refine (@Build_InGraph A (fun g x p => False) _ _);
  intros; simpl in *; contradiction.
Defined.

(* Explain why we have type specific defs and proofs computed by tactics/metaprograms, instead of going from a deep embedded type desc to the proofs.  *)

(* The type to represent a constructor in an inductive data type.
   The name [reified] stands for "reified inductive constructor".
   Notice how this type uses Gallina binders,
   it is a weak HOAS description of the constructor. *)
(* What other examples of cls are there? *)
Inductive reified (ann : Type -> Type) : Type :=
(* the type parameters in parametric polymorphism, isn't represented immediately in memory,
but the possibility for representation is needed later, e.g., A in [list A] *)
 | TYPEPARAM : (forall (A : Type) `{ann A}, reified ann) -> reified ann
 (* dependent argument, represented in memory, e.g. in positive_nat_list *)
 | ARG : forall (A : Type) `{ann A}, (A -> reified ann) -> reified ann
(* the end type, e.g., list X for cons : forall X, X -> list X -> **list X** *)
 | RES : forall (A : Type) `{ann A}, reified ann.

(* Makes nested sigmas (i.e. dependent tuples) of all the arguments. *)
Fixpoint args {cls : Type -> Type} (c : reified cls) : Type :=
  match c with
  | TYPEPARAM f => {A : Type & {H : cls A & args (f A H)}}
  | ARG A H f => {a : A & args (f a)}
  | RES _ _ => unit
  end.

(* Instance of result type *)
Fixpoint result {cls : Type -> Type} (c : reified cls) (xs : args c) : {A : Type & cls A} :=
  match c as l return (args l -> {A : Type & cls A}) with
  | TYPEPARAM f => fun P => let '(a; (h; rest)) := P in result (f a h) rest
  | ARG A H f => fun P => let '(a; rest) := P in result (f a) rest
  | RES A H => fun _ => (A; H)
  end xs.

(* some things are computationally irrelevant but still present at computational time *)
Variant erasure := erased | present.

Class ctor_ann (A : Type) : Type :=
  { is_erased : erasure
  ; field_in_graph : InGraph A
  }.

(* Makes a Coq level constructor type from a [reified], with the new type
   taking a nested dependent tuple instead of curried arguments. *)
Definition reflect {cls : Type -> Type} (c : reified cls) : Type :=
  forall (P : args c),
  projT1 (result c P).

(* The same thing as [reflect] but takes the actual constructor
   as an argument but "ignores" it. In reality that argument is
   used by the tactic to infer how to reflect. *)
Definition reflector {cls : Type -> Type} {T : Type} (x : T) (c : reified cls) :=
  reflect c.

Ltac destruct_through C :=
  match goal with
  | [P : (@sigT (_ _) _) |- _ ] =>
    destruct P; destruct_through C
  | [P : (@sigT _ _) |- _ ] =>
    let a := fresh "a" in destruct P as [a];
    destruct_through constr:(C a)
  | [P : (@prod _ _) |- _ ] =>
    let a := fresh "a" in destruct P as [a];
    let C' := constr:(C a) in
    destruct_through constr:(C a)
  | [P : unit |- _ ] => exact C
  end.

Ltac reflecting_aux C :=
  let P := fresh "P" in
  intro P;
  simpl in P;
  destruct_through C.

(* The entry point to the tactic that solves
   goals like [reflector S S_reified]. *)
Ltac reflecting :=
  match goal with
  | [ |- @reflector _ _ ?C _ ] => hnf; reflecting_aux C
  end.

(* EXAMPLES *)
(*
Instance Rep_unit : Rep unit.
  constructor. intros. exact True. Defined.
Instance Rep_nat : Rep nat.
  constructor. intros. exact True. Defined.
Instance Rep_list : forall A : Type, Rep A -> Rep (list A).
  intros. constructor. intros. exact True. Defined.

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n : nat, A -> vec A n -> vec A (S n).

Check <%% vec %%>.
Instance Rep_vec : forall (A : Type) (n : nat), Rep A -> Rep (vec A n).
  intros. constructor. intros. exact True. Defined.

Definition S_reified : reified :=
  @ARG nat Rep_nat (@RES nat Rep_nat).
Set Printing Universes.

Polymorphic Inductive plist (A : Type) :=
| pnil : plist A
| pcons : A -> plist A -> plist A.
Check <%% plist %%>.
Polymorphic Cumulative Inductive pprod (A B : Type) :=
| ppair : A -> B -> pprod A B.
Check <%% @pprod %%>.
Check tSort.

Instance Rep_plist (A : Type) (Rep_A : Rep A) : Rep (plist A) :=
  {| rep _ _ _ := False |}.

Definition pcons_reified : reified :=
  @TYPEPARAM (fun A H =>
                @ARG A H
                     (@ARG (plist A) (Rep_plist A H)
                           (@RES (plist A) (Rep_plist A H)))).

Definition pcons' : reflector (@pcons) pcons_reified.
  reflecting. Defined.
Print pcons'.

Check <%
  @TYPEPARAM (fun A H =>
                @ARG A H
                     (@ARG (plist A) (Rep_plist A H)
                           (@RES (plist A) (Rep_plist A H))))  %>.


Definition cons_reified : reified :=
  @TYPEPARAM (fun A H =>
                @ARG A H
                     (@ARG (list A) (Rep_list A H)
                           (@RES (list A) (Rep_list A H)))).

Compute reflector (@cons) cons_reified.
Goal reflector (@cons) cons_reified.
  reflecting. Defined.

Inductive two (A : Type) : Type :=
| mkTwo : A -> A -> two A.

Definition Rep_two : forall (A : Type), Rep A -> Rep (two A).
  intros. constructor. intros. exact True. Defined.
Existing Instance Rep_two.

Definition mkTwo_reified : reified :=
  @TYPEPARAM (fun A H =>
                @ARG A H (@ARG A H (@RES (two A) (Rep_two A H)))).

Goal reflector mkTwo mkTwo_reified.
  reflecting. Defined.

Definition vnil_reified : reified :=
  @TYPEPARAM (fun A H =>
                (@RES (vec A O) (Rep_vec A O H))).

Goal (reflector vnil vnil_reified).
  reflecting. Defined.

Definition vcons_reified : reified :=
  @TYPEPARAM (fun A H =>
     @INDEX nat Rep_nat (fun n =>
       @ARG A H (@ARG (vec A n) (Rep_vec A n H)
          (@RES (vec A (S n)) (Rep_vec A (S n) H))))).

Goal (reflector vcons vcons_reified).
  reflecting. Defined.

Check <%% vec %%>.

*)

(* GENERATION *)
(* Require Import MetaCoq.Template.All. *)
Require Import MetaCoq.Template.utils.MCString.
Record constructor_description :=
  { ctor_name : string
  ; ctor_reified : reified ctor_ann
  ; ctor_reflected : reflect ctor_reified
  ; ctor_tag : nat
  ; ctor_arity : nat
  }.

Class Desc {T : Type} (ctor_val : T) :=
  { desc : constructor_description
  (* Think about an addition like the following: *)
  (* ; proof : ctor_val = curry ctor_real *)
  }.

Require Import JMeq.

(* pattern match class? *)
Class Discrimination (A : Type) :=
  { get_desc : forall (x : A),
      { c : constructor_description &
          { y : args (ctor_reified c) &
              JMeq (ctor_reflected c y) x }  }
  }.

(*
Definition Descs_nat : Descs nat.
Proof.
  constructor.
  intros x.
  case x.
  exists (@desc _ O _). exists tt. auto.
  exists (@desc _ S _). exists (n; tt). auto.
Defined.
*)

Class Rep (A : Type) :=
  { in_graph : InGraph A
  ; disc : Discrimination A
  }.

Definition Reppyish := option ({A : Type & Rep A}).
