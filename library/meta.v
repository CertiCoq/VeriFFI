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

(* From VeriFFI Require Export verification.example.glue. *)
(* From VeriFFI Require Export verification.specs_library. *)

(* The type class to describe how a Coq type is represented in the CertiCoq heap graph.
   We also have some lemmas about this representation as a part of the type class. *)
Class InGraph (A : Type) :=
  { is_in_graph : graph -> A -> rep_type -> Prop }.
Class Rep (A : Type) : Type :=
  { in_graph : InGraph A
  ; has_v :
      forall (g : graph) (n : A) (v : VType), is_in_graph g n (repNode v) -> graph_has_v g v
  ; is_monotone :
      forall (g : graph) (to : nat) (lb : raw_vertex_block)
            (e : list (EType * (VType * VType))) (n : A) (p : rep_type),
      add_node_compatible g (new_copied_v g to) e ->
      graph_has_gen g to -> is_in_graph g n p -> is_in_graph (add_node g to lb e) n p
  }.

#[export] Instance InGraph_Prop : InGraph Prop :=
  {| is_in_graph g x p := graph_cRep g p (enum 0) [] |}.
#[export] Instance InGraph_Set : InGraph Set :=
  {| is_in_graph g x p := graph_cRep g p (enum 0) [] |}.
#[export] Instance InGraph_Type : InGraph Type :=
  {| is_in_graph g x p := graph_cRep g p (enum 0) [] |}.
#[export] Instance Rep_Prop : Rep Prop. Proof. apply (@Build_Rep _ InGraph_Prop). Admitted.
#[export] Instance Rep_Set : Rep Set. Proof. apply (@Build_Rep _ InGraph_Set). Admitted.
#[export] Instance Rep_Type : Rep Type. Proof. apply (@Build_Rep _ InGraph_Type). Admitted.

(* This is an unprovable but useful predicate about
   a Coq value being in the heap graph.
   Unprovable because it requires proving False.
   Useful because traversing HOAS-style annotations
   (like reific and annotated) requires a Rep instance.
   However, make sure you don't declare these as global instances.
   They should only be available in cases like this. *)
Theorem InGraph_any : forall {A : Type}, InGraph A.
Proof. intros. constructor. intros. exact False. Defined.
Theorem Rep_any : forall {A : Type}, Rep A.
Proof.
  intros. refine (@Build_Rep A (@InGraph_any A) _ _);
  intros; simpl in *; contradiction.
Defined.

(* Explain why we have type specific defs and proofs computed by tactics/metaprograms, instead of going from a deep embedded type desc to the proofs.  *)

(* The type to represent a constructor in an inductive data type.
   The name [reific] stands for "reified inductive constructor".
   Notice how this type uses Gallina binders,
   it is a weak HOAS description of the constructor. *)
(* What other examples of cls are there? *)
Inductive reific (cls : Type -> Type) : Type :=
(* the type parameters in parametric polymorphism, isn't represented immediately in memory,
but the possibility for representation is needed later, e.g., A in [list A] *)
 | TYPEPARAM  : (forall (A : Type) `{cls A}, reific cls) -> reific cls
(* Non-type parameters of a fixed type which isn't represented in memory, e.g., n in [n < m] *)
 | PARAM  : forall A : Type, (A -> reific cls) -> reific cls
(* index, represented in memory, e.g. the index of a vector *)
 | INDEX  : forall (A : Type) `{cls A}, (A -> reific cls) ->reific cls
 (* non-dependent version of arguments, argument represented in memory, e.g. for X/list X of cons *)
 | ARG : forall (A : Type) `{cls A}, reific cls -> reific cls
 (* dependent argument, represented in memory, e.g. in positive_nat_list *)
 | DEPARG : forall (A : Type) `{cls A}, (A -> reific cls) -> reific cls
(* the end type, e.g., list X for cons : forall X, X -> list X -> **list X** *)
 | RES  : forall (A : Type) `{cls A}, reific cls.

(* Makes nested sigmas (i.e. dependent tuples) of all the arguments. *)
Fixpoint args {cls : Type -> Type} (c : reific cls) : Type :=
  match c with
  | TYPEPARAM f => {A : Type & {H : cls A & args (f A H)}}
  | PARAM A f => {a : A & args (f a) }
  | INDEX A H f => {a : A & args (f a)}
  | ARG A H c => (A * args c)%type
  | DEPARG A H f => {a : A & args (f a)}
  | RES _ _ => unit
  end.

(* Instance of result type *)
Fixpoint result {cls : Type -> Type} (c : reific cls) (xs : args c) : {A : Type & cls A} :=
  match c as l return (args l -> {A : Type & cls A}) with
  | TYPEPARAM f => fun P => let '(a; (h; rest)) := P in result (f a h) rest
  | PARAM A f => fun P => let '(a; rest) := P in result (f a) rest
  | INDEX A H f => fun P => let '(a; rest) := P in result (f a) rest
  | ARG A H c => fun P => let '(a, rest) := P in result c rest
  | DEPARG A H f => fun P => let '(a; rest) := P in result (f a) rest
  | RES A H => fun _ => (A; H)
  end xs.

(* Makes a Coq level constructor type from a [reific], with the new type
   taking a nested dependent tuple instead of curried arguments. *)
Definition reconstruct {cls : Type -> Type} (c : reific cls) : Type :=
  forall (P : args c),
  projT1 (result c P).

(* The same thing as [reconstruct] but takes the actual constructor
   as an argument but "ignores" it. In reality that argument is
   used by the tactic to infer how to reconstruct. *)
Definition reconstructor {cls : Type -> Type} {T : Type} (x : T) (c : reific cls) :=
  reconstruct c.

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

Ltac reconstructing_aux C :=
  let P := fresh "P" in
  intro P;
  simpl in P;
  destruct_through C.

(* The entry point to the tactic that solves
   goals like [reconstructor S S_reific]. *)
Ltac reconstructing :=
  match goal with
  | [ |- @reconstructor _ _ ?C _ ] => hnf; reconstructing_aux C
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

Definition S_reific : reific :=
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

Definition pcons_reific : reific :=
  @TYPEPARAM (fun A H =>
                @ARG A H
                     (@ARG (plist A) (Rep_plist A H)
                           (@RES (plist A) (Rep_plist A H)))).

Definition pcons' : reconstructor (@pcons) pcons_reific.
  reconstructing. Defined.
Print pcons'.

Check <%
  @TYPEPARAM (fun A H =>
                @ARG A H
                     (@ARG (plist A) (Rep_plist A H)
                           (@RES (plist A) (Rep_plist A H))))  %>.


Definition cons_reific : reific :=
  @TYPEPARAM (fun A H =>
                @ARG A H
                     (@ARG (list A) (Rep_list A H)
                           (@RES (list A) (Rep_list A H)))).

Compute reconstructor (@cons) cons_reific.
Goal reconstructor (@cons) cons_reific.
  reconstructing. Defined.

Inductive two (A : Type) : Type :=
| mkTwo : A -> A -> two A.

Definition Rep_two : forall (A : Type), Rep A -> Rep (two A).
  intros. constructor. intros. exact True. Defined.
Existing Instance Rep_two.

Definition mkTwo_reific : reific :=
  @TYPEPARAM (fun A H =>
                @ARG A H (@ARG A H (@RES (two A) (Rep_two A H)))).

Goal reconstructor mkTwo mkTwo_reific.
  reconstructing. Defined.

Definition vnil_reific : reific :=
  @TYPEPARAM (fun A H =>
                (@RES (vec A O) (Rep_vec A O H))).

Goal (reconstructor vnil vnil_reific).
  reconstructing. Defined.

Definition vcons_reific : reific :=
  @TYPEPARAM (fun A H =>
     @INDEX nat Rep_nat (fun n =>
       @ARG A H (@ARG (vec A n) (Rep_vec A n H)
          (@RES (vec A (S n)) (Rep_vec A (S n) H))))).

Goal (reconstructor vcons vcons_reific).
  reconstructing. Defined.

Check <%% vec %%>.

*)

(* GENERATION *)
(* Require Import MetaCoq.Template.All. *)
Require Import MetaCoq.Template.utils.MCString.
Record constructor_description :=
  { ctor_name : string
  ; ctor_reific : reific Rep
  ; ctor_real : reconstruct ctor_reific
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
Class Descs (A : Type) :=
  { get_desc : forall (x : A),
      { c : constructor_description &
          { y : args (ctor_reific c) &
              JMeq (ctor_real c y) x }  }
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

Definition Reppyish := option ({A : Type & Rep A}).
