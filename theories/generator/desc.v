Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Lists.List
               Coq.Lists.ListSet.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad
               ExtLib.Data.String.

From MetaCoq.Template Require Import BasicAst.
Require Import MetaCoq.Template.All.

Require Import VeriFFI.generator.gen_utils.
Require Import VeriFFI.generator.rep.
Print Reps.

Module MyRepsTypes : RepsTypes.

Axiom rep_type : Type.
Axiom graph : Type.

Inductive cRep : Set :=
| enum : forall (ordinal : N), cRep
| boxed : forall (ordinal : N) (arity : N), cRep.

Axiom fitting_index : graph -> rep_type -> cRep -> list rep_type -> Prop.

End MyRepsTypes.

Module MyReps := Reps MyRepsTypes.
Import MyReps MyRepsTypes.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MonadNotation
       ListNotations
       MetaCoqNotations.

(* Axiom graph_has_v : graph -> rep_type -> Type. *)
Record representable_X  :=
  { X_type : Type;
    X_in_graph : graph -> X_type -> rep_type -> Prop;
    (* X_has_v : forall g n v, X_in_graph g n (repNode v) -> graph_has_v g v; *)
    (* X_monotone : forall g to lb e n p, *)
    (*     add_node_compatible g (new_copied_v g to) e *)
    (*     -> graph_has_gen g to *)
    (*     -> X_in_graph g n p *)
    (*     -> X_in_graph (add_node g to lb e) n p *)
    }.

Definition get_representable {A : Type} `{Rep A} : representable_X.
Proof.
  eapply (@Build_representable_X _ _).
  Unshelve.
  * exact A.
  * exact (@rep A H).
Defined.

Print Rep_Type.
Definition representable_Type : representable_X :=
  @get_representable Type Rep_Type.

Definition get_representableM {A : Type} : TemplateMonad representable_X :=
  x <- tmInferInstance (Some all) (Rep A) ;;
  match x with
  | my_None =>
    tmFail "Couldn't find the Rep instance for type."
  | my_Some ins =>
    ret (@get_representable A ins)
  end.



(*
Inductive constrCode :=
(* the type parameters in parametric polymorphism, isn't represented immediately in memory,
but the possibility for representation is needed later, e.g., A in [list A]
 *)
 | TYPEPARAM  : (representable_X -> constrCode) -> constrCode
(* Non-type parameters of a fixed type which isn't represented in memory, e.g., n in [n < m] *)
 | PARAM  : forall X : Type, (X -> constrCode) -> constrCode
(* index, represented in memory, e.g. the index of a vector *)
 | INDEX  : forall (X_: representable_X), (X_type X_ -> constrCode) -> constrCode
 (* non-dependent version of arguments, argument represented in memory, e.g. for X/list X of cons *)
 | ARG : representable_X -> constrCode -> constrCode
 (* dependent argument, represented in memory, e.g. in positive_nat_list *)
 | DEPARG : forall (X_: representable_X), (X_type X_ -> constrCode) -> constrCode
(* the end type, e.g., list X for cons : forall X, X -> list X -> **list X** *)
 | RES  : representable_X -> constrCode.

Fixpoint args (c : constrCode) : Type :=
    match c with
    | TYPEPARAM f => {X_ : representable_X & args (f X_) }
    | PARAM X f => {x : X & args (f x) }
    | INDEX X_ f => {x : X_type X_ & args (f x)}
    | ARG X_ arg => (X_type X_ * args arg)%type
    | DEPARG X_ f => {x : X_type X_ & args (f x) }
    | RES x => unit
end.

(* Instance of result type *)
Fixpoint getRes (c: constrCode) (xs : args c) : representable_X :=
  match c as l return (args l -> representable_X) with
  | TYPEPARAM f => fun H => let (X_, xs') := H in getRes (f X_) xs'
  | PARAM X f => fun H => let (x, xs') := H in getRes (f x) xs'
  | INDEX X_ f => fun H => let (x, xs') := H in getRes (f x) xs'
  | ARG X_ arg => fun H => let (x, xs') := H in getRes arg xs'
  | DEPARG X_ f => fun H  => let (x, xs') := H in getRes (f x) xs'
  | RES x => fun _ => x
  end xs.

Record constructor_description :=
{ name : ident;
  constr : constrCode;
  coqConstr : forall (xs : args constr), X_type (getRes constr xs)
}.
*)

Inductive code :=
(* the type parameters in parametric polymorphism, isn't represented immediately in memory,
but the possibility for representation is needed later, e.g., A in [list A]
 *)
 | TYPEPARAM  : (forall (A : Type) `{Rep A}, code) -> code
(* Non-type parameters of a fixed type which isn't represented in memory, e.g., n in [n < m] *)
 | PARAM  : forall X : Type, (X -> code) -> code
(* index, represented in memory, e.g. the index of a vector *)
 | INDEX  : forall (A : Type) `{Rep A}, (A -> code) -> code
 (* non-dependent version of arguments, argument represented in memory, e.g. for X/list X of cons *)
 | ARG : forall (A : Type) `{Rep A}, code -> code
 (* dependent argument, represented in memory, e.g. in positive_nat_list *)
 | DEPARG : forall (A : Type) `{Rep A}, (A -> code) -> code
(* the end type, e.g., list X for cons : forall X, X -> list X -> **list X** *)
 | RES  : forall (A : Type) `{Rep A}, code.


(*
Fixpoint reconstruct (c : code) : Type :=
  match c with
  | TYPEPARAM f => forall (a : Type), reconstruct (f a)
  (* | PARAM X x => _ *)
  (* | INDEX A H x => _ *)
  (* | ARG A H x => _ *)
  (* | DEPARG A H x => _ *)
  (* | RES A H => _ *)
  | _ => nat
  end.


Record constructor_description =
{ name : ident;
  constr : constrCode;
  coqConstr : forall (xs : args constr), X_type (getRes constr xs)
}.

Print TemplateMonad.
Check <% @S %>.
Check <%% @S %%>.
Check <%% @pair %%>.
Print  context.

Print context_decl.
Print  ind_params.
Print one_inductive_body.

Definition create_code
           (mut : mutual_inductive_body)
           (one : one_inductive_body)
           (ctor : (ident * term * nat)) : TemplateMonad constrCode :=
  let fix params (xs : context) (base : constrCode) : constrCode :=
      match xs with
      | nil => base
      | x :: rest =>
        params rest (TYPEPARAM (fun r => base))
      end
  in
  ret (params (ind_params mut) (RES representable_Type)).

Print TemplateMonad.

Definition create_desc {T : Type} (ctor_val : T) : TemplateMonad constructor_description :=
  t <- tmQuote ctor_val ;;
  match t with
  | tConstruct {| inductive_mind := kn ; inductive_ind := mut_tag |} ctor_tag _ =>
    mut <- tmQuoteInductive kn ;;

    match (nth_error (ind_bodies mut) mut_tag) with
    | None => tmFail "Impossible mutual block index"
    | Some one =>
      tmPrint one ;;
      match (nth_error (ind_ctors one) ctor_tag) with
      | None => tmFail "Impossible constructor index"
      | Some (ctor_name, ctor_type, ctor_arity) =>
        code <- create_code mut one (ctor_name, ctor_type, ctor_arity) ;;

        newName <- tmFreshName "new"%string ;;
        actual <- tmLemma newName (forall (xs : args code), X_type (getRes code xs)) ;;

        ret {| name := ctor_name
             ; constr := code
             ; coqConstr := actual
                 (* ltac:(simpl; intros; eapply T) *)
             |}
      end
    end
  | _ => tmFail "Not a constructor"
  end.

Notation "$ x" :=
  ((ltac:(let p y := exact y in run_template_program (create_desc x) p)))
  (only parsing, at level 30).

MetaCoq Run (create_desc S).
Next Obligation.


Check $ (@le_n).
Check $ (@le_S).
Check <%% @nil %%>.



(* Inductive arg_description := *)
(* | TYPEPARAM : forall (A : Type) (Rep_A : Rep A), arg_description -> arg_description *)
(* | PARAM : forall (A : Type) (Rep_A : Rep A), arg_description -> arg_description *)
(* | INDEX : forall (A : Type) (Rep_A : Rep A), arg_description -> arg_description *)
(* | ARG : forall (A : Type) (Rep_A : Rep A), arg_description -> arg_description *)
(* | RES : forall (A : Type) (Rep_A : Rep A), arg_description. *)


(* Check *)
(*    TYPEPARAM (A : Type) (!!Rep_A : Rep A) *)
(*      (INDEX (n : nat) (!!Rep_n : Rep nat) *)
(*        (ARG (x : A) (Rep_x : Rep A) *)
(*          (ARG (xs : vec A n) (Rep_xs : Rep (vec A n) *)
(*            (RES (vec A (S n)) (@vcons A n x xs) (Rep_res : Rep (vec A (S n)))))))). *)


(* Require Import Coq.Program.Equality. *)
(* Definition test : forall (A : Type) (P1 : nat) (x : vec A P1), Prop. *)
(* intros. *)
(* remember x as x'. *)
(* dependent induction x. *)
(* exact False. *)
(* apply (IHx x). auto. *)
(* Defined. *)

(* Eval compute in test. *)

(* Search _ (vec _ _). *)

*)
