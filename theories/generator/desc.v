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

Print MyReps.

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


Inductive code :=
(* the type parameters in parametric polymorphism, isn't represented immediately in memory,
but the possibility for representation is needed later, e.g., A in [list A]
 *)
 | TYPEPARAM  : (forall (A : Type) `{Rep A}, code) -> code
(* Non-type parameters of a fixed type which isn't represented in memory, e.g., n in [n < m] *)
 | PARAM  : forall A : Type, (A -> code) -> code
(* index, represented in memory, e.g. the index of a vector *)
 | INDEX  : forall (A : Type) `{Rep A}, (A -> code) -> code
 (* non-dependent version of arguments, argument represented in memory, e.g. for X/list X of cons *)
 | ARG : forall (A : Type) `{Rep A}, code -> code
 (* dependent argument, represented in memory, e.g. in positive_nat_list *)
 | DEPARG : forall (A : Type) `{Rep A}, (A -> code) -> code
(* the end type, e.g., list X for cons : forall X, X -> list X -> **list X** *)
 | RES  : forall (A : Type) `{Rep A}, code.

Fixpoint args (c : code) : Type :=
  match c with
  | TYPEPARAM f => {A : Type & {H : Rep A & args (f A H)}}
  | PARAM A f => {a : A & args (f a) }
  | INDEX A H f => {a : A & args (f a)}
  | ARG A H c => (A * args c)%type
  | DEPARG A H f => {a : A & args (f a)}
  | RES _ _ => unit
  end.

Definition Reppy := {A : Type & Rep A}.

(* Instance of result type *)
Fixpoint result (c: code) (xs : args c) : Reppy :=
  match c as l return (args l -> Reppy) with
  | TYPEPARAM f => fun P => let '(a; (h; rest)) := P in result (f a h) rest
  | PARAM A f => fun P => let '(a; rest) := P in result (f a) rest
  | INDEX A H f => fun P => let '(a; rest) := P in result (f a) rest
  | ARG A H c => fun P => let '(a, rest) := P in result c rest
  | DEPARG A H f => fun P => let '(a; rest) := P in result (f a) rest
  | RES A H => fun _ => (A; H)
  end xs.

Definition reconstruct (c : code) : Type :=
  forall (P : args c),
  let '(A; _) := result c P in A.


Ltac destruct_through C :=
  match goal with
  | [P : (@sigT (Rep _) _) |- _ ] =>
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
  compute;
  let P := fresh "P" in
  intro P;
  destruct_through C.

Definition reconstructor {T : Type} (x : T) (c : code) :=
  reconstruct c.

Ltac reconstructing :=
  match goal with
  | [ |- reconstructor ?C _ ] => simpl; reconstructing_aux C
  end.



(* EXAMPLES *)
Definition Rep_nat : Rep nat.
  constructor. intros. exact True. Defined.
Definition Rep_list : forall A : Type, Rep A -> Rep (list A).
  intros. constructor. intros. exact True. Defined.

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n : nat, A -> vec A n -> vec A (S n).
Definition Rep_vec : forall (A : Type) (n : nat), Rep A -> Rep (vec A n).
  intros. constructor. intros. exact True. Defined.

Definition S_code : code :=
  @ARG nat Rep_nat (@RES nat Rep_nat).

Definition cons_code : code :=
  @TYPEPARAM (fun A H =>
                @ARG A H
                     (@ARG (list A) (Rep_list A H)
                           (@RES (list A) (Rep_list A H)))).
Goal reconstructor (@cons) cons_code.
  reconstructing. Defined.

Inductive two (A : Type) : Type :=
| mkTwo : A -> A -> two A.

Definition Rep_two : forall (A : Type), Rep A -> Rep (two A).
  intros. constructor. intros. exact True. Defined.
Existing Instance Rep_two.

Definition mkTwo_code : code :=
  @TYPEPARAM (fun A H =>
                @ARG A H (@ARG A H (@RES (two A) (Rep_two A H)))).

Goal reconstructor mkTwo mkTwo_code.
  reconstructing. Defined.

Definition vcons_code : code :=
  @TYPEPARAM (fun A H =>
                @INDEX nat Rep_nat (fun n =>
                                      @ARG A H (@ARG (vec A n) (Rep_vec A n H)
                                                     (@RES (vec A (S n)) (Rep_vec A (S n) H))))).
Goal (reconstructor vcons vcons_code).
  reconstructing. Defined.


(* GENERATION *)
Record constructor_description :=
{ ctor_name : ident;
  ctor_code : code;
  ctor_real : reconstruct ctor_code
}.

Check <%% le %%>.

Definition Reppyish := option ({A : Type & Rep A}).

Axiom TODO : Type.

Definition create_code
           (mut : mutual_inductive_body)
           (one : one_inductive_body)
           (ctor : (ident * term * nat)) : TemplateMonad code :=
  let '(cn, t, arity) := ctor in
  let fix params (xs : context)
                 (base : list (ident * Reppyish) -> code)
                 (ctx : list (ident * Reppyish))
                 : code :=
    match xs with
    | nil => base ctx
    | x :: rest =>
      let n := match binder_name (decl_name x) with
               | nNamed id => id
               | _ => "_" end in
      TYPEPARAM (fun r H => params rest base ((n, Some (r; H)) :: ctx))
    end
  in

  ind_ty (* named_term *) <- DB.undeBruijn (ind_type one) ;;

  let fix indices
          (t : named_term) (remaining_params : nat) (count : nat)
          (base : list (ident * Reppyish) -> code)
          (ctx : list (ident * Reppyish))
          : code :=
    match t with
    | tProd (mkBindAnn nAnon rel) ty rest =>
      if remaining_params then
        indices rest (pred remaining_params) count base ctx
      else
        PARAM TODO (fun r =>
          let new_name := "P" ++ string_of_nat count in
          indices rest (pred remaining_params) (S count) base ((new_name, None) :: ctx))
    | tProd (mkBindAnn (nNamed id) rel) ty rest =>
      if remaining_params then
        indices rest (pred remaining_params) count base ctx
      else
        PARAM TODO (fun r =>
          indices rest (pred remaining_params) (S count) base ((id, None) :: ctx))
    | _ => base ctx
    end in
  let num_of_params := ind_npars mut in

  let fix args (t : named_term) (ctx : list (ident * Reppyish)) : code :=
    @RES Type Rep_Type (* TODO *)
  in
  t' <- DB.undeBruijn' nil t ;;
  let c := params (ind_params mut) (indices ind_ty num_of_params 0 (args t')) in
  ret (c nil).


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
        actual <- tmLemma newName (reconstructor ctor_val code) ;;

        ret {| ctor_name := ctor_name
             ; ctor_code := code
             ; ctor_real := actual
             |}
      end
    end
  | t' => tmPrint t' ;; tmFail "Not a constructor"
  (* | t' => tmPrint t' ;; tmMsg "error" ;; tmFail "" *)
  end.

Notation "$ x" :=
  ((ltac:(let p y := exact y in run_template_program (create_desc x) p)))
  (only parsing, at level 30).

MetaCoq Run (create_desc (@Some)).
Next Obligation.
  reconstructing_aux (@Some).
Defined.

MetaCoq Run (@create_desc (nat -> option nat) (@Some)).
Next Obligation.
  Admitted.


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
