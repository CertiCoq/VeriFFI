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
Require Import VeriFFI.base.
Require Import VeriFFI.generator.rep.

MetaCoq Run (rep_gen Z).

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation
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

(* The type to represent a constructor in an inductive data type.
   The name [reific] stands for "reified inductive constructor".
   Notice how this type uses Gallina binders,
   it is a weak HOAS description of the constructor.
 *)
Inductive reific :=
(* the type parameters in parametric polymorphism, isn't represented immediately in memory,
but the possibility for representation is needed later, e.g., A in [list A]
 *)
 | TYPEPARAM  : (forall (A : Type) `{Rep A}, reific) -> reific
(* Non-type parameters of a fixed type which isn't represented in memory, e.g., n in [n < m] *)
 | PARAM  : forall A : Type, (A -> reific) -> reific
(* index, represented in memory, e.g. the index of a vector *)
 | INDEX  : forall (A : Type) `{Rep A}, (A -> reific) -> reific
 (* non-dependent version of arguments, argument represented in memory, e.g. for X/list X of cons *)
 | ARG : forall (A : Type) `{Rep A}, reific -> reific
 (* dependent argument, represented in memory, e.g. in positive_nat_list *)
 | DEPARG : forall (A : Type) `{Rep A}, (A -> reific) -> reific
(* the end type, e.g., list X for cons : forall X, X -> list X -> **list X** *)
 | RES  : forall (A : Type) `{Rep A}, reific.

(* Makes nested sigmas (i.e. dependent tuples) of all the arguments. *)
Fixpoint args (c : reific) : Type :=
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
Fixpoint result (c: reific) (xs : args c) : Reppy :=
  match c as l return (args l -> Reppy) with
  | TYPEPARAM f => fun P => let '(a; (h; rest)) := P in result (f a h) rest
  | PARAM A f => fun P => let '(a; rest) := P in result (f a) rest
  | INDEX A H f => fun P => let '(a; rest) := P in result (f a) rest
  | ARG A H c => fun P => let '(a, rest) := P in result c rest
  | DEPARG A H f => fun P => let '(a; rest) := P in result (f a) rest
  | RES A H => fun _ => (A; H)
  end xs.

(* Makes a Coq level constructor type from a [reific], with the new type
   taking a nested dependent tuple instead of curried arguments. *)
Definition reconstruct (c : reific) : Type :=
  forall (P : args c),
  let '(A; _) := result c P in A.

(* The same thing as [reconstruct] but takes the actual constructor
   as an argument but "ignores" it. In reality that argument is
   used by the tactic to infer how to reconstruct. *)
Definition reconstructor {T : Type} (x : T) (c : reific) :=
  reconstruct c.

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

(* The entry point to the tactic that solves
   goals like [reconstructor S S_reific]. *)
Ltac reconstructing :=
  match goal with
  | [ |- reconstructor ?C _ ] => simpl; reconstructing_aux C
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
Instance Rep_vec : forall (A : Type) (n : nat), Rep A -> Rep (vec A n).
  intros. constructor. intros. exact True. Defined.

Definition S_reific : reific :=
  @ARG nat Rep_nat (@RES nat Rep_nat).

Definition cons_reific : reific :=
  @TYPEPARAM (fun A H =>
                @ARG A H
                     (@ARG (list A) (Rep_list A H)
                           (@RES (list A) (Rep_list A H)))).
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
Record constructor_description :=
{ ctor_name : BasicAst.ident;
  ctor_reific : reific;
  ctor_real : reconstruct ctor_reific
}.

Definition Reppyish := option ({A : Type & Rep A}).

Fixpoint adjust_context (ctx : list (BasicAst.ident * Reppyish)) : TemplateMonad (list (BasicAst.ident * named_term)) :=
  match ctx with
  | nil => ret nil
  | (id, None) :: xs => adjust_context xs
  | (id, Some (A; H)) :: xs =>
      A' <- tmQuote A ;;
      xs' <- adjust_context xs ;;
      ret ((id, A') :: xs')
  end.

Definition kleisli_compose {m a b c} `{Monad m} : (b -> m c) -> (a -> m b) -> (a -> m c) :=
  fun g f x => f x >>= g.

Definition fresh_aname (prefix : string) (a : aname) : TemplateMonad (BasicAst.ident * aname) :=
  let x := match binder_name a with | nAnon => prefix | nNamed i => prefix ++ i end in
  x' <- tmFreshName x ;;
  ret (x, {| binder_name := nNamed x'; binder_relevance := binder_relevance a |}).

Definition fill_hole
           (named_ctx : list (BasicAst.ident * named_term))
           (goal : named_term)
            : TemplateMonad named_term :=
  (* quantify all the free variables in the goal *)
  let quantified : global_term :=
      fold_left
        (fun tm '(id, ty) => tProd (mkBindAnn (nNamed id) Relevant) ty tm)
        named_ctx goal in
  (* use primitives to infer the type class instance over the global term *)
  hoisted <- instance_term quantified ;;
  (* make function application again to have the same free variables *)
  ret (tApp hoisted (rev (map (fun '(id, _) => tVar id) named_ctx))).

(*
MetaCoq Run (fill_hole [("H", tApp <% Rep %> [tVar "a"]);("a", <% Type %>)]
                       (tApp <% Rep %> [tApp <% @list %> [tVar "a"]]) >>= tmEval all >>= tmPrint).
*)

Definition create_reific
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body)
           (ctor : (BasicAst.ident * term * nat)) : TemplateMonad reific :=
  let '(cn, t, arity) := ctor in
  (* We convert the constructor type to the named representation *)
  let init_index_ctx : list (BasicAst.ident  * named_term) :=
      mapi (fun i one => (ind_name one, tInd {| inductive_mind := inductive_mind ind
                                              ; inductive_ind := i |} []))
           (ind_bodies mut) in
  t' <- DB.undeBruijn' (map (fun '(id, _) => nNamed id) init_index_ctx) t ;;

  let fix go
           (* type of the constructor to be taken apart *)
             (t : named_term)
           (* the context kept for De Bruijn indices *)
             (index_ctx : list (BasicAst.ident  * named_term))
           (* the context kept for "lambda lifting" the holes *)
             (named_ctx : list (BasicAst.ident * named_term))
           (* unprocessed number of parameters left on the type *)
             (num_params : nat) : TemplateMonad named_term :=
      match t, num_params with
      | tProd n (tSort s as t) b , S n' =>
        '(h, H) <- fresh_aname "H" n ;;
        let named_ctx' : list (BasicAst.ident * named_term) :=
            match binder_name n with
            | nNamed id => (h, tApp <% @Rep %> [tVar id]) :: (id, t) :: named_ctx
            | _ => named_ctx end in
        rest <- go b index_ctx named_ctx' (pred num_params) ;;
        let f := tLambda n (tSort s) (tLambda H (tApp <% @Rep %> [tRel O]) rest) in
        ret (tApp <% @TYPEPARAM %> [f])

      | tProd n t b , O =>
        let named_ctx' : list (BasicAst.ident * named_term) :=
            match binder_name n with
            | nNamed id => (id, t) :: named_ctx
            | _ => named_ctx end in
        rest <- go b index_ctx named_ctx' O ;;
        let t' := Substitution.named_subst_all index_ctx t in
        let f := tLambda n t' rest in
        H <- fill_hole named_ctx (tApp <% Rep %> [t']) ;;
        ret (tApp <% @DEPARG %> [t'; H; f])

      | rest , _ =>
        let rest' := Substitution.named_subst_all index_ctx rest in
        H <- fill_hole named_ctx (tApp <% Rep %> [rest']) ;;
        ret (tApp <% @RES %> [rest'; H])
      end
  in

  let num_of_params := ind_npars mut in
  c <- go t' init_index_ctx [] num_of_params ;;
  c' <- DB.deBruijn c ;;
  tmUnquoteTyped reific c'.

Definition create_desc {T : Type} (ctor_val : T) : TemplateMonad constructor_description :=
  t <- tmQuote ctor_val ;;
  match t with
  | tConstruct ({| inductive_mind := kn ; inductive_ind := mut_tag |} as ind) ctor_tag _ =>
    mut <- tmQuoteInductive kn ;;

    match (nth_error (ind_bodies mut) mut_tag) with
    | None => tmFail "Impossible mutual block index"
    | Some one =>
      match (nth_error (ind_ctors one) ctor_tag) with
      | None => tmFail "Impossible constructor index"
      | Some (ctor_name, ctor_type, ctor_arity) =>
        reific <- create_reific ind mut one (ctor_name, ctor_type, ctor_arity) ;;

        newName <- tmFreshName "new"%string ;;
        actual <- tmLemma newName (reconstructor ctor_val reific) ;;

        ret {| ctor_name := ctor_name
             ; ctor_reific := reific
             ; ctor_real := actual
             |}
      end
    end
  | t' => tmPrint t' ;; tmFail "Not a constructor"
  end.

Notation "$ x" :=
  ((ltac:(let p y := exact y in run_template_program (@create_desc _ x) p)))
  (only parsing, at level 30).

Obligation Tactic := reconstructing.

(* MetaCoq Run (create_desc tt >>= tmPrint). *)
(* MetaCoq Run (create_desc S >>= tmPrint). *)
(* MetaCoq Run (create_desc (@Some) >>= tmPrint). *)
(* MetaCoq Run (create_desc (@cons) >>= tmPrint). *)
