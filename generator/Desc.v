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
Require Import VeriFFI.library.base_representation.
Require Import VeriFFI.library.meta.
Require Import VeriFFI.generator.GraphPredicate.
Require Import VeriFFI.generator.InGraph.

(* Unset MetaCoq Strict Unquote Universe Mode. *)

(* Require Import VeriFFI.generator.InGraph. *)
(* MetaCoq Run (in_graph_gen bool). *)
(* Instance InGraph_bool : InGraph bool. rep_gen. Defined. *)
(* MetaCoq Run (in_graph_gen list). *)
(* Instance InGraph_list : forall A, InGraph A -> InGraph (list A). rep_gen. Defined. *)
(* MetaCoq Run (in_graph_gen nat). *)
(* Instance InGraph_nat : InGraph nat. rep_gen. Defined. *)

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation
       ListNotations
       MetaCoqNotations.

Set Universe Polymorphism.
(* Set Polymorphic Inductive Cumulativity. *)

Fixpoint adjust_context (ctx : list (Kernames.ident * Reppyish)) : TemplateMonad (list (Kernames.ident * named_term)) :=
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

Definition fresh_aname (prefix : string) (a : aname) : TemplateMonad (Kernames.ident * aname) :=
  let x := match binder_name a with | nAnon => prefix | nNamed i => prefix ++ i end in
  x' <- tmFreshName x ;;
  ret (x, {| binder_name := nNamed x'; binder_relevance := binder_relevance a |}).

Definition fill_hole
           (named_ctx : list (Kernames.ident * named_term))
           (goal : named_term)
            : TemplateMonad named_term :=
  (* quantify all the free variables in the goal *)
  let quantified : global_term :=
      fold_left
        (fun tm '(id, ty) => tProd (mkBindAnn (nNamed id) Relevant) ty tm)
        named_ctx goal in
  (* use primitives to infer the type class instance over the global term *)
  tmEval all quantified >>= tmPrint ;;
  hoisted <- instance_term quantified ;;
  (* make function application again to have the same free variables *)
  tmMsg! "hole ctx:" ;;
  tmEval all named_ctx >>= tmPrint! ;;
  let ctx_to_apps : list named_term :=
    rev (map (fun '(id, t) =>
                match t with
                | tApp (tInd {| inductive_mind := kn; inductive_ind := 0 |} _) _ =>
                    if eq_kername kn <? InGraph ?>
                    then tApp <% @field_in_graph %> [hole; tVar id]
                    (* then tApp (tConst (MPfile ["meta"; "library"; "VeriFFI"], "field_in_graph") []) [hole; tVar id] *)
                    else tVar id
                | _ => tVar id
                end) named_ctx) in
  ret (tApp hoisted ctx_to_apps).
  (* ret (strip_lambdas hoisted). *)
  (* ret (tApp hoisted (rev (map (fun '(id, _) => tVar id) named_ctx))). *)

(*
MetaCoq Run (fill_hole [("H", tApp <% InGraph %> [tVar "a"]);("a", <% Type %>)]
                       (tApp <% InGraph %> [tApp <% @list %> [tVar "a"]]) >>= tmEval all >>= tmPrint).
*)

Polymorphic Definition create_reific
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body)
           (ctor : constructor_body) : TemplateMonad (reified ctor_ann) :=
  let cn := cstr_name ctor in
  let t := cstr_type ctor in
  let arity := cstr_arity ctor in
  (* We convert the constructor type to the named representation *)
  let init_index_ctx : list (Kernames.ident  * named_term) :=
      mapi (fun i one => (ind_name one, tInd {| inductive_mind := inductive_mind ind
                                              ; inductive_ind := i |} []))
           (ind_bodies mut) in
  t' <- DB.undeBruijn' (map (fun '(id, _) => nNamed id) init_index_ctx) t ;;

  let fix go
           (* type of the constructor to be taken apart *)
             (t : named_term)
           (* the context kept for De Bruijn indices *)
             (index_ctx : list (Kernames.ident  * named_term))
           (* the context kept for "lambda lifting" the holes *)
             (named_ctx : list (Kernames.ident * named_term))
           (* unprocessed number of parameters left on the type *)
             (num_params : nat) : TemplateMonad named_term :=
      match t, num_params with
      | tProd n (tSort s as t) b , S n' =>
        '(h, H) <- fresh_aname "H" n ;;
        let named_ctx' : list (Kernames.ident * named_term) :=
            match binder_name n with
            | nNamed id => (h, tApp <% @InGraph %> [tVar id]) :: (id, t) :: named_ctx
            | _ => named_ctx end in
        rest <- go b index_ctx named_ctx' (pred num_params) ;;
        let f := tLambda n (tSort s) (tLambda H (tApp <% @ctor_ann %> [tRel O]) rest) in
        ret (tApp <% @TYPEPARAM ctor_ann %> [f])

      | tProd n t b , O =>
        let named_ctx' : list (Kernames.ident * named_term) :=
            match binder_name n with
            | nNamed id => (id, t) :: named_ctx
            | _ => named_ctx end in
        rest <- go b index_ctx named_ctx' O ;;
        let t' := Substitution.named_subst_all index_ctx t in
        let f := tLambda n t' rest in
        H <- fill_hole named_ctx (tApp <% InGraph %> [t']) ;;
        let H' := tApp <% Build_ctor_ann %> [t'; <% present %>; H] in
        ret (tApp <% @ARG ctor_ann %> [t'; H'; f])

      | rest , _ =>
        let rest' := Substitution.named_subst_all index_ctx rest in
        H <- fill_hole named_ctx (tApp <% InGraph %> [rest']) ;;
        let H' := tApp <% Build_ctor_ann %> [rest'; <% present %>; H] in
        ret (tApp <% @RES ctor_ann %> [rest'; H'])
      end
  in

  let num_of_params := ind_npars mut in
  c <- go t' init_index_ctx [] num_of_params ;;
  tmMsg "after go:" ;;
  tmEval all c >>= tmPrint! ;;
  c' <- DB.deBruijn c ;;
  (* tmMsg "after de bruijn:" ;; *)
  (* tmEval all c' >>= tmPrint ;; *)
  tmUnquoteTyped (reified ctor_ann) c'.

Definition desc_gen {T : Type} (ctor_val : T) : TemplateMonad unit :=
  t <- tmQuote ctor_val ;;
  match t with
  | tConstruct ({| inductive_mind := kn ; inductive_ind := mut_tag |} as ind) ctor_tag _ =>
    mut <- tmQuoteInductive kn ;;

    match (nth_error (ind_bodies mut) mut_tag) with
    | None => tmFail "Impossible mutual block index"
    | Some one =>
      match (nth_error (ind_ctors one) ctor_tag) with
      | None => tmFail "Impossible constructor index"
      | Some ctor =>
        reific <- create_reific ind mut one ctor ;;
        (* tmPrint "after create reific" ;; *)
        (* tmEval all reific >>= tmPrint ;; *)

        newName <- tmFreshName "new"%bs ;;
        reflected <- tmLemma newName (@reflector ctor_ann T ctor_val reific) ;;

        let d := {| ctor_name := cstr_name ctor
                  ; ctor_reified := reific
                  ; ctor_reflected := reflected
                  ; ctor_tag := ctor_tag
                  ; ctor_arity := cstr_arity ctor
                  |} in

        name <- tmFreshName (cstr_name ctor ++ "_desc")%bs ;;
        @tmDefinition name (@Desc T ctor_val) {| desc := d |} ;;
        (* Declare the new definition a type class instance *)
        mp <- tmCurrentModPath tt ;;
        tmExistingInstance (ConstRef (mp, name)) ;;
        ret tt
      end
    end
  | t' => tmPrint t' ;; tmFail "Not a constructor"
  end.

Definition descs_gen {kind : Type} (Tau : kind) : TemplateMonad unit :=
  '(env, tau) <- tmQuoteRec Tau ;;
  match declarations (env) with
  | (kn, InductiveDecl decl) :: _ =>
    let each_ctor (mut : mutual_inductive_body)
                  (one : one_inductive_body)
                  (mut_type_count : nat)
                  (ctor_count : nat)
                  (ctor : constructor_body) : TemplateMonad unit :=
      let ind := {| inductive_mind := kn ; inductive_ind := mut_type_count |} in
      t <- tmUnquote (tConstruct ind ctor_count []) ;;
      let '{| my_projT1 := T; my_projT2 := ctor_val |} := t in

      reific <- create_reific ind mut one ctor ;;
      (* tmPrint "after create reific" ;; *)
      (* tmEval all reific >>= tmPrint ;; *)

      newName <- tmFreshName "new"%bs ;;
      reflected <- tmLemma newName (@reflector ctor_ann T ctor_val reific) ;;

      let d := {| ctor_name := cstr_name ctor
                ; ctor_reified := reific
                ; ctor_reflected := reflected
                ; ctor_tag := ctor_count
                ; ctor_arity := cstr_arity ctor
                |} in

      name <- tmFreshName (cstr_name ctor ++ "_desc")%bs ;;
      @tmDefinition name (@Desc T ctor_val) {| desc := d |} ;;
      (* Declare the new definition a type class instance *)
      mp <- tmCurrentModPath tt ;;
      tmExistingInstance (ConstRef (mp, name)) ;;
      ret tt

    in
    let all_in_one (mut : mutual_inductive_body)
                   (mut_type_count : nat)
                   (one : one_inductive_body) : TemplateMonad unit :=
      let ctors := ind_ctors one in
      monad_map_i (each_ctor mut one mut_type_count) (ind_ctors one) ;; ret tt
    in
    let all_in_mut (mut : mutual_inductive_body) : TemplateMonad unit :=
      monad_map_i (all_in_one mut) (ind_bodies mut) ;; ret tt
    in
    all_in_mut decl
  | _ => tmFail "Need an inductive type in the environment"
  end.

Obligation Tactic := reflecting.

Ltac gen :=
  match goal with
  | [ |- @reflector _ _ _ _ ] => reflecting
  | _ => in_graph_gen_tac
  end.

Obligation Tactic := gen.

Unset MetaCoq Strict Unquote Universe Mode.

(* Set Universe Polymorphism. *)
(* Set Polymorphic Inductive Cumulativity. *)

(* MetaCoq Run (in_graph_gen option). *)
(* MetaCoq Run (descs_gen option). *)
(* MetaCoq Run (@desc_gen _ (@None)). *)

(* MetaCoq Run (in_graph_gen unit). *)
(* MetaCoq Run (descs_gen unit). *)

(* MetaCoq Run (in_graph_gen nat). *)
(* MetaCoq Run (descs_gen nat). *)


(* MetaCoq Run (desc_gen tt). *)
(* MetaCoq Run (desc_gen S). *)
(* Set Printing All. *)
(* Print S_desc. *)
(* Check <% tt %>. *)

(* MetaCoq Run (in_graph_gen unit). *)
(* MetaCoq Run (desc_gen tt). *)

(* (* Print new_obligation_1. *) *)
(* MetaCoq Run (descs_gen unit). *)


(* MetaCoq Run (in_graph_gen nat). *)
(* Instance InGraph_ *)
(* (* MetaCoq Run (rep_gen nat). *) *)
(* MetaCoq Run (descs_gen unit). *)
(* MetaCoq Run (desc_gen O). *)
(* Print O_desc. *)

(* MetaCoq Run (desc_gen O >>= @tmDefinition ("O_desc"%string) constructor_description). *)
(* Print S_desc. *)

