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
Require Import VeriFFI.generator.InGraph.
Require Import VeriFFI.generator.Rep.

(*Unset Strict Unquote Universe Mode.*) (* There is no flag or option with this name *)

(* Require Import VeriFFI.generator.Rep. *)
(* MetaCoq Run (in_graph_gen bool). *)
(* Instance Rep_bool : Rep bool. rep_gen. Defined. *)
(* MetaCoq Run (in_graph_gen list). *)
(* Instance Rep_list : forall A, Rep A -> Rep (list A). rep_gen. Defined. *)
(* MetaCoq Run (in_graph_gen nat). *)
(* Instance Rep_nat : Rep nat. rep_gen. Defined. *)

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation
       ListNotations
       MetaCoqNotations.

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
  ret (tApp hoisted (rev (map (fun '(id, _) => tVar id) named_ctx))).

(*
MetaCoq Run (fill_hole [("H", tApp <% Rep %> [tVar "a"]);("a", <% Type %>)]
                       (tApp <% Rep %> [tApp <% @list %> [tVar "a"]]) >>= tmEval all >>= tmPrint).
*)

Definition create_reific
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body)
           (ctor : constructor_body) : TemplateMonad (reific Rep) :=
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
            | nNamed id => (h, tApp <% @Rep %> [tVar id]) :: (id, t) :: named_ctx
            | _ => named_ctx end in
        rest <- go b index_ctx named_ctx' (pred num_params) ;;
        let f := tLambda n (tSort s) (tLambda H (tApp <% @Rep %> [tRel O]) rest) in
        ret (tApp <% @TYPEPARAM Rep %> [f])

      | tProd n t b , O =>
        let named_ctx' : list (Kernames.ident * named_term) :=
            match binder_name n with
            | nNamed id => (id, t) :: named_ctx
            | _ => named_ctx end in
        rest <- go b index_ctx named_ctx' O ;;
        let t' := Substitution.named_subst_all index_ctx t in
        let f := tLambda n t' rest in
        H <- fill_hole named_ctx (tApp <% Rep %> [t']) ;;
        ret (tApp <% @DEPARG Rep %> [t'; H; f])

      | rest , _ =>
        let rest' := Substitution.named_subst_all index_ctx rest in
        H <- fill_hole named_ctx (tApp <% Rep %> [rest']) ;;
        ret (tApp <% @RES Rep %> [rest'; H])
      end
  in

  let num_of_params := ind_npars mut in
  c <- go t' init_index_ctx [] num_of_params ;;
  (* tmMsg "after go:" ;; *)
  (* tmEval all c >>= tmPrint ;; *)
  c' <- DB.deBruijn c ;;
  (* tmMsg "after de bruijn:" ;; *)
  (* tmEval all c' >>= tmPrint ;; *)
  tmUnquoteTyped (reific Rep) c'.

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
        actual <- tmLemma newName (@reconstructor Rep T ctor_val reific) ;;

        let d := {| ctor_name := cstr_name ctor
                  ; ctor_reific := reific
                  ; ctor_real := actual
                  ; ctor_tag := ctor_tag
                  ; ctor_arity := cstr_arity ctor
                  |} in

        tmMsg "Before def" ;;
        d' <- tmEval all d ;;
        tmPrint d' ;;
        name <- tmFreshName (cstr_name ctor ++ "_desc")%bs ;;
        @tmDefinition name (@Desc T ctor_val) {| desc := d' |} ;;
        tmMsg "After def" ;;
        (* Declare the new definition a type class instance *)
        mp <- tmCurrentModPath tt ;;
        tmExistingInstance (ConstRef (mp, name)) ;;
        tmMsg "After inst"
      end
    end
  | t' => tmPrint t' ;; tmFail "Not a constructor"
  end.

(* Definition descs_gen {kind : Type} (Tau : kind) : TemplateMonad unit := *)
(*   '(env, tau) <- tmQuoteRec Tau ;; *)
(*   match declarations (env) with *)
(*   | (kn, InductiveDecl decl) :: _ => *)
(*     let each_ctor (mut_type_count : nat) *)
(*                   (ctor_count : nat) *)
(*                   (ctor : constructor_body) : TemplateMonad unit := *)
(*       t <- tmUnquote (tConstruct {| inductive_mind := kn *)
(*                                   ; inductive_ind := mut_type_count |} *)
(*                                 ctor_count []) ;; *)
(*       t' <- tmEval all (my_projT2 t) ;; *)
(*       (* ty_t' <- tmEval all (my_projT1 t) ;; *) *)
(*       (* let '(ctor_name, _, _) := ctor in *) *)
(*       (* @desc_gen _ t' ctor_name *) *)
(*       @desc_gen _ t' *)
(*     in *)
(*     let all_in_one (mut_type_count : nat) *)
(*                   (one : one_inductive_body) : TemplateMonad unit := *)
(*       let ctors := ind_ctors one in *)
(*       monad_map_i (each_ctor mut_type_count) (ind_ctors one) ;; ret tt *)
(*     in *)
(*     let all_in_mut (mut : mutual_inductive_body) : TemplateMonad unit := *)
(*       monad_map_i all_in_one (ind_bodies mut) ;; ret tt *)
(*     in *)
(*     all_in_mut decl *)
(*   | _ => tmFail "Need an inductive type in the environment" *)
(*   end. *)

Obligation Tactic := reconstructing.

(* Check <% tt %>. *)

(* MetaCoq Run (in_graph_gen unit). *)
(* MetaCoq Run (rep_gen unit). *)
(* MetaCoq Run (desc_gen tt). *)

(* (* Print new_obligation_1. *) *)
(* MetaCoq Run (descs_gen unit). *)


(* MetaCoq Run (in_graph_gen nat). *)
(* Instance Rep_ *)
(* (* MetaCoq Run (rep_gen nat). *) *)
(* MetaCoq Run (descs_gen unit). *)
(* MetaCoq Run (desc_gen O). *)
(* Print O_desc. *)

(* MetaCoq Run (desc_gen O >>= @tmDefinition ("O_desc"%string) constructor_description). *)
(* Print S_desc. *)

