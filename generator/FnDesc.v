Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Lists.List
               Coq.Lists.ListSet.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad
               ExtLib.Data.String.

Require Import MetaCoq.Template.All.

Require Import VeriFFI.generator.gen_utils.
Require Import VeriFFI.library.base_representation.
Require Import VeriFFI.library.meta.
Require Import VeriFFI.library.modelled.
Require Import VeriFFI.generator.GraphPredicate.
Require Import VeriFFI.generator.InGraph.

(*
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
  tmMsg "hole ctx:" ;;
  tmEval all named_ctx >>= tmPrint ;;
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

Polymorphic Definition create_reified
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body)
           (ctor : constructor_body) : TemplateMonad (reified foreign_ann) :=
  (* let cn := cstr_name ctor in *)
  (* let t := cstr_type ctor in *)
  (* let arity := cstr_arity ctor in *)
  (* (* We convert the constructor type to the named representation *) *)
  (* let init_index_ctx : list (Kernames.ident  * named_term) := *)
  (*     mapi (fun i one => (ind_name one, tInd {| inductive_mind := inductive_mind ind *)
  (*                                             ; inductive_ind := i |} [])) *)
  (*          (ind_bodies mut) in *)
  (* t' <- DB.undeBruijn' (map (fun '(id, _) => nNamed id) init_index_ctx) t ;; *)

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
  tmEval all c >>= tmPrint ;;
  c' <- DB.deBruijn c ;;
  (* tmMsg "after de bruijn:" ;; *)
  (* tmEval all c' >>= tmPrint ;; *)
  tmUnquoteTyped (reified ctor_ann) c'.

Print tmQuote.
Print constant_body.

Definition fn_desc_gen
           {T1 T2 : Type}
           (model_val : T1) (foreign_val : T2)
           (c_name : string) : TemplateMonad unit :=
  model_t <- tmQuote model_val ;;
  foreign_t <- tmQuote foreign_val ;;
  match model_t , foreign_t with
  | tConst model_kn _ , tConst foreign_kn _ =>
    if ident_eq (snd model_kn) (snd foreign_kn)
      then tmMsg "Warning: functional model and foreign function names are different"
      else ret tt ;;
        
    reified <- create_reified model_t foreign_t ;;
    (* tmPrint "after create reified" ;; *)
    (* tmEval all reified >>= tmPrint ;; *)

    newName <- tmFreshName "new"%bs ;;
    reflected <- tmLemma newName (@reflector foreign_ann T2 foreign_val reified) ;;

    let d := {| type_desc := reified
              ; foreign_fn := foreign_val
              ; model_fn := reflected
              ; fn_arity := _
              ; c_name := c_name
              |} in

    name <- tmFreshName (snd foreign_kn ++ "_desc")%bs ;;
    @tmDefinition name fn_desc d ;;
    (* Declare the new definition a type class instance *)
    (* mp <- tmCurrentModPath tt ;; *)
    (* tmExistingInstance export (ConstRef (mp, name)) ;; *)
    ret tt
  | _ , _ =>
    tmFail "Need two constant definitions in the environment"
  end.

Local Obligation Tactic := reflecting.

Ltac gen :=
  match goal with
  | [ |- @reflector _ _ _ _ ] => reflecting
  | _ => in_graph_gen_tac
  end.

Local Obligation Tactic := gen.

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


*)
