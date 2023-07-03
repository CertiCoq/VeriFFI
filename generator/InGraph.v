(*
  Author: Joomy Korkut (joomy@cs.princeton.edu), 2020-2022

  Generator for the [is_in_graph] relation for a given Coq type.

  The [is_in_graph] function should match on a Coq value of a given type,
  and check if a C value represents that Coq value
  the same way CertiCoq represents it.

  This is similar to the pattern in VST but instead of [A -> val -> mpred],
  our [is_in_graph] function has the type [graph -> A -> rep_type -> Prop],
  for a given [A].

  This file defines a MetaCoq program that generates a [InGraph] instance
  for a given Coq type.

  Currently our generator works on:
  [x] simple types like [bool]
  [x] recursive types like [nat]
  [x] polymorphic types like [option]
  [x] multi-polymorphic types like [pair]
  [x] recursive and polymorphic types like [list]
  [ ] recursive and dependent types like [fin]
  [ ] recursive, polymorphic and dependent types like [vector]
  [x] mutually recursive types like [tree] and [forest]
  [ ] mutually recursive and dependent types like [even] and [odd]
  [ ] nested types
  [ ] types of sort Prop like [True], [and] or [le]
  [ ] types that use functions in its definition

  Game plan:
  * Take a type constructor (in Coq, not reified) as an input.
  * Recursively quote the type constructor, get a type environment as well.
  * The type environment consists of mutual inductive type declarations.
  * For every type in every mutual block,
    find out if there is a [InGraph] instance for it,
    and remember it in a list of lists.
    * In order to find out the [InGraph] instance, you have to
      quantify over all parameters and indices.
  * If a block is missing any instance,
    define type class instances for each type in the block.

  Caveats:
  * If a type is of sort [Prop], the representation of its values is
    the same as [unit] for all values.
  * Parameters are not included in the memory representation,
    indices are. But parameters should be quantified over in the [InGraph] instance type.
*)
Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Lists.List
               Coq.Lists.ListSet.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad.

From MetaCoq.Template Require Import BasicAst.
Require Import MetaCoq.Template.All.

Require Import VeriFFI.generator.gen_utils.
Require Import VeriFFI.library.base_representation.
Require Import VeriFFI.library.meta.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation
       ListNotations
       MetaCoqNotations.

Notation "f >=> g" := (fun x => (f x) >>= g)
                      (at level 51, right associativity) : monad_scope.
Notation "f <$> x" := (x' <- x%monad ;; ret (f x'))
                      (at level 52, right associativity) : monad_scope.
Open Scope bs.

(* These lines below are for debugging. There are lines in the generator for
   print debugging. We don't want to remove them all, but also we don't want them
   to run when we are generating things as usual. So we overload the print
   debugging functions with things that don't execute. *)
Notation "'tmPrint!'" := (tmPrint).
Notation "'tmMsg!'" := (tmMsg).
(* Notation "'tmPrint'" := (tmPrint). *)
(* Notation "'tmMsg'" := (tmMsg). *)
Notation "'tmPrint'" := (fun _ => ret tt).
Notation "'tmMsg'" := (fun _ => ret tt).

#[export] Instance InGraph_Prop : InGraph Prop :=
  {| is_in_graph g x p := graph_cRep g p (enum 0) [] |}.
#[export] Instance InGraph_Set : InGraph Set :=
  {| is_in_graph g x p := graph_cRep g p (enum 0) [] |}.
#[export] Instance InGraph_Type : InGraph Type :=
  {| is_in_graph g x p := graph_cRep g p (enum 0) [] |}.

(* Starting generation of [InGraph] instances! *)

Section Argumentation.

  Variant arg_variant : Type :=
  | param_arg : forall (param_name : ident) (param_type : named_term), arg_variant
  | value_arg : forall (arg_name exists_name : ident) (arg_type : named_term), arg_variant.

  (* Takes the identifying information for a single inductive type
     in a mutual block, a constructor for that type,
     and generates the list of arguments and the [named_term]
     that is possibly using those argument names. *)
  Definition argumentation
             (ind : inductive)
             (mut : mutual_inductive_body)
             (ctor : ctor_info) : TemplateMonad (list arg_variant * named_term) :=
    let number_of_params : nat := ind_npars mut in
    (* The type names are referred with de Bruijn indices
       so we must add them to the initial context. *)
    let mp : modpath := fst (inductive_mind ind) in
    let kn : kername := inductive_mind ind in
    (* We need two passes here,
       - one to replace the type references to globally unique [ident]s
       - another to substitute those [ident]s into terms referring to those types,
         so that later when we encounter the [tInd] we know which [InGraph] instance to call.
     *)
    let mut_names : list ident :=
        map (fun one => "$$$" ++ string_of_kername (mp, ind_name one)) (ind_bodies mut) in
    let mut_ind_terms : list (ident * global_term) :=
        mapi (fun i one =>
                let id := "$$$" ++ string_of_kername (mp, ind_name one) in
                let ind := mkInd kn i in
                (id, tInd ind nil))
            (ind_bodies mut) in

    let fix aux (params : nat) (* number of parameters left *)
                (arg_count : nat) (* number of args seen *)
                (ctx : list ident) (* names of params and args to be used *)
                (t : term) (* what is left from the constructor type *)
                {struct t}
                : TemplateMonad (list arg_variant * named_term) :=
      match params, t with
      (* Go through the params *)
      | S params', tProd n t b =>
        match n with
        | mkBindAnn (nNamed id) _ =>
          '(args, rest) <- aux params' arg_count (id :: ctx) b ;;
          t' <- DB.undeBruijn' (map nNamed ctx) t ;;
          let t' := Substitution.named_subst_all mut_ind_terms t' in
          ret (param_arg id t' :: args, rest)
        | _ => tmFail "Impossible: unnamed param"
        end
      | S _ , _ => tmFail "Impossible: all constructors quantify over params"

      (* Other arguments *)
      | O , tProd n t b =>
        let arg_name : ident := "arg" ++ string_of_nat arg_count in
        let exists_name : ident := "p" ++ string_of_nat arg_count in
        '(args, rest) <- aux O (S arg_count) (arg_name :: ctx) b ;;
        t' <- DB.undeBruijn' (map nNamed ctx) t ;;
        let t' := Substitution.named_subst_all mut_ind_terms t' in
        ret (value_arg arg_name exists_name t' :: args, rest)
      | O, t =>
        (* rename variables in the root *)
        t' <- DB.undeBruijn' (map nNamed ctx) t ;;
        let t' := Substitution.named_subst_all mut_ind_terms t' in
        ret (nil , t')
      end in

    aux number_of_params O (rev mut_names) (ctor_type ctor).

End Argumentation.

Definition is_sort : Type := bool.
Definition check_sort (t : any_term) : is_sort :=
  match t with tSort _ => true | _ => false end.
Definition is_param : Type := bool.

(* Takes the identifying information for a single inductive type
   in a mutual block, and generates a type for the whole block.
   This is a function that will be used to generate the type of the new [InGraph] instance,
   for which the [type_quantifier] adds a [InGraph] instance argument.
   This function can also be used to get a fully applied [named_term] and its quantifiers.
   The quantifiers would go around the [is_in_graph] function and the [InGraph] instance.
*)
Definition generate_instance_type
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body)
           (type_quantifier : ident -> named_term -> named_term)
           (replacer : named_term -> named_term) : TemplateMonad named_term :=
  (* Convert the type of the type to explicitly named representation *)
  ty <- DB.undeBruijn (ind_type one) ;;
  let num_of_params := ind_npars mut in
  (* Goes over a nested π-type and collects binder names,
     makes up a name where there isn't one.
     It also builds a function to replace the part after the π-binders. *)
  let fix collect
          (t : named_term) (remaining_params : nat) (count : nat) (replacer : named_term -> named_term)
          : list (ident * is_param * is_sort) * (named_term -> named_term) :=
    match t with
    | tProd (mkBindAnn nAnon rel) ty rest =>
        let '(idents, f) := collect rest (pred remaining_params) (S count) replacer in
        let new_name := "P" ++ string_of_nat count in
        let this_is_param := if remaining_params then false else true in
        ((new_name, this_is_param, check_sort ty) :: idents,
         (fun t' => tProd (mkBindAnn (nNamed new_name) rel) ty (f t')))
    | tProd (mkBindAnn (nNamed id) rel) ty rest =>
        let '(idents, f) := collect rest (pred remaining_params) (S count) replacer in
        let this_is_param := if remaining_params then false else true in
        ((id, this_is_param, check_sort ty) :: idents,
         (fun t' => tProd (mkBindAnn (nNamed id) rel) ty (f t')))
    | _ => (nil, replacer)
    end in
  let (quantified, new) := collect ty num_of_params O replacer in

  (* Check if there are any non-parameter type arguments *)
  monad_map (fun '(n,p,s) =>
              match p, s with
              | false, true =>
                tmFail "Our system cannot generate representation relations for types that use type arguments in non-parameter positions."
              | _ , _ => ret tt
              end) quantified ;;
  let names := map (fun '(n,_,_) => n) quantified in
  let vars := map tVar names in
  let type_quantifiers := map (fun '(n,_,_) => n) (filter (fun '(_,p,s) => andb p s) quantified) in
  let base := tApp (tInd ind []) vars in

  (* Fully apply the quantified type constructor.
     If you had [list] initially, now you have [forall (A : Type), list A] *)
  let result := new (fold_right type_quantifier base type_quantifiers) in
  ret result.

Fixpoint apply_to_pi_base (f : term -> term) (t : term) : term :=
  match t with
  | tProd b t body => tProd b t (apply_to_pi_base f body)
  | _ => f t
  end.

(* Checks if the given type class instance type has an instance.
   This wrapper function makes type checking easier
   since [tmInferInstance] is dependently typed but we don't need that now. *)
Definition has_instance (A : Type) : TemplateMonad bool :=
  opt_ins <- tmInferInstance (Some all) A ;;
  ret (match opt_ins with | my_Some _ => true | my_None => false end).

Definition generate_InGraph_instance_type
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad named_term :=
  generate_instance_type ind mut one
    (fun ty_name t =>
      let n := "InGraph_" ++ ty_name in
      tProd (mkBindAnn (nNamed n) Relevant) (tApp <% InGraph %> [tVar ty_name]) t)
    (fun t => apply_to_pi_base (fun t' => tApp <% InGraph %> [t']) t).

(* Constructs the instance type for the type at hand,
   checks if there's an instance for it. *)
Definition find_missing_instance
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad bool :=
  tmMsg! ("Missing: " ++ string_of_inductive ind) ;;
  generate_InGraph_instance_type ind mut one >>=
  DB.deBruijn >>= tmUnquoteTyped Type >>= has_instance.

(* Take in a [global_declarations], which is a list of declarations,
   and find the inductive declarations in that list
   that do not have [InGraph] instances. *)
Fixpoint find_missing_instances
        (env : global_declarations) : TemplateMonad (list kername) :=
    match env with
    | (kn, InductiveDecl mut) :: env' =>
      rest <- find_missing_instances env' ;;
      ones <- monad_map_i
                (fun i => find_missing_instance
                            {| inductive_mind := kn ; inductive_ind := i |} mut)
                (ind_bodies mut) ;;
      if (fold_left andb ones true) (* if there are instances for all *)
        then ret rest (* then this one is not missing *)
        else ret (kn :: rest)
    | _ :: env' => find_missing_instances env'
    | nil =>
      tmMsg "End of missings" ;;
      ret nil
    end.

Definition get_ty_info_from_inductive
           (ind : inductive) : TemplateMonad ty_info :=
  mut <- tmQuoteInductive (inductive_mind ind) ;;
  match nth_error (ind_bodies mut) (inductive_ind ind) with
  | None => tmFail "Wrong index for the mutual inductive block"
  | Some one =>
      params <- monad_map (fun c => match decl_name c with
                           | mkBindAnn nAnon _ => tmFail "Unnamed inductive type parameter"
                           | mkBindAnn (nNamed n) _ => ret n
                           end) (ind_params mut) ;;
      ret {| ty_name := inductive_mind ind
           ; ty_body := one
           ; ty_inductive := ind
           ; ty_params := params
           |}
  end.

(* Get the [ty_info] for the first type in the mutual block. *)
Definition get_ty_info
           (kn : kername) : TemplateMonad ty_info :=
  get_ty_info_from_inductive {| inductive_mind := kn ; inductive_ind := 0 |}.

Definition get_one_from_inductive
           (ind : inductive) : TemplateMonad one_inductive_body :=
  ty_body <$> get_ty_info_from_inductive ind.


Definition make_tInd (ind : inductive) : global_term :=
  tInd ind [].

Fixpoint make_lambdas
         (args : list arg_variant)
         : named_term -> named_term :=
  match args with
  | value_arg arg_name _ nt :: args' =>
    fun x => tLambda (mkBindAnn (nNamed arg_name) Relevant)
                     nt
                     (make_lambdas args' x)
  | _ :: args' => fun x => make_lambdas args' x
  | _ => fun x => x
  end.

(* MetaCoq's [bcontext] expects the context from last to first,
   so we have to reverse it. *)
Definition make_bcontext
           (args : list arg_variant)
           : list aname :=
  let fix aux (args : list arg_variant) : list aname :=
    match args with
    | value_arg arg_name _ nt :: args' =>
      (mkBindAnn (nNamed arg_name) Relevant) :: aux args'
    | _ :: args' => aux args'
    | _ => []
    end
  in rev (aux args).

Fixpoint make_exists
         (args : list arg_variant)
         : named_term -> named_term :=
  match args with
  | value_arg _ p_name nt :: args' =>
    fun x => tApp <% ex %>
                  [ <% rep_type %>
                  ; tLambda (mkBindAnn (nNamed p_name) Relevant)
                            <% rep_type %>
                            (make_exists args' x) ]
  | _ :: args' => fun x => make_exists args' x
  | _ => fun x => x
  end.


(* Special helper functions to make lists consisting of [rep_type] values *)
Definition t_cons (t : any_term) (t' : any_term) : any_term :=
  tApp <% @cons %> [<% rep_type %> ; t ; t'].
Definition t_conses (xs : list any_term) : any_term :=
  fold_right t_cons <% @nil rep_type %> xs.
Definition t_and (t : any_term) (t' : any_term) : any_term :=
  tApp <% @and %> [t ; t'].

(* [tmInferInstance] can create some type checking error
   but this definition solves it for some reason. *)
Polymorphic Definition tmInferInstanceEval (t : Type) := tmInferInstance (Some all) t.

(* Takes in a term representing a type like [forall A, InGraph (list A)]),
   and finds the type class instance for that. *)
Definition instance_term (inst_ty : named_term) : TemplateMonad named_term :=
  tmMsg "instance_term1:" ;;
  inst_ty' <- DB.deBruijn inst_ty >>= tmUnquoteTyped Type ;;
  tmMsg "instance_term:" ;;
  tmEval all inst_ty' >>= tmPrint ;;
  opt_ins <- tmInferInstanceEval inst_ty' ;;
  match opt_ins with
  | my_Some x => tmQuote x >>= DB.undeBruijn
  | _ => tmMsg! "No instance of type" ;;
         tmEval all inst_ty >>= tmPrint! ;;
         tmFail "No such instance"
  end.

(* Remove all the initial consecutive π-type quantifiers from a [term]. *)
Fixpoint strip_quantifiers (t : named_term) : named_term :=
  match t with
  | tProd _ _ rest => strip_quantifiers rest
  | x => x
  end.

(* Remove all the initial consecutive λ-type quantifiers from a [term]. *)
Fixpoint strip_lambdas (t : named_term) : named_term :=
  match t with
  | tLambda _ _ rest => strip_lambdas rest
  | x => x
  end.

(* Remove a given number of initial consecutive λ-type quantifiers from a [term]. *)
Fixpoint strip_n_lambdas (n : nat) (t : named_term) : named_term :=
  match n , t with
  | S n' , tLambda _ _ rest => strip_n_lambdas n' rest
  | _ , _ => t
  end.

(* Get binder names and binding types for all
   initial consecutive π-type quantifiers in a [named_term]. *)
Fixpoint get_quantifiers
         (modify : ident -> ident)
         (t : named_term) : list (aname * named_term) :=
  match t with
  | tProd (mkBindAnn nAnon rel) ty rest =>
    (mkBindAnn nAnon rel, ty) :: get_quantifiers modify rest
  | tProd (mkBindAnn (nNamed id) rel) ty rest =>
    (mkBindAnn (nNamed (modify id)) rel, ty) :: get_quantifiers modify rest
  | _ => nil
  end.

(* Given binder names and binding types, add binders to the base [named_term].
   Can be used to add λs (with [tLambda]) or πs (with [tProd]). *)
Fixpoint build_quantifiers
         (binder : aname -> named_term -> named_term -> named_term)
         (l : list (aname * named_term))
         (base : named_term) : named_term :=
  match l with
  | nil => base
  | (n, t) :: rest => binder n t (build_quantifiers binder rest base)
  end.

Definition make_arg (x : aname * named_term) : named_term :=
  match x with
  | (mkBindAnn (nNamed id) _ , _) => tVar id
  | _ => <% False %>
  end.

Definition build_inst_call
           (all_single_rep_tys : list (aname * named_term))
           (quantifiers : list (aname * named_term))
           (ind : inductive)
           (nt : named_term) : TemplateMonad named_term :=
  let args := (all_single_rep_tys ++ quantifiers)%list in
  let quantified := build_quantifiers tProd args (tApp <% InGraph %> [nt]) in
  quantified <- tmEval all quantified ;;
  tmMsg "==========" ;;
  (* tmMsg "FOR:" ;; *)
  (* tmPrint nt ;; *)
  (* tmMsg "QUANTIFIED:" ;; *)
  (* tmPrint quantified ;; *)
  tmEval all quantified >>= tmPrint ;;
  t <- instance_term quantified ;;
  (* NOTE: could this ever be a problem?
           is it possible for the fake [___InGraph]s to come eta reduced? *)
  let t := tApp (strip_n_lambdas (length all_single_rep_tys) t)
                (map make_arg quantifiers) in
  tmEval cbn t.

Definition build_method_call
           (all_single_rep_tys : list (aname * named_term))
           (quantifiers : list (aname * named_term))
           (ind : inductive)
           (nt : named_term) : TemplateMonad named_term :=
  InGraph_call <- build_inst_call all_single_rep_tys quantifiers ind nt ;;
  res <-
    match InGraph_call with
    | tApp (tVar n) rest =>
      if bytestring.String.prefix "___InGraph" n
      then
        let num : string := bytestring.String.substring 10 13 n in
        ret (tApp (tVar ("is_in_graph" ++ num)) (map make_arg quantifiers))
        (* ret (tVar ("is_in_graph" ++ num)) *)
      else
        ret (tApp <% @is_in_graph %> [nt ; InGraph_call])
    | _ =>
      ret (tApp <% @is_in_graph %> [nt ; InGraph_call])
    end ;;
  res <- tmEval all res ;;
  tmMsg "build_method_call :" ;;
  tmEval all quantifiers >>= tmPrint ;;
  tmPrint res ;;
  ret res.

Definition make_prop
         (all_single_rep_tys : list (aname * named_term))
         (quantifiers : list (aname * named_term))
         (ind : inductive)
         (one : one_inductive_body)
         (ctor : ctor_info)
         (args : list arg_variant)
         : TemplateMonad named_term :=
  let t_g := tVar "g" in
  let t_p := tVar "p" in

  let make_prop_base : TemplateMonad named_term :=
    (* Create the [cRep] for this constructor and evaluate *)
    crep <- tmEval all
              (match gen_utils.ctor_arity ctor with
                | O => enum (N.of_nat (ctor_ordinal ctor))
                | a => boxed (N.of_nat (ctor_ordinal ctor)) (N.of_nat a)
                end) ;;
    t_crep <- tmQuote crep ;;
    (* Create list of [[p0;p1;p2;...]] to pass to [graph_cRep] *)
    let l := t_conses (map (fun n => tVar ("p" ++ string_of_nat n))
                           (seq 0 (gen_utils.ctor_arity ctor))) in
    ret (tApp <% graph_cRep %>
              [ t_g ; t_p ; t_crep ; l])
  in


  (* Takes in the [arg_variant],
     generates the call to [is_in_graph] for that argument.
     Returns a list so that [param_arg] can return a empty list. *)
  let make_arg_prop (i : nat) (arg : arg_variant) : TemplateMonad (list named_term) :=
    tmMsg ("ARG_PROP #" ++ string_of_nat i ++ ":") ;;
    match arg with
      | value_arg arg_name p_name nt =>
        (* tmMsg "HERE'S ONE!" ;; *)
        let t_arg := tVar arg_name in
        let t_p := tVar p_name in
        call <- build_method_call all_single_rep_tys quantifiers ind nt ;;
        tmMsg "IS IN GRAPH CALL: " ;;
        tmEval all nt >>= tmPrint ;;
        tmEval all call >>= tmPrint ;;
        ret [tApp call [ t_g ; t_arg; t_p ]]
      | _ => ret nil
    end
  in
  arg_props <- monad_map_i make_arg_prop args ;;
  tmMsg "==== END OF make_arg_props ====" ;;
  (* tmMsg "arg_props:" ;; *)
  (* tmEval all arg_props >>= tmPrint ;; *)
  base <- make_prop_base ;;
  ret (fold_right t_and base (concat arg_props)).

(* Takes in the info for a single constructor of a type, generates the branches
   of a match expression for that constructor. *)
Definition ctor_to_branch
    (all_single_rep_tys : list (aname * named_term))
      (* names and types of all [is_in_graph_i] functions in the fix block *)
    (quantifiers : list (aname * named_term))
      (* all quantifiers for this type *)
    (ind : inductive)
      (* the type we're generating for *)
    (one : one_inductive_body)
      (* the single type we're generating for *)
    (tau : term)
      (* reified term of the type we're generating for *)
    (ctor : ctor_info)
      (* a single constructor to generate for *)
    : TemplateMonad (branch named_term) :=
  let kn : kername := inductive_mind ind in
  mut <- tmQuoteInductive kn ;;
  let ctx : list dissected_type :=
      mapi (fun i _ => dInd {| inductive_mind := kn ; inductive_ind := i |})
           (ind_bodies mut) in
  params <- ty_params <$> get_ty_info (inductive_mind ind) ;;
  mut <- tmQuoteInductive (inductive_mind ind) ;;
  '(args, res) <- argumentation ind mut ctor ;;

  (* tmMsg "ARGS:" ;; *)
  (* tmEval all args >>= tmPrint ;; *)

  (* TODO these are the quantifiers for the entire type? not just this branch *)
  prop <- make_prop all_single_rep_tys quantifiers ind one ctor args ;;
  (* tmMsg "PROP:" ;; *)
  (* tmEval all t >>= tmPrint ;; *)
  ret {| bcontext := make_bcontext args
       ; bbody := make_exists args prop
       |}.

(* For sort parameters we have to skip 2 quantifiers,
   one for the param itself, one for the [InGraph] instance.
   For all other parameters we can just skip one. *)
Fixpoint count_quantifiers_to_skip (xs : context) : nat :=
  match xs with
  | x :: xs' =>
    (if check_sort (decl_type x) then 2 else 1) + count_quantifiers_to_skip xs'
  | nil => 0
  end.

(* Check <% fun A => fun xs : list A => match xs with nil => true | cons y ys => false end %>. *)
(* Generates a reified match expression *)
Definition matchmaker
    (all_single_rep_tys : list (aname * named_term))
      (* names and types of all [is_in_graph_i] functions in the fix block *)
    (quantifiers : list (aname * named_term))
      (* all quantifiers for this type *)
    (ind : inductive)
      (* description of the type we're generating for *)
    (mut : mutual_inductive_body)
      (* the mutual type we're generating for *)
    (one : one_inductive_body)
      (* the single type we're generating for *)
    (tau : term)
      (* reified term of the type we're generating for *)
    (ctors : list ctor_info)
      (* constructors we're generating match branches for *)
    : TemplateMonad named_term :=
  branches <- monad_map (ctor_to_branch all_single_rep_tys quantifiers ind one tau) ctors ;;
  let params : list named_term :=
    @map _ _ (fun cd => match binder_name (decl_name cd) with
                        | nAnon => hole | nNamed id => tVar id end)
    (ind_params mut) in
  ret (tCase {| ci_ind := ind
              ; ci_npar := 0
              ; ci_relevance := Relevant
              |}
             {| puinst := []
              ; pparams := params
              ; pcontext := [{| binder_name := nNamed "x"; binder_relevance := Relevant |}]
              ; preturn := <% Prop %>
              |}
             (tVar "x")
             branches).

(* Make a single record to use in a [tFix].
   For mutually inductive types, we want to build them all once,
   and define all the [InGraph] instances with that. *)
Definition make_fix_single
           (all_single_rep_tys : list (aname * named_term))
           (quantifiers : list (aname * named_term))
           (tau : named_term) (* fully applied type constructor *)
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad (BasicAst.def named_term) :=
  let this_name := nNamed ("is_in_graph" ++ string_of_nat (inductive_ind ind)) in
  prop <- matchmaker all_single_rep_tys quantifiers ind mut one tau (process_ctors (ind_ctors one)) ;;
  let ty :=
      tProd (mkBindAnn (nNamed "g") Relevant) <% graph %>
        (tProd (mkBindAnn (nNamed "x") Relevant) tau
          (tProd (mkBindAnn (nNamed "p") Relevant) <% rep_type %> <% Prop %>)) in
  let body :=
      tLambda (mkBindAnn (nNamed "g") Relevant) <% graph %>
        (tLambda (mkBindAnn (nNamed "x") Relevant) tau
          (tLambda (mkBindAnn (nNamed "p") Relevant) <% rep_type %> prop)) in
  ret {| dname := mkBindAnn this_name Relevant
       ; dtype := build_quantifiers tProd quantifiers ty
       ; dbody := build_quantifiers tLambda quantifiers body
       ; rarg := 1 + length quantifiers |}.

Definition singles_tys (kn : kername)
                       (mut : mutual_inductive_body)
                       : TemplateMonad (list (aname * named_term)) :=
  monad_map_i
    (fun i one =>
      (* FIXME get rid of repeated computation here *)
      let ind := {| inductive_mind := kn ; inductive_ind := i |} in
      quantified <- generate_instance_type ind mut one
                      (fun ty_name t =>
                        let n := "InGraph_" ++ ty_name in
                        tProd (mkBindAnn (nNamed n) Relevant) (tApp <% InGraph %> [tVar ty_name]) t)
                      (fun t => apply_to_pi_base (fun t' => tApp <% InGraph %> [t']) t) ;;
      (* tmMsg "quantified:" ;; *)
      quantified <- tmEval all quantified ;;
      (* ___InGraph0, ___InGraph1 etc. are fake instances,
          gotta replace their usage with calls to is_in_graph0, is_in_graph1 etc later. *)
      let an := mkBindAnn (nNamed ("___InGraph" ++ string_of_nat i)) Relevant in
      ret (an, quantified))
    (ind_bodies mut).

Definition singles (kn : kername)
                   (mut : mutual_inductive_body)
                   (singles_tys : list (aname * named_term))
                   : TemplateMonad (list (def named_term)) :=
  monad_map_i
    (fun i one =>
      (* FIXME get rid of repeated computation here *)
      let ind := {| inductive_mind := kn ; inductive_ind := i |} in
      quantified <- generate_instance_type ind mut one
                      (fun ty_name t =>
                        let n := "InGraph_" ++ ty_name in
                        tProd (mkBindAnn (nNamed n) Relevant) (tApp <% InGraph %> [tVar ty_name]) t)
                        id ;;
      (* tmMsg "quantified:" ;; *)
      (* tmEval all quantified >>= tmPrint ;; *)
      let quantifiers := get_quantifiers id quantified in
      let tau := strip_quantifiers quantified in
      make_fix_single singles_tys quantifiers tau {| inductive_mind := kn ; inductive_ind := i |} mut one)
    (ind_bodies mut).

(* This gives us something like [forall (A : Type) (n : nat), vec A n] *)
Definition quantified ind mut one (inst_prefix: string) (inst: global_term) :=
  generate_instance_type ind mut one
    (fun ty_name t =>
      let n := inst_prefix ++ ty_name in
      tProd (mkBindAnn (nNamed n) Relevant) (tApp inst [tVar ty_name]) t)
    id.

Definition add_instances_aux (kn : kername)
                   (mut : mutual_inductive_body)
                   (singles_tys : list (aname * named_term))
                   (singles: list (def named_term)) : TemplateMonad _ :=
  monad_map_i
    (fun i one =>
       let ind := {| inductive_mind := kn ; inductive_ind := i |} in
       quantified <- quantified ind mut one "InGraph_" <% InGraph %> ;;
       (* Now what can we do with this? *)
       (*    Let's start by going to its named representation. *)
       (* The reified type of the fully applied type constructor, *)
       (*    but with free variables! *)
       let tau := strip_quantifiers quantified in
       let fn_ty := tProd (mkBindAnn (nNamed "g") Relevant)
                          <% graph %>
                          (tProd (mkBindAnn (nNamed "x") Relevant)
                                 hole
                                 (tProd (mkBindAnn (nNamed "p") Relevant)
                                        <% rep_type %>
                                        <% Prop %>)) in
       let quantifiers : list (aname * named_term) :=
           get_quantifiers id quantified in
       args_let <- monad_map (fun '(an, _) =>
                                match an with
                                | mkBindAnn (nNamed n) _ => ret (tVar n)
                                | _ => tmFail "Unnamed parameter"
                                end) quantifiers ;;
       let fn : named_term :=
           tLetIn (mkBindAnn (nNamed "f") Relevant)
                  (tFix singles i)
                  (build_quantifiers tProd quantifiers fn_ty)
                  (tApp (tVar "f") args_let) in
       let prog_named : named_term :=
           build_quantifiers tLambda quantifiers
                             (tApp <% @Build_InGraph %>
                                   [tau; fn]) in
       prog <- DB.deBruijn prog_named ;;
       extra_quantified <- DB.deBruijn (build_quantifiers tProd quantifiers
                                                          (tApp <% InGraph %> [tau])) ;;
       tmMsg "Extra Quantified:" ;;
       tmEval all extra_quantified >>= tmPrint ;;
       instance_ty <- tmUnquoteTyped Type extra_quantified ;;
       tmMsg "Prog" ;;
       prog' <- tmEval all prog ;;
       tmPrint prog';;
       instance <- tmUnquote prog' ;;
       (* tmMsg "Inst" ;; *)
       (* tmPrint instance ;; *)
       (* Remove [tmEval] when MetaCoq issue 455 is fixed: *)
       (* https://github.com/MetaCoq/metacoq/issues/455 *)
       name <- tmFreshName =<< tmEval all ("InGraph_" ++ ind_name one)%bs ;;

       (* (* This is sort of a hack. I couldn't use [tmUnquoteTyped] above *)
       (*    because of a mysterious type error. (Coq's type errors in monadic *)
       (*    contexts are just wild.) Therefore I had to [tmUnquote] it to get *)
       (*    a Σ-type. But when you project the second field out of that, *)
       (*    the type doesn't get evaluated to [InGraph _], it stays as *)
       (*    [my_projT2 {| ... |}]. The same thing goes for the first projection, *)
       (*    which is the type of the second projection. When the user prints *)
       (*    their [InGraph] instance, Coq shows the unevaluated version. *)
       (*    But we don't want to evaluate it [all] the way, that would unfoldd *)
       (*    the references to other instances of [InGraph]. We only want to get *)
       (*    the head normal form with [hnf]. *)
       (*    We have to do this both for the instance body and its type. *) *)
       tmEval hnf (my_projT2 instance) >>=
         tmDefinitionRed_ false name (Some hnf) ;;

       (* Declare the new definition a type class instance *)
       mp <- tmCurrentModPath tt ;;
       tmExistingInstance (ConstRef (mp, name)) ;;

       let fake_kn := (fst kn, ind_name one) in
       tmMsg! ("Added InGraph instance for " ++ string_of_kername fake_kn) ;;
       ret tt) (ind_bodies mut).

Definition add_instances (kn : kername) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  singles_tys <- singles_tys kn mut ;;
  tmEval all singles_tys >>= tmPrint ;;
  singles <- singles kn mut singles_tys ;;
  tmEval all singles >>= tmPrint ;;
  add_instances_aux kn mut singles_tys singles ;;
  ret tt.

(* Derives a [InGraph] instance for the type constructor [Tau],
   and the types its definition depends on. *)
Definition in_graph_gen {kind : Type} (Tau : kind) : TemplateMonad unit :=
  '(env, tau) <- tmQuoteRec Tau ;;
  missing <- find_missing_instances (declarations env) ;;
  monad_iter add_instances (rev missing).

(* Playground: *)
(* MetaCoq Run (in_graph_gen unit). *)
(* MetaCoq Run (in_graph_gen nat). *)
(* MetaCoq Run (in_graph_gen option). *)
(* MetaCoq Run (in_graph_gen list). *)


(*

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A O
| vcons : forall n, A -> vec A n -> vec A (S n).

Check <%% vec %%>.
MetaCoq Run (in_graph_gen nat).

(* Check <% fun (A : Type) (P1 : nat) (x : vec A P1) => *)
(*            match x with vnil => False end %>. *)


MetaCoq Run (in_graph_gen vec).

MetaCoq Run (in_graph_gen unit).
Print InGraph_unit.

MetaCoq Run (in_graph_gen option).
Print InGraph_option.

Inductive option_indexed : Type -> Type :=
| mysome : forall A, A -> option_indexed A.
(* This is supposed to fail because if the type argument is not a parameter,
   then knowing how to represent things of that type statically is tricky,
   and often impossible. *)
Fail MetaCoq Run (in_graph_gen option_indexed).

MetaCoq Run (in_graph_gen bool).
Print InGraph_bool.

MetaCoq Run (in_graph_gen prod).
Print InGraph_prod.


Inductive mylist (A B : Type) : Type :=
| mynil : mylist A B
| mycons : A -> option A -> option B -> mylist A B.
MetaCoq Run (in_graph_gen mylist).

MetaCoq Run (in_graph_gen nat).
Print InGraph_nat.

MetaCoq Run (in_graph_gen list).
Print InGraph_list.


(* Testing mutually recursive inductive types: *)
Inductive T1 :=
| c1 : T2 -> T1
with T2 :=
| c2 : T1 -> T2.
MetaCoq Run (in_graph_gen T1).

Inductive tree (A : Type) : Type :=
| tleaf : tree A
| tnode : nat -> forest A -> tree A
with forest (A : Type) : Type :=
| fnil : forest A
| fcons : tree A -> forest A -> forest A.
MetaCoq Run (in_graph_gen tree)


(* Testing dependent types: *)
Inductive natty : nat -> nat -> Type :=
| mynatty : forall n m, natty n m.
MetaCoq Run (in_graph_gen natty).

Inductive D1 : nat -> Type :=
| cd1 : forall n : nat, D1 n.
MetaCoq Run (in_graph_gen D1).

Inductive D2 (n : nat) : Type :=
| cd2 : D2 n.
MetaCoq Run (in_graph_gen D2).

Inductive indexed : nat -> Type :=
| bar : indexed O.
MetaCoq Run (in_graph_gen indexed).

| vcons : forall n, A -> vec A n -> vec A (S n).
(* FIXME: this one doesn't work but should *)

Inductive fin : nat -> Set :=
| F1 : forall {n}, fin (S n)
| FS : forall {n}, fin n -> fin (S n).
MetaCoq Run (in_graph_gen fin).


Inductive param_and_index (a b : nat) : a < b -> Type :=
| foo : forall (pf : a < b), param_and_index a b pf.
(* MetaCoq Run (in_graph_gen param_and_index). *)


(*
Instance InGraph_vec (A : Type) (InGraph_A : InGraph A) (n : nat) : InGraph (vec A n) :=
  let fix is_in_graph_vec (n : nat) (g : graph) (x : vec A n) (p : rep_type) {struct x} : Prop :=
    match x with
    | vnil => graph_cRep g p (enum 0) []
    | vcons arg0 arg1 arg2 =>
        exists p0 p1 p2 : rep_type,
          @rep nat InGraph_nat g arg0 p0 /\
          @rep A InGraph_A g arg1 p1 /\
          is_in_graph_vec arg0 g arg2 p2 /\
          graph_cRep g p (boxed 0 3) [p0; p1; p2]
    end
  in @Build_InGraph (vec A n) (rep_vec n).

Instance InGraph_fin (n : nat) : InGraph (fin n) :=
  let fix rep_fin (n : nat) (g : graph) (x : fin n) (p : rep_type) {struct x} : Prop :=
    match x with
    | @F1 arg0 =>
        exists p0 : rep_type, rep g arg0 p0 /\ graph_cRep g p (boxed 0 1) [p0]
    | @FS arg0 arg1 =>
        exists p0 p1 : rep_type,
          rep g arg0 p0 /\
          rep_fin arg0 g arg1 p1 /\ graph_cRep g p (boxed 1 2) [p0; p1]
    end in @Build_InGraph (fin n) (rep_fin n).
*)

(* Testing nested types: *)
(* "Haskell Programming with Nested Types: A Principled Approach", Johann and Ghani, 2009 *)
Inductive lam (A : Type) : Type :=
| variable : A -> lam A
| app : lam A -> lam A -> lam A
| abs : lam (option A) -> lam A.

Inductive digit (A : Type) : Type :=
| one : A -> digit A
| two : A -> A -> digit A
| three : A -> A -> A -> digit A
| four : A -> A -> A -> A -> digit A.
Inductive node (A : Type) : Type :=
| node2 : nat -> A -> A -> node A
| node3 : nat -> A -> A -> A -> node A.
Inductive finger_tree (A : Type) : Type :=
| emptyT : finger_tree A
| single : A -> finger_tree A
| deep : nat -> digit A -> finger_tree (node A) -> digit A -> finger_tree A.


Inductive two (A : Type) := mkTwo : A -> A -> two A.
Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : two (tree A) -> tree A.
Inductive ntree (A : Type) : Type :=
| nleaf : ntree A
| nnode : ntree (two A) -> ntree A.

*)

(* MetaCoq Run (in_graph_gen Rep). *)
