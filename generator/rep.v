(*
  Author: Joomy Korkut (joomy@cs.princeton.edu), 2020

  Generator for the [rep] relation for a given Coq type.

  The [rep] function should match on a Coq value of a given type,
  and check if a C value represents that Coq value
  the same way CertiCoq represents it.

  This is similar to the pattern in VST but instead of [T -> val -> mpred],
  our [rep] function has the type [graph -> T -> rep_type -> Prop],
  for a given [T].

  This file defines a [Rep] type class containing the [rep] relation,
  and it also defines a MetaCoq program that generates a [Rep] instance
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
    find out if there is a [Rep] instance for it,
    and remember it in a list of lists.
    * In order to find out the [Rep] instance, you have to
      quantify over all parameters and indices.
  * If a block is missing any instance,
    define type class instances for each type in the block.

  Caveats:
  * If a type is of sort [Prop], the representation of its values is
    the same as [unit] for all values.
  * Parameters are not included in the memory representation,
    indices are. But parameters should be quantified over in the [Rep] instance type.
*)
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

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation
       ListNotations
       MetaCoqNotations.

(* Alias to distinguish terms that are NOT in de Bruijn notation. *)
Definition named_term : Type := term.
(* Alias for terms that do not contain references to local variables,
   therefore can be used in either [term]s in de Bruijn notation
   and [named_term]s in named notation. *)
Definition global_term : Type := term.
(* Alias to denote that a function works with
   either [term], [named_term] or [global_term]. *)
Definition any_term : Type := term.

Module DB.
  (* Inspired by code written by John Li but changed slightly.
     We should eventually consider making a MetaCoq_utils module. *)

  (* Takes a named representation and converts it into the de Bruijn representation. *)
  Definition deBruijn' (ctx : list name) (t : named_term) : TemplateMonad term :=
    let fix find_in_ctx (count : nat) (id : BasicAst.ident) (ctx : list name) : option nat :=
      match ctx with
      | nil => None
      | nAnon :: ns => find_in_ctx (S count) id ns
      | (nNamed id') :: ns =>
        if BasicAst.ident_eq id id' then Some count else find_in_ctx (S count) id ns
      end in
    let fix go (ctx : list name) (t : named_term) : TemplateMonad term :=
        let go_mfix (mf : mfixpoint named_term) : TemplateMonad (mfixpoint term) :=
          let ctx' := map (fun x => binder_name (dname x)) mf in
          monad_map (fun def =>
                       dtype' <- go ctx def.(dtype) ;;
                       dbody' <- go (rev ctx' ++ ctx) def.(dbody) ;;
                       ret (mkdef _ def.(dname) dtype' dbody' def.(rarg))) mf
        in
        match t with
        | tRel n => ret t
        | tVar id =>
            match find_in_ctx O id ctx with
            | Some i => ret (tRel i)
            | None => ret t (* could be a free variable *)
            end
        | tEvar ev args =>
            args' <- monad_map (go ctx) args ;;
            ret (tEvar ev args')
        | tSort s => ret t
        | tCast t kind v =>
            t' <- go ctx t ;;
            v' <- go ctx v ;;
            ret (tCast t' kind v')
        | tProd na ty body =>
            ty' <- go ctx ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tProd na ty' body')
        | tLambda na ty body =>
            ty' <- go ctx ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tLambda na ty' body')
        | tLetIn na def def_ty body =>
            def' <- go ctx def ;;
            def_ty' <- go ctx def_ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tLetIn na def' def_ty' body')
        | tApp f args =>
            f' <- go ctx f ;;
            args' <- monad_map (go ctx) args ;;
            ret (tApp f' args')
        | tConst c u => ret t
        | tInd ind u => ret t
        | tConstruct ind idx u => ret t
        | tCase ind_nbparams_relevance type_info discr branches =>
            type_info' <- go ctx type_info ;;
            discr' <- go ctx discr ;;
            branches' <- monad_map (fun '(n, t) => t' <- go ctx t ;; ret (n, t')) branches ;;
            ret (tCase ind_nbparams_relevance type_info' discr' branches')
        | tProj proj t =>
            t' <- go ctx t ;;
            ret (tProj proj t')
        | tFix mfix idx =>
            mfix' <- go_mfix mfix ;;
            ret (tFix mfix' idx)
        | tCoFix mfix idx =>
            mfix' <- go_mfix mfix ;;
            ret (tCoFix mfix' idx)
        | tInt p => ret (tInt p)
        | tFloat p => ret (tFloat p)
        end
    in go ctx t.

  Definition deBruijn (t : named_term) : TemplateMonad term := deBruijn' nil t.

  (* Takes a de Bruijn representation and changes [tRel]s to [tVar]s. *)
  Definition undeBruijn' (ctx : list name) (t : term) : TemplateMonad named_term :=
    let fix go (ctx : list name) (t : term) : TemplateMonad named_term :=
        let go_mfix (mf : mfixpoint term) : TemplateMonad (mfixpoint named_term) :=
          let ctx' := map (fun x => binder_name (dname x)) mf in
          monad_map (fun def =>
                       dtype' <- go ctx def.(dtype) ;;
                       dbody' <- go (rev ctx' ++ ctx) def.(dbody) ;;
                       ret (mkdef _ def.(dname) dtype' dbody' def.(rarg))) mf
        in
        match t with
        | tRel n =>
            match nth_error ctx n with
            | None => ret t
            | Some nAnon => tmFail "Reference to anonymous binding"
            | Some (nNamed id) => ret (tVar id)
            end
        | tVar id => ret t
        | tEvar ev args =>
            args' <- monad_map (go ctx) args ;;
            ret (tEvar ev args')
        | tSort s => ret t
        | tCast t kind v =>
            t' <- go ctx t ;;
            v' <- go ctx v ;;
            ret (tCast t' kind v')
        | tProd na ty body =>
            ty' <- go ctx ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tProd na ty' body')
        | tLambda na ty body =>
            ty' <- go ctx ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tLambda na ty' body')
        | tLetIn na def def_ty body =>
            def' <- go ctx def ;;
            def_ty' <- go ctx def_ty ;;
            body' <- go (binder_name na :: ctx) body ;;
            ret (tLetIn na def' def_ty' body')
        | tApp f args =>
            f' <- go ctx f ;;
            args' <- monad_map (go ctx) args ;;
            ret (tApp f' args')
        | tConst c u => ret t
        | tInd ind u => ret t
        | tConstruct ind idx u => ret t
        | tCase ind_nbparams_relevance type_info discr branches =>
            type_info' <- go ctx type_info ;;
            discr' <- go ctx discr ;;
            branches' <- monad_map (fun '(n, t) => t' <- go ctx t ;; ret (n, t')) branches ;;
            ret (tCase ind_nbparams_relevance type_info' discr' branches')
        | tProj proj t =>
            t' <- go ctx t ;;
            ret (tProj proj t')
        | tFix mfix idx =>
            mfix' <- go_mfix mfix ;;
            ret (tFix mfix' idx)
        | tCoFix mfix idx =>
            mfix' <- go_mfix mfix ;;
            ret (tCoFix mfix' idx)
        | tInt p => ret (tInt p)
        | tFloat p => ret (tFloat p)
        end
    in go ctx t.

  Definition undeBruijn (t : term) : TemplateMonad named_term :=
    undeBruijn' nil t.

  (* Example usage for deBruijn:

   MetaCoq Run (t <- DB.deBruijn
                      (tLambda (mkBindAnn (nNamed "x") Relevant)
                                <% bool %> (tVar "x"))%string ;;
                t' <- tmUnquoteTyped (bool -> bool) t ;;
                tmPrint t).
  *)

  (* Example usage for undeBruijn:

   MetaCoq Run (t <- DB.undeBruijn <% fun (x : bool) => x %> ;;
                tmPrint t).
  *)

  (* Round trip test:

  MetaCoq Run (t <- DB.undeBruijn
                      <% fix f (x y : nat) :=
                           match x with S x' => f x' (S y) | O => y end %> ;;
               t <- DB.deBruijn t ;;
               t' <- tmUnquoteTyped (nat -> nat -> nat) t ;;
               tmPrint t').
  *)

End DB.


Module Substitution.
  (* Capturing substitution for named terms, only use for global terms. *)
  Fixpoint named_subst (t : global_term) (x : BasicAst.ident) (u : named_term) {struct u} : named_term :=
    match u with
    | tVar id => if eq_string id x then t else u
    | tEvar ev args => tEvar ev (map (named_subst t x) args)
    | tCast c kind ty => tCast (named_subst t x c) kind (named_subst t x ty)
    | tProd (mkBindAnn (nNamed id) rel) A B =>
      if eq_string x id
      then tProd (mkBindAnn (nNamed id) rel) (named_subst t x A) B
      else tProd (mkBindAnn (nNamed id) rel) (named_subst t x A) (named_subst t x B)
    | tProd na A B => tProd na (named_subst t x A) (named_subst t x B)
    | tLambda (mkBindAnn (nNamed id) rel) T M =>
      if eq_string x id
      then tLambda (mkBindAnn (nNamed id) rel) (named_subst t x T) M
      else tLambda (mkBindAnn (nNamed id) rel) (named_subst t x T) (named_subst t x M)
    | tLambda na T M => tLambda na (named_subst t x T) (named_subst t x M)
    | tLetIn (mkBindAnn (nNamed id) rel) b ty b' =>
      if eq_string x id
      then tLetIn (mkBindAnn (nNamed id) rel) (named_subst t x b) (named_subst t x ty) b'
      else tLetIn (mkBindAnn (nNamed id) rel) (named_subst t x b) (named_subst t x ty) (named_subst t x b')
    | tLetIn na b ty b' => tLetIn na (named_subst t x b) (named_subst t x ty) (named_subst t x b')
    | tApp u0 v => mkApps (named_subst t x u0) (map (named_subst t x) v)
    | tCase ind p c brs =>
        let brs' := map (on_snd (named_subst t x)) brs in
        tCase ind (named_subst t x p) (named_subst t x c) brs'
    | tProj p c => tProj p (named_subst t x c)
    | tFix mfix idx => (* FIXME *)
      let mfix' := map (map_def (named_subst t x) (named_subst t x)) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := map (map_def (named_subst t x) (named_subst t x)) mfix in
      tCoFix mfix' idx
    | _ => u
    end.

  (* Substitute multiple [named_term]s into a [named_term]. *)
  Fixpoint named_subst_all (l : list (BasicAst.ident * named_term)) (u : named_term) : named_term :=
    match l with
    | nil => u
    | (id, t) :: l' => named_subst_all l' (named_subst t id u)
    end.
End Substitution.

Module ConstSubstitution.
  Fixpoint named_subst (t : global_term) (x : kername) (u : named_term) {struct u} : named_term :=
    match u with
    | tConst kn _ => if eq_kername x kn then t else u
    | tVar id => t
    | tEvar ev args => tEvar ev (map (named_subst t x) args)
    | tCast c kind ty => tCast (named_subst t x c) kind (named_subst t x ty)
    | tProd (mkBindAnn (nNamed id) rel) A B =>
      tProd (mkBindAnn (nNamed id) rel) (named_subst t x A) (named_subst t x B)
    | tProd na A B => tProd na (named_subst t x A) (named_subst t x B)
    | tLambda (mkBindAnn (nNamed id) rel) T M =>
      tLambda (mkBindAnn (nNamed id) rel) (named_subst t x T) (named_subst t x M)
    | tLambda na T M => tLambda na (named_subst t x T) (named_subst t x M)
    | tLetIn (mkBindAnn (nNamed id) rel) b ty b' =>
      tLetIn (mkBindAnn (nNamed id) rel) (named_subst t x b) (named_subst t x ty) (named_subst t x b')
    | tLetIn na b ty b' => tLetIn na (named_subst t x b) (named_subst t x ty) (named_subst t x b')
    | tApp u0 v => mkApps (named_subst t x u0) (map (named_subst t x) v)
    | tCase ind p c brs =>
        let brs' := map (on_snd (named_subst t x)) brs in
        tCase ind (named_subst t x p) (named_subst t x c) brs'
    | tProj p c => tProj p (named_subst t x c)
    | tFix mfix idx => (* FIXME *)
      let mfix' := map (map_def (named_subst t x) (named_subst t x)) mfix in
      tFix mfix' idx
    | tCoFix mfix idx =>
      let mfix' := map (map_def (named_subst t x) (named_subst t x)) mfix in
      tCoFix mfix' idx
    | _ => u
    end.

  (* Substitute multiple [named_term]s into a [named_term]. *)
  Fixpoint named_subst_all (l : list (kername * named_term)) (u : named_term) : named_term :=
    match l with
    | nil => u
    | (id, t) :: l' => named_subst_all l' (named_subst t id u)
    end.
End ConstSubstitution.

Notation "f >=> g" := (fun x => (f x) >>= g)
                      (at level 51, right associativity) : monad_scope.
Notation "f <$> x" := (x' <- x%monad ;; ret (f x'))
                      (at level 52, right associativity) : monad_scope.
Open Scope string.

Class Rep (A : Type) : Type :=
  { rep : forall (g : graph) (x : A) (p : rep_type), Prop }.

Instance Rep_Prop : Rep Prop :=
  {| rep g x p := graph_cRep g p (enum 0) [] |}.
Instance Rep_Set : Rep Set :=
  {| rep g x p := graph_cRep g p (enum 0) [] |}.
Instance Rep_Type : Rep Type :=
  {| rep g x p := graph_cRep g p (enum 0) [] |}.

(* Starting generation of [Rep] instances! *)

Section Argumentation.

  Variant arg_variant : Type :=
  | param_arg : forall (param_name : BasicAst.ident) (param_type : named_term), arg_variant
  | value_arg : forall (arg_name exists_name : BasicAst.ident) (arg_type : named_term), arg_variant.

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
         so that later when we encounter the [tInd] we know which [Rep] instance to call.
     *)
    let mut_names : list BasicAst.ident :=
        map (fun one => "$$$" ++ string_of_kername (mp, ind_name one)) (ind_bodies mut) in
    let mut_ind_terms : list (BasicAst.ident * global_term) :=
        mapi (fun i one =>
                let id := "$$$" ++ string_of_kername (mp, ind_name one) in
                let ind := mkInd kn i in
                (id, tInd ind nil))
            (ind_bodies mut) in

    let fix aux (params : nat) (* number of parameters left *)
                (arg_count : nat) (* number of args seen *)
                (ctx : list BasicAst.ident) (* names of params and args to be used *)
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
        let arg_name : BasicAst.ident := "arg" ++ string_of_nat arg_count in
        let exists_name : BasicAst.ident := "p" ++ string_of_nat arg_count in
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
   This is a function that will be used to generate the type of the new [Rep] instance,
   for which the [type_quantifier] adds a [Rep] instance argument.
   This function can also be used to get a fully applied [named_term] and its quantifiers.
   The quantifiers would go around the [rep] function and the [Rep] instance.
*)
Definition generate_instance_type
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body)
           (type_quantifier : BasicAst.ident -> named_term -> named_term)
           (replacer : named_term -> named_term) : TemplateMonad named_term :=
  (* Convert the type of the type to explicitly named representation *)
  ty <- DB.undeBruijn (ind_type one) ;;
  let num_of_params := ind_npars mut in
  (* Goes over a nested π-type and collects binder names,
     makes up a name where there isn't one.
     It also builds a function to replace the part after the π-binders. *)
  let fix collect
          (t : named_term) (remaining_params : nat) (count : nat) (replacer : named_term -> named_term)
          : list (BasicAst.ident * is_param * is_sort) * (named_term -> named_term) :=
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

Definition generate_Rep_instance_type
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad named_term :=
  generate_instance_type ind mut one
    (fun ty_name t =>
      let n := "Rep_" ++ ty_name in
      tProd (mkBindAnn (nNamed n) Relevant) (tApp <% Rep %> [tVar ty_name]) t)
    (fun t => apply_to_pi_base (fun t' => tApp <% Rep %> [t']) t).

(* Constructs the instance type for the type at hand,
   checks if there's an instance for it. *)
Definition find_missing_instance
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad bool :=
  tmMsg ("Missing: " ++ string_of_inductive ind) ;;
  generate_Rep_instance_type ind mut one >>=
  DB.deBruijn >>= tmUnquoteTyped Type >>= has_instance.

(* Take in a [global_env], which is a list of declarations,
   and find the inductive declarations in that list
   that do not have [Rep] instances. *)
Fixpoint find_missing_instances
        (env : global_env) : TemplateMonad (list kername) :=
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

(* Takes in a term representing a type like [forall A, Rep (list A)]),
   and finds the type class instance for that. *)
Definition instance_term (inst_ty : named_term) : TemplateMonad named_term :=
  tmMsg "instance_term1:" ;;
  inst_ty' <- DB.deBruijn inst_ty >>= tmUnquoteTyped Type ;;
  tmMsg "instance_term:" ;;
  tmEval all inst_ty' >>= tmPrint ;;
  opt_ins <- tmInferInstanceEval inst_ty' ;;
  match opt_ins with
  | my_Some x => tmQuote x >>= DB.undeBruijn
  | _ =>
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
         (modify : BasicAst.ident -> BasicAst.ident)
         (t : named_term) : list (aname * named_term) :=
  match t with
  | tProd (mkBindAnn nAnon rel) ty rest =>
    (mkBindAnn nAnon rel, ty) :: get_quantifiers modify rest
  | tProd (mkBindAnn (nNamed id) rel) ty rest =>
    (mkBindAnn (nNamed (modify id)) rel, ty) :: get_quantifiers modify rest
  | x => nil
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

Definition build_Rep_call
           (all_single_rep_tys : list (aname * named_term))
           (quantifiers : list (aname * named_term))
           (ind : inductive)
           (nt : named_term) : TemplateMonad named_term :=
  let args := (all_single_rep_tys ++ quantifiers)%list in
  let quantified := build_quantifiers tProd args (tApp <% Rep %> [nt]) in
  quantified <- tmEval all quantified ;;
  tmMsg "==========" ;;
  (* tmMsg "FOR:" ;; *)
  (* tmPrint nt ;; *)
  (* tmMsg "QUANTIFIED:" ;; *)
  (* tmPrint quantified ;; *)
  tmEval all quantified >>= tmPrint ;;
  t <- instance_term quantified ;;
  (* NOTE: could this ever be a problem?
           is it possible for the fake [___Rep]s to come eta reduced? *)
  let t := tApp (strip_n_lambdas (length all_single_rep_tys) t)
                (map make_arg quantifiers) in
  tmEval cbn t.

Definition build_rep_call
           (all_single_rep_tys : list (aname * named_term))
           (quantifiers : list (aname * named_term))
           (ind : inductive)
           (nt : named_term) : TemplateMonad named_term :=
  Rep_call <- build_Rep_call all_single_rep_tys quantifiers ind nt ;;
  res <-
    match Rep_call with
    | tApp (tVar n) rest =>
      if prefix "___Rep" n
      then
        let num : string := substring 6 10 n in
        ret (tApp (tVar ("rep" ++ num)) (map make_arg quantifiers))
        (* ret (tVar ("rep" ++ num)) *)
      else
        ret (tApp <% @rep %> [nt ; Rep_call])
    | _ =>
      ret (tApp <% @rep %> [nt ; Rep_call])
    end ;;
  res <- tmEval all res ;;
  (* tmMsg "build_rep_call :" ;; *)
  (* tmEval all quantifiers >>= tmPrint ;; *)
  (* tmPrint res ;; *)
  ret res.

Fixpoint make_prop
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
              (match ctor_arity ctor with
                | O => enum (N.of_nat (ctor_ordinal ctor))
                | a => boxed (N.of_nat (ctor_ordinal ctor)) (N.of_nat a)
                end) ;;
    t_crep <- tmQuote crep ;;
    (* Create list of [[p0;p1;p2;...]] to pass to [graph_cRep] *)
    let l := t_conses (map (fun n => tVar ("p" ++ string_of_nat n))
                           (seq 0 (ctor_arity ctor))) in
    ret (tApp <% graph_cRep %>
              [ t_g ; t_p ; t_crep ; l])
  in


  (* Takes in the [arg_variant],
     generates the call to [rep] for that argument.
     Returns a list so that [param_arg] can return a empty list. *)
  let make_arg_prop (i : nat) (arg : arg_variant) : TemplateMonad (list named_term) :=
    tmMsg ("ARG_PROP #" ++ string_of_nat i ++ ":") ;;
    match arg with
      | value_arg arg_name p_name nt =>
        (* tmMsg "HERE'S ONE!" ;; *)
        let t_arg := tVar arg_name in
        let t_p := tVar p_name in
        call <- build_rep_call all_single_rep_tys quantifiers ind nt ;;
        tmMsg "REP CALL: " ;;
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
      (* names and types of all rep_i functions in the fix block *)
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
    : TemplateMonad (nat * named_term) :=
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
  let t := make_lambdas args (make_exists args prop) in
  (* tmMsg "PROP:" ;; *)
  (* tmEval all t >>= tmPrint ;; *)
  ret (ctor_arity ctor, t).

(* For sort parameters we have to skip 2 quantifiers,
   one for the param itself, one for the [Rep] instance.
   For all other parameters we can just skip one. *)
Fixpoint count_quantifiers_to_skip (xs : context) : nat :=
  match xs with
  | x :: xs' =>
    (if check_sort (decl_type x) then 2 else 1) + count_quantifiers_to_skip xs'
  | nil => 0
  end.

(* Generates a reified match expression *)
Definition matchmaker
    (all_single_rep_tys : list (aname * named_term))
      (* names and types of all rep_i functions in the fix block *)
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
  let to_skip :=
    (count_quantifiers_to_skip (ind_params mut)) in
  tmMsg ("Will skip " ++ string_of_nat to_skip) ;;
  let quantifiers_without_params :=
      skipn to_skip quantifiers in
  tmMsg "QUANT WITHOUT PARAMS:" ;;
  tmEval all quantifiers_without_params >>= tmPrint ;;
  ret (tCase (ind, O, Relevant)
             (* TODO only quantify over the indices, not parameters *)
             (build_quantifiers tLambda quantifiers_without_params
                                (tLambda (mkBindAnn (nNamed "y") Relevant) tau <% Prop %>))
             (* (tLambda (mkBindAnn (nNamed "y") Relevant) tau <% Prop %>) *)
             (tVar "x")
             branches).

(* Make a single record to use in a [tFix].
   For mutually inductive types, we want to build them all once,
   and define all the [Rep] instances with that. *)
Definition make_fix_single
           (all_single_rep_tys : list (aname * named_term))
           (quantifiers : list (aname * named_term))
           (tau : named_term) (* fully applied type constructor *)
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad (BasicAst.def named_term) :=
  let this_name := nNamed ("rep" ++ string_of_nat (inductive_ind ind)) in
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

Definition add_instances (kn : kername) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  singles_tys <- monad_map_i
               (fun i one =>
                  (* FIXME get rid of repeated computation here *)
                  let ind := {| inductive_mind := kn ; inductive_ind := i |} in
                  quantified <- generate_instance_type ind mut one
                                  (fun ty_name t =>
                                    let n := "Rep_" ++ ty_name in
                                    tProd (mkBindAnn (nNamed n) Relevant) (tApp <% Rep %> [tVar ty_name]) t)
                                  (fun t => apply_to_pi_base (fun t' => tApp <% Rep %> [t']) t) ;;
                  (* tmMsg "quantified:" ;; *)
                  quantified <- tmEval all quantified ;;
                  (* ___Rep0, ___Rep1 etc. are fake instances,
                     gotta replace their usage with calls to rep0, rep1 etc later. *)
                  let an := mkBindAnn (nNamed ("___Rep" ++ string_of_nat i)) Relevant in
                  ret (an, quantified))
               (ind_bodies mut) ;;
  (* Build the single function definitions for each of
     the mutually recursive types. *)
  singles <- monad_map_i
               (fun i one =>
                  (* FIXME get rid of repeated computation here *)
                  let ind := {| inductive_mind := kn ; inductive_ind := i |} in
                  quantified <- generate_instance_type ind mut one
                                  (fun ty_name t =>
                                    let n := "Rep_" ++ ty_name in
                                    tProd (mkBindAnn (nNamed n) Relevant) (tApp <% Rep %> [tVar ty_name]) t)
                                    id ;;
                  (* tmMsg "quantified:" ;; *)
                  (* tmEval all quantified >>= tmPrint ;; *)
                  let quantifiers := get_quantifiers id quantified in
                  let tau := strip_quantifiers quantified in
                  make_fix_single singles_tys quantifiers tau {| inductive_mind := kn ; inductive_ind := i |} mut one)
               (ind_bodies mut) ;;

  (* Loop over each mutually recursive type again *)
  monad_map_i
    (fun i one =>
       let ind := {| inductive_mind := kn ; inductive_ind := i |} in
       (* This gives us something like
          [forall (A : Type) (n : nat), vec A n] *)
       quantified <- generate_instance_type ind mut one
                      (fun ty_name t =>
                        let n := "Rep_" ++ ty_name in
                        tProd (mkBindAnn (nNamed n) Relevant) (tApp <% Rep %> [tVar ty_name]) t)
                      id ;;
       (* tmMsg "quantified:" ;; *)
       (* tmEval all quantified >>= tmPrint ;; *)

       (* Now what can we do with this?
          Let's start by going to its named representation. *)
       (* quantified_named <- DB.undeBruijn [] quantified ;; *)

       (* tmEval all quantified_named >>= tmPrint ;; *)
       (* The reified type of the fully applied type constructor,
          but with free variables! *)
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
       (* tmMsg "args_let: " ;; tmEval all args_let >>= tmPrint ;; *)
       let fn : named_term :=
           tLetIn (mkBindAnn (nNamed "f") Relevant)
                  (tFix singles i)
                  (build_quantifiers tProd quantifiers fn_ty)
                  (tApp (tVar "f") args_let) in
       let prog_named : named_term :=
           build_quantifiers tLambda quantifiers
                             (tApp <% @Build_Rep %>
                                   [tau; fn]) in
       (* tmMsg "" ;; *)
       tmMsg "Final:" ;;
       tmEval all prog_named >>= tmPrint ;;

       (* Convert generated program from named to de Bruijn representation *)
       prog <- DB.deBruijn prog_named ;;
       (* tmMsg "Final unnamed:" ;; *)
       (* tmEval all prog >>= tmPrint ;; *)

       extra_quantified <- DB.deBruijn (build_quantifiers tProd quantifiers
                                                          (tApp <% Rep %> [tau])) ;;
       tmMsg "Instance ty before:" ;;
       tmEval all extra_quantified >>= tmPrint ;;
       (* If need be, here's the reified type of our [Rep] instance: *)
       instance_ty <- tmUnquoteTyped Type extra_quantified ;;

       tmMsg "Instance ty:" ;;
       tmEval all instance_ty >>= tmPrint ;;

       instance <- tmUnquote prog ;;

       (* tmMsg "Instance:" ;; *)
       (* tmEval all instance >>= tmPrint ;; *)

       (* Remove [tmEval] when MetaCoq issue 455 is fixed: *)
       (* https://github.com/MetaCoq/metacoq/issues/455 *)
       name <- tmFreshName =<< tmEval all ("Rep_" ++ ind_name one)%string ;;

       (* This is sort of a hack. I couldn't use [tmUnquoteTyped] above
          because of a mysterious type error. (Coq's type errors in monadic
          contexts are just wild.) Therefore I had to [tmUnquote] it to get
          a Σ-type. But when you project the second field out of that,
          the type doesn't get evaluated to [Rep _], it stays as
          [my_projT2 {| ... |}]. The same thing goes for the first projection,
          which is the type of the second projection. When the user prints
          their [Rep] instance, Coq shows the unevaluated version.
          But we don't want to evaluate it [all] the way, that would unfold
          the references to other instances of [Rep]. We only want to get
          the head normal form with [hnf].
          We have to do this both for the instance body and its type. *)
       tmEval hnf (my_projT2 instance) >>=
         tmDefinitionRed_ false name (Some hnf) ;;

       (* Declare the new definition a type class instance *)
       mp <- tmCurrentModPath tt ;;
       tmExistingInstance (ConstRef (mp, name)) ;;

       let fake_kn := (fst kn, ind_name one) in
       tmMsg ("Added Rep instance for " ++ string_of_kername fake_kn) ;;
       ret tt) (ind_bodies mut) ;;
  ret tt.

(* Derives a [Rep] instance for the type constructor [Tau],
   and the types its definition depends on. *)
Definition rep_gen {kind : Type} (Tau : kind) : TemplateMonad unit :=
  '(env, tau) <- tmQuoteRec Tau ;;
  missing <- find_missing_instances env ;;
  monad_iter add_instances (rev missing).

(* Playground: *)

(* MetaCoq Run (rep_gen unit). *)
(* MetaCoq Run (rep_gen nat). *)
(* MetaCoq Run (rep_gen option). *)
(* MetaCoq Run (rep_gen list). *)

(*

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A O
| vcons : forall n, A -> vec A n -> vec A (S n).

Check <%% vec %%>.
MetaCoq Run (rep_gen nat).

(* Check <% fun (A : Type) (P1 : nat) (x : vec A P1) => *)
(*            match x with vnil => False end %>. *)


MetaCoq Run (rep_gen vec).

MetaCoq Run (rep_gen unit).
Print Rep_unit.

MetaCoq Run (rep_gen option).
Print Rep_option.

Inductive option_indexed : Type -> Type :=
| mysome : forall A, A -> option_indexed A.
(* This is supposed to fail because if the type argument is not a parameter,
   then knowing how to represent things of that type statically is tricky,
   and often impossible. *)
Fail MetaCoq Run (rep_gen option_indexed).

MetaCoq Run (rep_gen bool).
Print Rep_bool.

MetaCoq Run (rep_gen prod).
Print Rep_prod.


Inductive mylist (A B : Type) : Type :=
| mynil : mylist A B
| mycons : A -> option A -> option B -> mylist A B.
MetaCoq Run (rep_gen mylist).

MetaCoq Run (rep_gen nat).
Print Rep_nat.

MetaCoq Run (rep_gen list).
Print Rep_list.


(* Testing mutually recursive inductive types: *)
Inductive T1 :=
| c1 : T2 -> T1
with T2 :=
| c2 : T1 -> T2.
MetaCoq Run (rep_gen T1).

Inductive tree (A : Type) : Type :=
| tleaf : tree A
| tnode : nat -> forest A -> tree A
with forest (A : Type) : Type :=
| fnil : forest A
| fcons : tree A -> forest A -> forest A.
MetaCoq Run (rep_gen tree)


(* Testing dependent types: *)
Inductive natty : nat -> nat -> Type :=
| mynatty : forall n m, natty n m.
MetaCoq Run (rep_gen natty).

Inductive D1 : nat -> Type :=
| cd1 : forall n : nat, D1 n.
MetaCoq Run (rep_gen D1).

Inductive D2 (n : nat) : Type :=
| cd2 : D2 n.
MetaCoq Run (rep_gen D2).

Inductive indexed : nat -> Type :=
| bar : indexed O.
MetaCoq Run (rep_gen indexed).

| vcons : forall n, A -> vec A n -> vec A (S n).
(* FIXME: this one doesn't work but should *)

Inductive fin : nat -> Set :=
| F1 : forall {n}, fin (S n)
| FS : forall {n}, fin n -> fin (S n).
MetaCoq Run (rep_gen fin).


Inductive param_and_index (a b : nat) : a < b -> Type :=
| foo : forall (pf : a < b), param_and_index a b pf.
(* MetaCoq Run (rep_gen param_and_index). *)


(*
Instance Rep_vec (A : Type) (Rep_A : Rep A) (n : nat) : Rep (vec A n) :=
  let fix rep_vec (n : nat) (g : graph) (x : vec A n) (p : rep_type) {struct x} : Prop :=
    match x with
    | vnil => graph_cRep g p (enum 0) []
    | vcons arg0 arg1 arg2 =>
        exists p0 p1 p2 : rep_type,
          @rep nat Rep_nat g arg0 p0 /\
          @rep A Rep_A g arg1 p1 /\
          rep_vec arg0 g arg2 p2 /\
          graph_cRep g p (boxed 0 3) [p0; p1; p2]
    end
  in @Build_Rep (vec A n) (rep_vec n).

Instance Rep_fin (n : nat) : Rep (fin n) :=
  let fix rep_fin (n : nat) (g : graph) (x : fin n) (p : rep_type) {struct x} : Prop :=
    match x with
    | @F1 arg0 =>
        exists p0 : rep_type, rep g arg0 p0 /\ graph_cRep g p (boxed 0 1) [p0]
    | @FS arg0 arg1 =>
        exists p0 p1 : rep_type,
          rep g arg0 p0 /\
          rep_fin arg0 g arg1 p1 /\ graph_cRep g p (boxed 1 2) [p0; p1]
    end in @Build_Rep (fin n) (rep_fin n).
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
