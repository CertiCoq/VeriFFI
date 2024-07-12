(*
  Author: Joomy Korkut (joomy@cs.princeton.edu), 2024

  Generator for the [graph_predicate] relation for a given Coq type.

  The [graph_predicate] function should match on a Coq value of a given type,
  and check if a C value represents that Coq value
  the same way CertiCoq represents it.

  This is similar to the pattern in VST but instead of [A -> val -> mpred],
  our [graph_predicate] function has the type [graph -> A -> rep_type -> Prop],
  for a given [A].

  This file defines a MetaCoq program that generates a [GraphPredicate] instance
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
    find out if there is a [GraphPredicate] instance for it,
    and remember it in a list of lists.
    * In order to find out the [GraphPredicate] instance, you have to
      quantify over all parameters and indices.
  * If a block is missing any instance,
    define type class instances for each type in the block.

  Caveats:
  * If a type is of sort [Prop], the representation of its values is
    the same as [unit] for all values.
  * Parameters are not included in the memory representation,
    indices are. But parameters should be quantified over in the [GraphPredicate] instance type.
*)
Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Lists.List
               Coq.Lists.ListSet.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad.

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
Notation "'tmPrint'" := (tmPrint).
Notation "'tmMsg'" := (tmMsg).
(* Notation "'tmPrint'" := (fun _ => ret tt). *)
(* Notation "'tmMsg'" := (fun _ => ret tt). *)

(* Starting generation of [GraphPredicate] instances! *)

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
         so that later when we encounter the [tInd] we know which [GraphPredicate] instance to call.
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
   This is a function that will be used to generate the type of the new [GraphPredicate] instance,
   for which the [type_quantifier] adds a [GraphPredicate] instance argument.
   This function can also be used to get a fully applied [named_term] and its quantifiers.
   The quantifiers would go around the [graph_predicate] function and the [GraphPredicate] instance.
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
  (* monad_map (fun '(n,p,s) => *)
  (*             match p, s with *)
  (*             | false, true => *)
  (*               tmFail "Our system cannot generate representation relations for types that use type arguments in non-parameter positions." *)
  (*             | _ , _ => ret tt *)
  (*             end) quantified ;; *)
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

Definition generate_GraphPredicate_instance_type
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad named_term :=
  generate_instance_type ind mut one
    (fun ty_name t =>
      let n := "GraphPredicate_" ++ ty_name in
      tProd (mkBindAnn (nNamed n) Relevant) (tApp <% GraphPredicate %> [tVar ty_name]) t)
    (fun t => apply_to_pi_base (fun t' => tApp <% GraphPredicate %> [t']) t).

(* Constructs the instance type for the type at hand,
   checks if there's an instance for it. *)
Definition find_missing_instance
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad bool :=
  tmMsg ("Missing: " ++ string_of_inductive ind) ;;
  generate_GraphPredicate_instance_type ind mut one >>=
  DB.deBruijn >>= tmUnquoteTyped Type >>= has_instance.

(* Take in a [global_declarations], which is a list of declarations,
   and find the inductive declarations in that list
   that do not have [GraphPredicate] instances. *)
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

(* Takes in a term representing a type like [forall A, GraphPredicate (list A)]),
   and finds the type class instance for that. *)
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

(* For sort parameters we have to skip 2 quantifiers,
   one for the param itself, one for the [GraphPredicate] instance.
   For all other parameters we can just skip one. *)
Fixpoint count_quantifiers_to_skip (xs : context) : nat :=
  match xs with
  | x :: xs' =>
    (if check_sort (decl_type x) then 2 else 1) + count_quantifiers_to_skip xs'
  | nil => 0
  end.

Definition singles_tys (kn : kername)
                       (mut : mutual_inductive_body)
                       : TemplateMonad (list (aname * named_term)) :=
  monad_map_i
    (fun i one =>
      (* FIXME get rid of repeated computation here *)
      let ind := {| inductive_mind := kn ; inductive_ind := i |} in
      quantified <- generate_instance_type ind mut one
                      (fun ty_name t =>
                        let n := "GraphPredicate_" ++ ty_name in
                        tProd (mkBindAnn (nNamed n) Relevant) (tApp <% GraphPredicate %> [tVar ty_name]) t)
                      (fun t => apply_to_pi_base (fun t' => tApp <% GraphPredicate %> [t']) t) ;;
      (* tmMsg "quantified:" ;; *)
      quantified <- tmEval all quantified ;;
      (* ___GraphPredicate0, ___GraphPredicate1 etc. are fake instances,
          gotta replace their usage with calls to graph_predicate0, graph_predicate1 etc later. *)
      let an := mkBindAnn (nNamed ("___GraphPredicate" ++ string_of_nat i)) Relevant in
      ret (an, quantified))
    (ind_bodies mut).

(* This gives us something like [forall (A : Type) (n : nat), vec A n] *)
Definition quantified ind mut one (inst_prefix: string) (inst: global_term) :=
  generate_instance_type ind mut one
    (fun ty_name t =>
      let n := inst_prefix ++ ty_name in
      tProd (mkBindAnn (nNamed n) Relevant) (tApp inst [tVar ty_name]) t)
    id.

Polymorphic Definition tmLemma' (id : ident) (t : term) : TemplateMonad unit.
refine (t' <- tmUnquoteTyped Type t ;; _).
refine (tmLemma id t' ;; _).
refine (tmReturn tt).
Defined.

Definition GraphPredicate_with_info
           (mutuals : nat)
           (mutual_index : nat)
           (ctors : list (list arg_variant)) : Type -> Type :=
  GraphPredicate.

Definition add_instances_aux
           (kn : kername)
           (mut : mutual_inductive_body)
           (singles_tys : list (aname * named_term)) : TemplateMonad unit :=
  let mutuals : nat := length (ind_bodies mut) in
  t_mutuals <- tmEval all mutuals >>= tmQuote ;;
  monad_map_i
    (fun i one =>
       let ind := {| inductive_mind := kn ; inductive_ind := i |} in
       quantified <- quantified ind mut one "GraphPredicate_" <% GraphPredicate %> ;;
       (* Now what can we do with this? *)
       (*    Let's start by going to its named representation. *)
       (* The reified type of the fully applied type constructor, *)
       (*    but with free variables! *)
       let tau := strip_quantifiers quantified in
       let quantifiers : list (aname * named_term) :=
           get_quantifiers id quantified in
       args_let <- monad_map (fun '(an, _) =>
                                match an with
                                | mkBindAnn (nNamed n) _ => tmReturn (tVar n)
                                | _ => tmFail "Unnamed parameter"
                                end) quantifiers ;;
       t_i <- tmQuote i ;;
       extra_quantified <-
         DB.deBruijn (build_quantifiers tProd quantifiers
                                        (tApp <% GraphPredicate_with_info %>
                                              [ t_mutuals
                                              ; t_i
                                              ; tApp <% @nil %> [ hole ]
                                              ; tau])) ;;
       (* tmMsg "Extra Quantified:" ;; *)
       (* tmEval all extra_quantified >>= tmPrint ;; *)
       (* instance_ty <- tmUnquoteTyped Type extra_quantified ;; *)
       name <- tmFreshName ("GraphPredicate_" ++ ind_name one)%bs ;;
       tmEval all extra_quantified >>= tmLemma' name ;;

       (* Declare the new definition a type class instance *)
       mp <- tmCurrentModPath tt ;;
       tmExistingInstance export (ConstRef (mp, name)) ;;

       let fake_kn := (fst kn, ind_name one) in
       tmMsg! ("Added GraphPredicate instance for " ++ string_of_kername fake_kn) ;;
       tmReturn tt) (ind_bodies mut) ;;
  tmReturn tt.

Definition add_instances (kn : kername) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  singles_tys <- singles_tys kn mut ;;
  tmEval all singles_tys >>= tmPrint ;;
  add_instances_aux kn mut singles_tys ;;
  ret tt.

(* Derives a [GraphPredicate] instance for the type constructor [Tau],
   and the types its definition depends on. *)
Definition graph_predicate_gen {kind : Type} (Tau : kind) : TemplateMonad unit :=
  '(env, tau) <- tmQuoteRec Tau ;;
  missing <- find_missing_instances (declarations env) ;;
  monad_iter add_instances (rev missing).

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A O
| vcons : forall n, A -> vec A n -> vec A (S n).

#[local] Instance GraphPredicate_nat : GraphPredicate nat. Admitted.
#[local] Instance GraphPredicate_vec (A : Type) (GraphPredicate_A : GraphPredicate A) (n : nat) : GraphPredicate (vec A n) :=
  let fix graph_predicate_vec (n : nat) (g : graph) (x : vec A n) (p : rep_type) {struct x} : Prop :=
    match x with
    | vnil => graph_cRep g p (enum 0) []
    | vcons arg0 arg1 arg2 =>
        exists p0 p1 p2 : rep_type,
          @graph_predicate nat GraphPredicate_nat g arg0 p0 /\
          @graph_predicate A GraphPredicate_A g arg1 p1 /\
          graph_predicate_vec arg0 g arg2 p2 /\
          graph_cRep g p (boxed 0 3) [p0; p1; p2]
    end
  in @Build_GraphPredicate (vec A n) (graph_predicate_vec n).

MetaCoq Run (tmInferInstance (Some all) (GraphPredicate nat) >>= tmPrint).
MetaCoq Run (tmInferInstance (Some all) (forall A `{GraphPredicate A} n, GraphPredicate (vec A n)) >>= tmPrint).

Inductive tree (A : Type) : Type :=
| tleaf : tree A
| tnode : A -> forest A -> tree A
with forest (A : Type) : Type :=
| fnil : forest A
| fcons : tree A -> forest A -> forest A.

#[local]
Instance GraphPredicate_tree (A : Type) (GraphPredicate_A : GraphPredicate A) : GraphPredicate (tree A) :=
  let f :=
    fix graph_predicate_tree (g : graph) (x : tree A) (p : rep_type) {struct x} : Prop :=
      match x with
      | tleaf => graph_cRep g p (enum 0) []
      | tnode arg0 arg1 =>
          exists p0 p1 : rep_type,
            @graph_predicate A GraphPredicate_A g arg0 p0 /\
            graph_predicate_forest g arg1 p1 /\
            graph_cRep g p (boxed 0 2) [p0; p1]
      end
    with graph_predicate_forest (g : graph) (x : forest A) (p : rep_type) {struct x} : Prop :=
      match x with
      | fnil => graph_cRep g p (enum 0) []
      | fcons arg0 arg1 =>
          exists p0 p1 : rep_type,
            graph_predicate_tree g arg0 p0 /\
            graph_predicate_forest g arg1 p1 /\
            graph_cRep g p (boxed 0 2) [p0; p1]
      end
    for graph_predicate_tree
  in @Build_GraphPredicate (tree A) f.


(* Fixpoint tree_size {A} (t : tree A) : nat := *)
(*   match t with *)
(*   | tleaf => 0 *)
(*   | tnode _ f => 1 + forest_size f *)
(*   end *)
(* with forest_size {A} (f : forest A) : nat := *)
(*   match f with *)
(*   | fnil => 0 *)
(*   | fcons t f => tree_size t + forest_size f *)
(*   end. *)

Definition tree_size :=
  fix tree_size {A : Type} (t : tree A) : nat :=
    match t with
    | tleaf => 0
    | tnode _ f => 1 + forest_size f
    end
  with forest_size {A : Type} (f : forest A) : nat :=
    match f with
    | fnil => 0
    | fcons t f => tree_size t + forest_size f
    end
  for tree_size.

Fixpoint forest_size {A : Type} (f : forest A) : nat :=
  match f with
  | fnil => 0
  | fcons t f => tree_size t + forest_size f
  end.

Print tmPrint.




(* Playground: *)
Goal nat -> bool -> True.
fix f 1.
Print reductionStrategy.
Check (let fix ).

Ltac apply_fixes mutuals T :=
  unfold GraphPredicate_with_info;
  match mutuals with
  | 0 => fail "No mutual block can have zero types."
  | 1 =>
      let f1 := fresh "f" in
      refine (let fix f1 g (x : T) p {struct x} : Prop := _
              in @Build_GraphPredicate T f1)
  | 2 =>
      let f := fresh "f" in
      let f1 := fresh "f" in
      let f2 := fresh "f" in
      refine (let f := fix f1 g (x : T) p {struct x} : Prop := _
                       with f2 g (x : T) p {struct x} : Prop := _
                       for f1
              in @Build_GraphPredicate T f1)
  end.
    
Ltac graph_predicate_gen :=
  match goal with
  | [ |- @GraphPredicate_with_info ?mutuals ?mutual_index ?ctors ?T ] => 
      apply_fixes mutuals T
  | _ => fail
  end.

Inductive T1 :=
| c1 : T2 -> T1
with T2 :=
| c2 : T1 -> T2.
MetaCoq Run (graph_predicate_gen T1).


(* MetaCoq Run (graph_predicate_gen nat). *)
Next Obligation.
  refine
  graph_predicate_gen.
        
  refine (let fix f1 g (x : nat) p {struct x} : Prop := _ in @Build_GraphPredicate nat f1).
  case x.
  refine (graph_cRep g p (enum 0) []).
  intro arg0.
  refine (exists p0 : rep_type, _).
  refine (_ /\ _).
  refine (f1 g arg0 p0).
  refine (graph_cRep g p (boxed 0 1) [p0]).
Defined.
  
Print GraphPredicate_nat_obligation_1.

Inductive MI {bytestring : Type} : Type -> Type :=
| pureI : forall {A}, A -> MI A
| bindI : forall {A B}, MI A -> (A -> MI B) -> MI B
| printI : bytestring -> MI unit
| scanI : nat -> MI bytestring.

MetaCoq Run (graph_predicate_gen MI).


(* MetaCoq Run (graph_predicate_gen unit). *)
(* MetaCoq Run (graph_predicate_gen nat). *)
(* MetaCoq Run (graph_predicate_gen option). *)
(* MetaCoq Run (graph_predicate_gen list). *)
(* MetaCoq Run (graph_predicate_gen prod). *)

(*

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A O
| vcons : forall n, A -> vec A n -> vec A (S n).

Check <%% vec %%>.
MetaCoq Run (graph_predicate_gen nat).

(* Check <% fun (A : Type) (P1 : nat) (x : vec A P1) => *)
(*            match x with vnil => False end %>. *)


MetaCoq Run (graph_predicate_gen vec).

MetaCoq Run (graph_predicate_gen unit).
Print GraphPredicate_unit.

MetaCoq Run (graph_predicate_gen option).
Print GraphPredicate_option.

Inductive option_indexed : Type -> Type :=
| mysome : forall A, A -> option_indexed A.
(* This is supposed to fail because if the type argument is not a parameter,
   then knowing how to represent things of that type statically is tricky,
   and often impossible. *)
Fail MetaCoq Run (graph_predicate_gen option_indexed).

MetaCoq Run (graph_predicate_gen bool).
Print GraphPredicate_bool.

MetaCoq Run (graph_predicate_gen prod).
Print GraphPredicate_prod.


Inductive mylist (A B : Type) : Type :=
| mynil : mylist A B
| mycons : A -> option A -> option B -> mylist A B.
MetaCoq Run (graph_predicate_gen mylist).

MetaCoq Run (graph_predicate_gen nat).
Print GraphPredicate_nat.

MetaCoq Run (graph_predicate_gen list).
Print GraphPredicate_list.


(* Testing mutually recursive inductive types: *)
Inductive T1 :=
| c1 : T2 -> T1
with T2 :=
| c2 : T1 -> T2.
MetaCoq Run (graph_predicate_gen T1).

Inductive tree (A : Type) : Type :=
| tleaf : tree A
| tnode : nat -> forest A -> tree A
with forest (A : Type) : Type :=
| fnil : forest A
| fcons : tree A -> forest A -> forest A.
MetaCoq Run (graph_predicate_gen tree)


(* Testing dependent types: *)
Inductive natty : nat -> nat -> Type :=
| mynatty : forall n m, natty n m.
MetaCoq Run (graph_predicate_gen natty).

Inductive D1 : nat -> Type :=
| cd1 : forall n : nat, D1 n.
MetaCoq Run (graph_predicate_gen D1).

Inductive D2 (n : nat) : Type :=
| cd2 : D2 n.
MetaCoq Run (graph_predicate_gen D2).

Inductive indexed : nat -> Type :=
| bar : indexed O.
MetaCoq Run (graph_predicate_gen indexed).

| vcons : forall n, A -> vec A n -> vec A (S n).
(* FIXME: this one doesn't work but should *)

Inductive fin : nat -> Set :=
| F1 : forall {n}, fin (S n)
| FS : forall {n}, fin n -> fin (S n).
MetaCoq Run (graph_predicate_gen fin).


Inductive param_and_index (a b : nat) : a < b -> Type :=
| foo : forall (pf : a < b), param_and_index a b pf.
(* MetaCoq Run (graph_predicate_gen param_and_index). *)


(*
Instance GraphPredicate_vec (A : Type) (GraphPredicate_A : GraphPredicate A) (n : nat) : GraphPredicate (vec A n) :=
  let fix graph_predicate_vec (n : nat) (g : graph) (x : vec A n) (p : rep_type) {struct x} : Prop :=
    match x with
    | vnil => graph_cRep g p (enum 0) []
    | vcons arg0 arg1 arg2 =>
        exists p0 p1 p2 : rep_type,
          @rep nat GraphPredicate_nat g arg0 p0 /\
          @rep A GraphPredicate_A g arg1 p1 /\
          graph_predicate_vec arg0 g arg2 p2 /\
          graph_cRep g p (boxed 0 3) [p0; p1; p2]
    end
  in @Build_GraphPredicate (vec A n) (rep_vec n).

Instance GraphPredicate_fin (n : nat) : GraphPredicate (fin n) :=
  let fix rep_fin (n : nat) (g : graph) (x : fin n) (p : rep_type) {struct x} : Prop :=
    match x with
    | @F1 arg0 =>
        exists p0 : rep_type, rep g arg0 p0 /\ graph_cRep g p (boxed 0 1) [p0]
    | @FS arg0 arg1 =>
        exists p0 p1 : rep_type,
          rep g arg0 p0 /\
          rep_fin arg0 g arg1 p1 /\ graph_cRep g p (boxed 1 2) [p0; p1]
    end in @Build_GraphPredicate (fin n) (rep_fin n).
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

(* MetaCoq Run (graph_predicate_gen Rep). *)
