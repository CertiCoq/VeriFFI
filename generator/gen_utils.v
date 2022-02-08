Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Strings.Ascii
               Coq.Lists.List.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.String.

From MetaCoq.Template Require Import BasicAst.
Require MetaCoq.Template.All.

(* Import monad_utils.MCMonadNotation. *)
(* Open Scope monad_scope. *)

Section Names.

  Fixpoint split_aux (acc : string) (sep : ascii) (s : string) : list string :=
    match s with
    | EmptyString => acc :: nil
    | String c s' =>
        if Char.ascii_dec sep c
          then acc :: split_aux EmptyString sep s'
          else split_aux (acc ++ String c EmptyString) sep s'
    end.

  Definition split (c : ascii) (s : string) : list string :=
    split_aux EmptyString c s.

 Definition qualifying_prefix := modpath.
 Definition base_name := string.
 Definition sanitized_name := string.

 (* takes a fully qualified name and removes the base name,
    leaving behind the qualifying prefix.
    e.g. "Coq.Init.Datatypes.bool" becomes "Coq.Init.Datatypes." *)
  Definition find_qualifying_prefix (n : kername) : qualifying_prefix :=
    fst n.
  (* match rev (split "." n) with
    | nil => (* not possible *) ""%string
    | base :: rest => String.concat "." (rev (""%string :: rest))
    end. *)

 (* takes a fully qualified name and gives the base name *)
  Definition find_base_name (n : kername) : base_name :=
    snd n.
  (* match rev (split "." n) with
    | nil => (* not possible *) ""%string
    | base :: rest => base
    end. *)

  Definition sanitize_dirpath (dp : dirpath) : string :=
    String.concat "_" (List.rev dp).

  Fixpoint sanitize_modpath (mp : modpath) : string :=
    match mp with
    | MPfile dp => sanitize_dirpath dp
    | MPbound dp id _ => (sanitize_dirpath dp ++ "_" ++ id)%string
    | MPdot mp0 id => (sanitize_modpath mp0 ++ "_" ++ id)%string
    end.

  (* Takes in "M1.M2.tau" and returns "M1_M2_tau". *)
  Definition sanitize_qualified (n : kername) : sanitized_name :=
    let (mp, id) := n in
    (sanitize_modpath mp ++ "_" ++ id)%string.

  Definition sanitize_string (s : string) : sanitized_name :=
    String.concat "_" (split "." s).

End Names.

(* A record that holds L1 information about Coq types. *)
Record ty_info : Type :=
  Build_ty_info
    { ty_name      : kername
    ; ty_body      : Ast.one_inductive_body
    ; ty_inductive : inductive
    ; ty_params    : list string
    }.

(* A record that holds information about Coq constructors.
   This may be redesigned in the future to hold info about
   the [dissected_type] etc, like a one-stop shop for constructors? *)
Record ctor_info : Type :=
  { ctor_name    : BasicAst.ident
  ; ctor_arity   : nat
  ; ctor_ordinal : nat
  ; ctor_type    : Ast.term
  }.

Section L1Constructors.

  Inductive dissected_type :=
  | dInd : inductive -> dissected_type
  | dApp : dissected_type -> list dissected_type -> dissected_type
  | dFun : dissected_type (* for higher-order arguments to constructor *)
  | dParam : string -> dissected_type (* for argument of the parametrized types *)
  | dSort : dissected_type (* for type arguments to the ctor *)
  | dInvalid : dissected_type (* used for variables that could not be found *).

  (* Get nth type from the [dissected_type] context.
     Used for when n is a De Bruijn index. *)
  Definition get_from_ctx (ctx : list dissected_type) (n : nat) : dissected_type :=
    nth_default dInvalid ctx n.

  Fixpoint dissect_type
         (* type context, required to be able to resolve De Bruijn indices *)
           (ctx : list dissected_type)
         (* a simple component of constructor type *)
           (ty : Ast.term)
         (* the dissected type component (not the full type) *)
           : dissected_type :=
    match ty with
    | Ast.tRel n => get_from_ctx ctx n
    | Ast.tInd ind _ => dInd ind
    | Ast.tProd _ e1 e2 => dFun
    | Ast.tSort _ => dSort
    | Ast.tApp hd args =>
        dApp (dissect_type ctx hd) (map (dissect_type ctx) args)
    | _ => dInvalid
    end.

  Definition for_ctx (d : dissected_type) : dissected_type :=
    match d with
    | dSort => dInvalid
    | _ => d
    end.

  Fixpoint dissect_types
         (* number of parameters in the type *)
           (params : list string)
         (* context of types for De Bruijn indices in the type *)
           (ctx : list dissected_type)
         (* the type of the constructor that will be dissected *)
           (ty : Ast.term)
         (* a list of arguments and the return type *)
           : list dissected_type * dissected_type :=
    match ty, params with
    (* Parameters have to be named!
       Ideally we'd print an error message otherwise. *)
    | Ast.tProd (mkBindAnn (nNamed x) _) e1 e2, _ :: p' =>
        dissect_types p' (dParam x :: ctx) e2
    | Ast.tProd _ e1 e2, nil =>
        let e1' := dissect_type ctx e1 in
        let (args, rt) := dissect_types params (for_ctx e1' :: ctx) e2 in
        (e1' :: args, rt)
    | _, _ => (nil, dissect_type ctx ty)
    end.


  Import Template.Ast
         ListNotations.

  (*
  Definition s := tProd nAnon (tRel 0) (tRel 1).
  Eval compute in (dissect_types nil (dInd (MPfile nil, "Coq.Init.Datatypes.nat"%string) :: nil) s).

  Definition datatypes_kn na : kername := (MPfile (cons "Datatypes" (cons "Init" (cons "Coq" nil))), na)%string.
  Definition top_kn na : kername := (MPfile (cons "Top" nil), na)%string.
  Arguments top_kn na%string.
  Definition change := tProd nAnon
                          (tProd nAnon
                            (tInd
                                {|
                                inductive_mind := datatypes_kn "nat"%string;
                                inductive_ind := 0 |} nil)
                            (tRel 1))
                          (tRel 1).

  Eval compute in (dissect_types [] (dInd (top_kn "color") :: nil) change).

  (* Definition c := tProd (nNamed "a"%string) *)
  (*                   (tSort ((Level.Level "Top.43", false) :: nil)) *)
  (*                   (tProd nAnon (tRel 0) (tRel 2)). *)
  (* Eval compute in (dissect_types 0 (dInd "Top.test" :: nil) c). *)

  Definition s := tProd nAnon (tRel 0) (tRel 1).
  Eval compute in (dissect_types 0 (dInd "Coq.Init.Datatypes.nat" :: nil) s).

  Definition no := tProd (nNamed "a"%string)
                     (tSort ((Level.Level "Top.40", false) :: nil))
                     (tProd nAnon (tRel 0)
                         (tProd nAnon (tApp (tRel 2) (tRel 1 :: nil))
                           (tProd nAnon (tApp (tRel 3) (tRel 2 :: nil))
                               (tApp (tRel 4) (tRel 3 :: nil))))).
  Eval compute in (dissect_types 1 (dInd "Top.tree" :: nil) no).
  *)

End L1Constructors.

Section Ctor_Info.

  Variant ctor_box : Type := unboxed | boxed.

  (* Can be used [if unbox_check c then ... else ...] *)
  Definition unbox_check (ctor : BasicAst.ident * Ast.term * nat) : ctor_box :=
    let '(_, _, arity) := ctor in
    match arity with
    | O => unboxed
    | S _ => boxed
    end.

  (* A function to calculate the ordinals of a type's constructors. *)
  Definition process_ctors
             (ctors : list (BasicAst.ident * Ast.term * nat)) : list ctor_info :=
    let fix aux
            (unboxed_count : nat)
            (boxed_count : nat)
            (ctors : list (BasicAst.ident * Ast.term * nat)) : list ctor_info :=
      match ctors with
      | nil => nil
      | (name, t, ar) :: ctors' =>
        let '(ord, rest) :=
            match ar with
            | O   => (unboxed_count, aux (S unboxed_count) boxed_count ctors')
            | S _ => (boxed_count, aux unboxed_count (S boxed_count) ctors')
            end
        in
          {| ctor_name := name
           ; ctor_arity := ar
           ; ctor_ordinal := ord
           ; ctor_type := t
           |} :: rest
      end
    in aux O O ctors.

End Ctor_Info.

Module MetaCoqNotations.
  Import MetaCoq.Template.All.

  (* Recursive quoting *)
  Notation "<%% x %%>" :=
    ((ltac:(let p y := exact y in run_template_program (tmQuoteRec x) p)))
    (only parsing).
  (* Check <%% nat %%>. *)

  (* Splicing / top level antiquotation *)
  Notation "~( x )" :=
    (ltac:(let p y :=
              let e := eval unfold my_projT2 in (my_projT2 y) in
              exact e in
          run_template_program (tmUnquote x) p))
    (only parsing).
  (* Check (~( <% fun (x : bool) => if x then false else true  %>)). *)
  (* Compute (~(<% fun (x : bool) => if x then false else true %>) false). *)

  (* Name resolution *)
  Notation "<? x ?>" :=
    (ltac:(let p y :=
              match y with
              | tInd {| inductive_mind := ?name |} _ =>
                exact name
              | tConst ?name _ =>
                exact name
              | _ => fail "not a type constructor or definition name" end in
          run_template_program (tmQuote x) p))
    (only parsing).
  (* Compute <? option ?>. *)
End MetaCoqNotations.

From MetaCoq.Template Require Import BasicAst.
Require Import MetaCoq.Template.All.

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
        | tSort s =>
          ret t
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
        | tSort s =>
          ret t
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
