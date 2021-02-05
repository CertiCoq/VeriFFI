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

Import MonadNotation.
Open Scope monad_scope.

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

  (* Data type name resolution *)
  Notation "<? x ?>" :=
    (ltac:(let p y :=
              match y with
              | tInd {| inductive_mind := ?name |} _ =>
                exact name
              | _ => fail "not a type constructor" end in
          run_template_program (tmQuote x) p))
    (only parsing).
  (* Compute <? option ?>. *)
End MetaCoqNotations.
