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
Require Import VeriFFI.library.isomorphism.

(* Unset MetaCoq Strict Unquote Universe Mode. *)

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation
       ListNotations
       MetaCoqNotations.

Module Type T.
  Axiom t : Type.
  Axiom add : t -> t -> t.
End T.
Module C : T.
  Axiom t : Type.
  Axiom add : t -> t -> t.
End C.
Module FM : T.
  Definition t := nat.
  Definition add := plus.
End FM.

MetaCoq Run (tmQuoteModule "FM"%bs >>= tmPrint).
(* Check (tmQuoteModule "M"%bs >>= monad_iter (fun x => tmLocate x >>= tmPrint)). *)
(* MetaCoq Run (tmQuoteModule "M"%bs >>= monad_iter (fun x => tmLocate x >>= tmPrint)). *)

Definition get_type (t : term) : TemplateMonad term :=
  t' <- tmUnquote t ;;
  tmEval all (my_projT1 t') >>= tmQuote.

Definition get_kn_type (kn : kername) : TemplateMonad term :=
  get_type (tConst kn []).

(* Check if the term is of the form "(_ ->)* (Type|Set|Prop)" *)
Fixpoint is_type (t : term) : bool :=
  match t with
  | tProd _ _ rest => is_type rest
  | tSort _ => true
  | _ => false
  end.

Check @Isomorphism.
Print tApp.
Definition type_to_isomorphism (c_ty f_ty : term) : TemplateMonad term :=
  let fix aux (c_ty f_ty : term) (c_args f_args : list named_term) : TemplateMonad named_term :=
    match c_ty, f_ty with
    | tProd cn ct c_rest, tProd fn ft f_rest =>
        id1 <- tmFreshName "A"%bs ;;
        id2 <- tmFreshName "B"%bs ;;
        id3 <- tmFreshName "Iso"%bs ;;
        rest <- aux c_rest f_rest (tVar id1 :: c_args) (tVar id2 :: f_args) ;;
        match is_type ct, is_type ft with
        | true, true => 
            ret (tProd (mkBindAnn (nNamed id1) Relevant) ct
                  (tProd (mkBindAnn (nNamed id2) Relevant) ft
                    (tProd (mkBindAnn (nNamed id3) Relevant)
                      (tApp <% Isomorphism %> [tVar id1; tVar id2]) rest)))
        | false, false => 
            ret (tProd (mkBindAnn (nNamed id1) Relevant) ct
                  (tProd (mkBindAnn (nNamed id2) Relevant) ft rest))
        | _, _ => tmFail "Mismatch on arguments"%bs
        end
    | tSort _, tSort _ =>
        ret (tApp <% Isomorphism %> [hole; hole]) (* TODO *)
    | _, _ => tmFail "Not a type"%bs
    end
  in aux c_ty f_ty nil nil.

Definition tmVariable_ (id : ident) (t : term) : TemplateMonad unit :=
  @tmBind _ _ (tmUnquoteTyped Type t) (fun ty => tmVariable id ty).
Set Printing Universes.
Print tmVariable_.

Definition tmVariable__ (id : ident) (t : term) : TemplateMonad unit :=
  tmVariable_ id t.

Check tmVariable__.
Check tmVariable_.
Print tmVariable.
Print Z.
Set Printing All.
Compute (-1)%Z.

Print N.
Print positive.
Compute (0%N).
Fixpoint module_to_specs
         (c_refs f_refs : list global_reference) : TemplateMonad (list fn_desc) :=
  match c_refs, f_refs with
  | ConstRef c_kn :: c_grs, ConstRef f_kn :: f_grs =>
      let '(c_id, f_id) := (snd c_kn, snd f_kn) in
      if negb (ident_eq c_id f_id)
      then tmFail ("Mismatch between functions " ++ c_id ++ " and " ++ f_id)%bs
      else
        c_ty <- get_kn_type c_kn ;;
        tmPrint c_ty ;;
        if is_type c_ty
        then
          f_ty <- get_kn_type f_kn ;;
          iso_ty <- type_to_isomorphism c_ty f_ty ;;
          iso_name <- tmFreshName ("Isomorphism_" ++ c_id)%bs ;;
          tmPrint iso_ty ;;
          tmVariable__ iso_name iso_ty ;;
          tmMsg ("Parametrized over " ++ iso_name)%bs ;;
          module_to_specs c_grs f_grs
        else
          tmMsg "NOPE"%bs ;;
          module_to_specs c_grs f_grs
  | c_gr :: c_grs , f_gr :: f_grs =>
      tmMsg "Couldn't generate spec for: "%bs ;;
      tmPrint c_gr ;;
      module_to_specs c_grs f_grs
  | nil , nil => ret nil
  | nil , _ => tmFail "Reference list mismatch, the functional model has more definitions"%bs
  | _ , nil => tmFail "Reference list mismatch, the primitives have more definitions"%bs
  end.

Definition test c fm : TemplateMonad unit :=
  cl <- tmQuoteModule c ;;
  fl <- tmQuoteModule fm ;;
  module_to_specs cl fl >>= tmPrint.

MetaCoq Run (test "C" "FM")%bs.
Print global_reference.
Set Universe Polymorphism.
(* Set Polymorphic Inductive Cumulativity. *)

