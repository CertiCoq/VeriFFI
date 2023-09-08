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
Require Import VeriFFI.library.modelled.

(* Unset MetaCoq Strict Unquote Universe Mode. *)

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation
       ListNotations
       MetaCoqNotations.

Module Type T.
  Axiom y : nat.
  Inductive f : Prop:=
  with g :=.
End T.
Module M : T.
  Variable x : unit.
  Inductive f : Prop:=
  with g :=.
  Axiom y : nat.
  Definition z := O.
End M.

Definition test : TemplateMonad unit :=
  tmQuoteModule "M"%bs >>= tmPrint.
MetaCoq Run (test).

Print TemplateMonad.
Print term.
Print global_reference.

Definition module_to_specs (l : list global_reference) : TemplateMonad (list fn_desc).
  match l with
  | VarRef : ident -> global_reference
  | ConstRef : kername -> global_reference
  | IndRef : inductive -> global_reference
  | ConstructRef : inductive -> nat -> global_reference.
  end.
    

Definition ref_to_term (g : global_reference) : TemplateMonad global_term :=
  match g
  


Definition test : TemplateMonad unit :=
  tmQuoteModule "M" >>= tmPrint!.
MetaCoq Run (test).
Print global_reference.
Set Universe Polymorphism.
(* Set Polymorphic Inductive Cumulativity. *)

