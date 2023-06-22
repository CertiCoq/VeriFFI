Require Import VeriFFI.library.base_representation.
Require Import VeriFFI.library.meta.
Require Import VeriFFI.generator.InGraph.
Require Import VeriFFI.generator.Rep.
Require Import VeriFFI.generator.Desc.

From MetaCoq.Template Require Import BasicAst.
Require Import MetaCoq.Template.All.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation.

Definition gen_for {kind : Type} (Tau : kind) : TemplateMonad unit :=
  @in_graph_gen kind Tau ;;
  @rep_gen kind Tau.

Definition desc_gen {T : Type} (ctor_val : T) : TemplateMonad unit :=
  @Desc.desc_gen T ctor_val.

Ltac gen :=
  match goal with
  | [ |- @reconstructor _ _ ?C _ ] => reconstructing
  | _ => rep_gen_tac
  end.
