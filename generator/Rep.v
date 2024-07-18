Require Import VeriFFI.library.base_representation.
Require Import VeriFFI.library.meta.
Require Import VeriFFI.generator.GraphPredicate.
Require Import VeriFFI.generator.InGraph.
Require Import VeriFFI.generator.CtorDesc.

Require Import MetaCoq.Template.All.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation.

Definition gen_for {kind : Type} (Tau : kind) : TemplateMonad unit :=
  @graph_predicate_gen kind Tau ;;
  @in_graph_gen kind Tau.

Definition desc_gen {T : Type} (ctor_val : T) : TemplateMonad unit :=
  @ctor_desc_gen T ctor_val.

Ltac gen :=
  match goal with
  | [ |- @reflector _ _ _ _ ] => reflecting
  | _ => in_graph_gen_tac
  end.

Local Obligation Tactic := gen.

(* MetaCoq Run (in_graph_gen unit). *)
(* MetaCoq Run (desc_gen tt). *)