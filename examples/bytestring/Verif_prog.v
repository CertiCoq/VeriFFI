Require Import ZArith.
Require Import Psatz.

Require Import VeriFFI.generator.funspec.
Require Import VeriFFI.generator.Rep.

(* Obligation Tactic := gen. *)
(* MetaCoq Run (gen_for nat). *)
(* MetaCoq Run (gen_for unit). *)

Require Import VeriFFI.examples.bytestring.prog.
Require Import VeriFFI.examples.bytestring.model.

Import Bytestring_Proofs.
Check pure_desc.

Check (fn_desc_to_funspec pure_desc).
