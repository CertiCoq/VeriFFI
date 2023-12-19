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
(* Check append_desc. *)

(* C function in examples/bytestring/prims.c *)
(* Check (fn_desc_to_funspec append_desc). *)
