Require Import String.

Require Import ZArith.
Require Import Psatz.
Require Import List.
Import ListNotations.

Require Import VeriFFI.library.isomorphism.
Require Import VeriFFI.library.meta.
Require Import VeriFFI.library.modelled.

Require Import VST.floyd.proofauto.

(*
mk_funspec
  ((_f OF tptr voidstar_funtype)%formals :: (_args OF tptr tvoid)%formals :: nil, tvoid)
  cc_default
  spawn_arg_type
  spawn_pre
  spawn_post
  spawn_pre_nonexpansive
  spawn_post_nonexpansive.
Check mk_funspec.
*)

Definition val : type := tulong.
(*
Definition ep_to_funspec_aux
         (has_tinfo : bool)
         (a : annotated)
         (bogus : Type) : compcert_rmaps.typesig :=
  let fix aux (a : annotated) {struct a} : compcert_rmaps.typesig :=
    match a with
    | TYPEPARAM f =>
        let (args, res) := aux (f False Rep_any) in
        (val :: args, val)
    | OPAQUE _ _ _ (Some f) =>
        let (args, res) := aux (f False Rep_any) in
        (val :: args, val)
    | OPAQUE _ _ _ None =>
        (nil, val)
    | TRANSPARENT _ _ (Some f) =>
        (nil, val)
    | TRANSPARENT _ _ None =>
        (nil, val)
    end in
  let (args, res) := aux a False in
  if has_tinfo
  then (cons (Tstruct (ident_of_string "thread_info") noattr) args, res)
  else (args, res).
*)

Fixpoint ep_to_funspec_aux
         (a : annotated)
         (ft : to_prim_fn_type a)
         (mt : to_model_fn_type a) {struct a} : funspec.
exact ImpossibleFunspec.
Defined.

Definition ep_to_funspec (ep : extern_properties) : funspec :=
  ep_to_funspec_aux (type_desc ep) (prim_fn ep) (model_fn ep).
