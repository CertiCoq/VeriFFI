Require Import VeriFFI.examples.uint63nat.prog.

Require Import ZArith.
Require Import Psatz.

Require Import VeriFFI.verification.specs_general.

Require Import VeriFFI.generator.all.

Obligation Tactic := gen.
MetaCoq Run (gen_for nat).
MetaCoq Run (gen_for bool).

MetaCoq Run (desc_gen S).

Require Import VST.floyd.proofauto.
Require Import VeriFFI.examples.uint63nat.glue.
Require Import VeriFFI.library.meta.


Require Import VST.floyd.proofauto.
Require Import CertiGraph.CertiGC.GCGraph.

From VeriFFI Require Import library.base_representation.
From VeriFFI Require Import library.meta.
From VeriFFI Require Import verification.graph_add.
From VeriFFI Require Import verification.specs_library.

Definition alloc_make_Coq_Init_Datatypes_nat_S_spec : ident * funspec :=
  DECLARE _alloc_make_Coq_Init_Datatypes_nat_S
          (alloc_make_spec_general (@desc _ S _) 1).

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := [alloc_make_Coq_Init_Datatypes_nat_S_spec].

Lemma intro_prop_through_close_precondition :
  forall {Espec : OracleKind} Delta (p1 : Prop) f ps LS sf c post,
  (p1 -> semax Delta (sepcon (close_precondition f ((PROPx ps LS))) sf) c post) ->
  semax Delta (sepcon (close_precondition f (PROPx (p1 :: ps) LS)) sf) c post.
Proof.
  intros.
  unfold close_precondition in *.
  simpl in *.
  eapply semax_pre with (andp (prop p1)
  (fun rho : environ =>
        ((EX vals : list val,
          !! (map (Map.get (te_of rho)) f = map Some vals /\
              Forall (fun v : val => v <> Vundef) vals) &&
          PROPx ps LS (ge_of rho, vals))
            * sf rho)%logic)).
  2: apply semax_extract_prop; auto.
  clear H.
  intro rho.
  simpl.
  apply andp_left2.
  Intro vals.
  Exists vals.
  unfold PROPx.
  simpl.
  normalize.
  apply andp_right; auto.
  apply prop_right; auto.
Qed.

(* Trying to rewrite with something like: *)
(* Lemma aux : forall P ps, (A' xs' ps' -> P ps') -> (A xs ps -> P ps) *)
Lemma combined_sigT_in_arg :
  forall (A : Type) (P : A -> Type) (T : forall (p : {x : A & P x}), Type),
     (forall (a1 : A) (a2: P a1), T (a1; a2)) -> (forall (p : {x : A & P x}), T p).
Proof. intros A P T f p. destruct p. apply f. Qed.

Lemma separate_sigT_in_arg :
  forall (A : Type) (P : A -> Type) (T : forall (p : {x : A & P x}), Type),
      (forall (p : {x : A & P x}), T p) -> (forall (a1 : A) (a2: P a1), T (a1; a2)).
Proof. auto. Qed.


Lemma body_alloc_make_Coq_Init_Datatypes_nat_S :
  semax_body Vprog Gprog
             f_alloc_make_Coq_Init_Datatypes_nat_S
             alloc_make_Coq_Init_Datatypes_nat_S_spec.
Proof.
  unfold alloc_make_Coq_Init_Datatypes_nat_S_spec.
  unfold alloc_make_spec_general.
  start_function1.
  hnf in xs.
  repeat (simple apply intro_prop_through_close_precondition; intro).
  pattern xs.

  (* apply combined_sigT_in_arg. *)
  (* pattern H. *)

  (* destruct xs. *)
  (* hnf in xs. *)
  (* pattern ps. *)
  (* destruct xs. *)
  (* (* write a lemma and rewrite *) *)
  (* destruct ps. *)
  (* contradiction H0. *)
  (* destruct a. *)

  (* unfold in_graphs in H0. *)
  (* destruct H0. *)
  (* subst. *)


  (* erewrite compute_close_precondition_eq. *)
  (* 2 : { reflexivity.} *)
  (* 2 : { simpl. reflexivity.} *)
  (*   Print start_function2. *)
  (*   start_function2. *)
  (*   start_function. *)
Abort.
