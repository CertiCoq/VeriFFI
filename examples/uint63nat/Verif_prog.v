Require Import VeriFFI.examples.uint63nat.prog.

Require Import ZArith.
Require Import Psatz.

Require Import VeriFFI.verification.specs_general.
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

#[export] Instance CCE1: change_composite_env env_graph_gc.CompSpecs CompSpecs.
make_cs_preserve env_graph_gc.CompSpecs CompSpecs.
Defined.

(* BEGIN patch simulating VST p.r. #681.
  This patch can be deleted, even before merging the P.R., because its
  only purpose is to diagnose when compspecs don't match, and our
  current proof correctly does a change_compspecs to make them match. *)
Ltac equal_pointers p q :=
 lazymatch p with
 | offset_val 0 ?p' => equal_pointers p' q
 | _ => lazymatch q with offset_val 0 ?q' => equal_pointers p q'
        | _ => unify p q
        end
 end.

Ltac SEP_field_at_unify' gfs ::=
  match goal with
  | |- @field_at ?csl ?shl ?tl ?gfsl ?vl ?pl = @field_at ?csr ?shr ?tr ?gfsr ?vr ?pr =>
      unify tl tr;
      unify (Floyd_skipn (length gfs - length gfsl) gfs) gfsl;
      unify gfsl gfsr;
      unify shl shr;
      unify vl vr;
      equal_pointers pl pr;
      constr_eq csl csr +
      fail 12 "Two different compspecs present:" 
         csl "and" csr 
        ".  Try using change_compspecs, or use VSUs";

      generalize vl; intro;
      rewrite <- ?field_at_offset_zero;
      f_equal; (* this line is important to prevent blow-ups *)
      reflexivity
  end.
(* END patch simulating VST p.r. #681 *)

Lemma body_alloc_make_Coq_Init_Datatypes_nat_S :
  semax_body Vprog Gprog
             f_alloc_make_Coq_Init_Datatypes_nat_S
             alloc_make_Coq_Init_Datatypes_nat_S_spec.
Proof.
  unfold alloc_make_Coq_Init_Datatypes_nat_S_spec.
  unfold alloc_make_spec_general.
  start_function1.
  repeat (simple apply intro_prop_through_close_precondition; intro).
  simpl in xs. destruct xs. destruct u.
  simpl in H. clear H.
  destruct ps; try contradiction.
  destruct H0. simpl in H0. subst ps.
  start_function2.
  start_function3.
  unfold full_gc. Intros.
  unfold before_gc_thread_info_rep. Intros.
  change_compspecs CompSpecs. 
  forward.
  entailer!.  admit.
Fail  forward.



  (* erewrite compute_close_precondition_eq. *)
  (* 2 : { reflexivity.} *)
  (* 2 : { simpl. reflexivity.} *)
  (*   Print start_function2. *)
  (*   start_function2. *)
  (*   start_function. *)
Abort.
