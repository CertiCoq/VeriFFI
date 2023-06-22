Require Import VeriFFI.examples.uint63.prog.

Require Import ZArith.
Require Import Psatz.

Require Import VeriFFI.verification.specs_general.

Require Import VeriFFI.generator.all.

Obligation Tactic := gen.
MetaCoq Run (gen_for Z).
MetaCoq Run (gen_for nat).
MetaCoq Run (gen_for bool).

Print positive.
(* MetaCoq Run (desc_gen xH). *)
MetaCoq Run (desc_gen xI).
(* MetaCoq Run (desc_gen xO). *)

(* MetaCoq Run (desc_gen Z0). *)
(* MetaCoq Run (desc_gen Zpos). *)
(* MetaCoq Run (desc_gen Zneg). *)


Require Import VST.floyd.proofauto.
Require Import VeriFFI.examples.uint63.glue.
Require Import VeriFFI.library.meta.

Definition alloc_make_Coq_Numbers_BinNums_positive_xI_spec : ident * funspec :=
  DECLARE _alloc_make_Coq_Numbers_BinNums_positive_xI
          (alloc_make_spec_general (@desc _ xI _) 1).

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := [alloc_make_Coq_Numbers_BinNums_positive_xI_spec].

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

Check intro_prop_through_close_precondition.

Lemma body_alloc_make_Coq_Numbers_BinNums_positive_xI :
  semax_body Vprog Gprog
             f_alloc_make_Coq_Numbers_BinNums_positive_xI
             alloc_make_Coq_Numbers_BinNums_positive_xI_spec.
Proof.
  unfold alloc_make_Coq_Numbers_BinNums_positive_xI_spec.
  unfold alloc_make_spec_general.
  start_function1.
  repeat (simple apply intro_prop_through_close_precondition; intro).
  destruct ps, xs.

  Print PROPx.


  Print close_precondition.



erewrite compute_close_precondition_eq.
2 : { reflexivity.}
2 : { simpl. reflexivity.}
  Print start_function2.
  start_function2.
  start_function.
Admitted.
