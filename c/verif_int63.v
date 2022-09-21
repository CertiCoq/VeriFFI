From VST Require Import floyd.proofauto.
From VeriFFI Require Import c.int63.
From VeriFFI Require Import c.spec_int63.
From VeriFFI Require Import library.modelled.


Lemma eqmod_mul_m:
 forall c m a b, Zbits.eqmod m a b -> Zbits.eqmod (c*m) (c*a) (c*b).
Proof.
intros.
unfold Zbits.eqmod in *.
destruct H as [k ?].
exists k. lia.
Qed.

Lemma body_add: semax_body Vprog ASI f_certicoq_prim__int63_add certicoq_prim__int63_add_spec.
Proof.
unfold certicoq_prim__int63_add_spec, tag63.
start_function.
forward.
apply prop_right.
f_equal.
destruct x as [a ?].
destruct y as [b ?].
simpl proj1_sig.
replace (2*a+1+(2*b+1)-1) with
  (2*(a+b)+1) by lia.
forget (a+b) as c.
clear.
apply Int64.eqm_samerepr.
apply Int64.eqm_add; [ | apply Int64.eqm_refl].
unfold Int64.eqm.
change Int64.modulus with (2 * 2^63).
apply eqmod_mul_m.
apply Zbits.eqmod_mod.
lia.
Qed.

Lemma body_mul: semax_body Vprog ASI f_certicoq_prim__int63_mul certicoq_prim__int63_mul_spec.
Proof.
unfold certicoq_prim__int63_mul_spec, tag63.
start_function.
forward.
apply prop_right.
f_equal.
destruct x as [a ?].
destruct y as [b ?].
simpl proj1_sig.
unfold Int64.shru.
rewrite !Int64.unsigned_repr by rep_lia.
rewrite mul64_repr.
rewrite Z.shiftr_div_pow2 by lia.
rewrite add64_repr.
rewrite Z.pow_1_r.
replace ((2 * a + 1)/2) with a.
2:{
rewrite Z.add_comm.
rewrite Z.mul_comm.
rewrite Z.div_add by lia.
simpl. lia.
}
rewrite Z.add_simpl_r.
replace (a*(2*b)) with (2*(a*b)) by ring.
forget (a+b) as c.
clear.
apply Int64.eqm_samerepr.
apply Int64.eqm_add; [ | apply Int64.eqm_refl].
unfold Int64.eqm.
change Int64.modulus with (2 * 2^63).
apply eqmod_mul_m.
apply Zbits.eqmod_mod.
lia.
Qed.
