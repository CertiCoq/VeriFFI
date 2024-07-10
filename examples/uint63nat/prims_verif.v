Require Import VeriFFI.examples.uint63nat.prims.
Require Import ZArith.
Require Import Psatz.
Require Import CertiGraph.CertiGC.spatial_gcgraph.

Require Import VeriFFI.examples.uint63nat.specs.

#[export] Instance CCE3: change_composite_env Verif_prog_general.CompSpecs CompSpecs.
make_cs_preserve Verif_prog_general.CompSpecs CompSpecs.
Defined.

Definition description_S := @ctor_desc_of_val _ S _. 

Lemma decode_encode_Z: 
  forall n, (* min_signed <= *) encode_Z (Z.of_nat n) <= Int64.max_unsigned ->
  Int64.shru (Int64.repr (encode_Z (Z.of_nat n)))
              (Int64.repr (Int.unsigned (Int.repr 1)))
               = Int64.repr (Z.of_nat n).
Proof.
intros.
unfold encode_Z in *.
autorewrite with norm. rewrite Int64.shru_div_two_p.
change (two_p _) with 2.
rewrite !Int64.unsigned_repr by lia.  
rewrite Z.div_add_l by lia.
simpl Z.div; rewrite Z.add_0_r.
auto.
Qed.

Lemma body_uint63_add:
  semax_body Vprog Gprog f_uint63_add uint63_add_spec.
Proof. 
start_function1.
repeat (simple apply intro_prop_through_close_precondition; intro).
concretize_PARAMS.
(* TODO: FIX *)
destruct xs. unfold prim_in_graphs in H1. simpl in H1. destruct ps; try contradiction.
destruct H1. subst.
start_function2. 
start_function3.
forward.
 entailer!.
  unfold encode_Z in *.
  autorewrite with norm.
(*   rewrite !Int64.shru_div_two_p.
change (two_p _) with 2.
rewrite !Int64.unsigned_repr by lia.  
rewrite Z.div_add_l by lia.
rewrite Int64.shl_mul_two_p.
autorewrite with norm. change (two_p _) with 2. 
f_equal. f_equal.
assert ((Z.of_nat n * 2 + 1) / 2 = Z.of_nat n) as ->. 
{ rewrite Z.add_comm. rewrite Z_div_plus; try lia.
  replace (1/2) with 0 by reflexivity. 
  lia. }
lia. 
Qed. *)
Admitted.

Lemma body_uint63_from_nat:
  semax_body Vprog Gprog f_uint63_from_nat uint63_from_nat_spec.
Proof.
 start_function'. 
 rename x into n.
 forward.
 fold (rep_type_val g p).
 forward.
 rewrite Int.signed_repr 
   by (unfold encode_Z in H; rep_lia).
 forward_loop ( EX m : nat, EX p': rep_type,
        PROP ( (m <= n)%nat; is_in_graph g outlier (n - m)%nat p';        
              nat_has_tag_prop (n - m)%nat (nat_get_desc (n-m)%nat))
        LOCAL (temp _i (Vlong (Int64.repr (Z.of_nat m))); 
               temp _temp (rep_type_val g p');
               temp _n (rep_type_val g p); gvars gv) 
        SEP (full_gc g t_info roots outlier ti sh gv * library.mem_mgr gv)
    )
   break: (PROP()LOCAL(temp _i (Vlong (Int64.repr (Z.of_nat n))))
           SEP(full_gc g t_info roots outlier ti sh gv * library.mem_mgr gv)).
- (* Before the loop. *)
  Exists 0%nat. Exists p. rewrite Nat.sub_0_r. entailer!.
  destruct n; constructor.
- (* loop body *)
  Intros m p'.
  forward_call (gv, g, p', (n-m)%nat, roots, sh, ti, outlier, t_info).
  forward_if.
  +  (* then clause *)
    destruct (n-m)%nat as [ | nm'] eqn:Hnm'. discriminate. clear H3.
    forward.
    forward_call (gv, g, p', nm', roots, sh, ti, outlier, t_info).
    Intros vret; destruct vret as [q shq].
    simpl snd in H4. simpl fst in H6.
    simpl fst; simpl snd.
    set (px := rep_type_val g p') in *.
    limited_change_compspecs CompSpecs.
    forward. {
      entailer.
      rewrite Znth_0_cons.
      sep_apply modus_ponens_wand.
      unfold full_gc.
      Intros.
      sep_apply (is_pointer_or_integer_rep_type_val g outlier nm' q H6).
      entailer!!.
    }
    Exists (n-nm')%nat q.
    replace (n - (n-nm'))%nat with nm' by lia.
    entailer!!.
    split.
    destruct nm'; constructor.
    f_equal. f_equal. lia.
    apply modus_ponens_wand.
  + (* else clause *)
    forward.
    entailer!!.
    destruct (n-m)%nat eqn:?H.
    2: contradiction H4; reflexivity.
    f_equal. f_equal.
     lia.
- (* after the loop *)
 forward. simpl. 
Exists (repZ (Z.of_nat n)) g roots t_info.
 entailer!. split3.
 + simpl. destruct xs.  unfold FM.from_nat. 

 cbn - [Nat.pow].
 admit.
 + apply gc_graph_iso_refl.
 + simpl. unfold odd_Z2val. simpl.
 rewrite Int64.shl_mul_two_p, mul64_repr, add64_repr. 
  unfold two_p. simpl. unfold two_power_pos. simpl.  
  f_equal. f_equal. lia. 
 
Admitted.

#[export] Instance CCE4: change_composite_env filteredCompSpecs CompSpecs.
make_cs_preserve filteredCompSpecs CompSpecs.
Defined.

Lemma body_uint63_to_nat_no_gc_spec :
  semax_body Vprog Gprog
             f_uint63_to_nat_no_gc
             uint63_to_nat_no_gc_spec.
Proof. 
  start_function.
  forward. unfold full_gc. Intros. 
  forward_call (gv, g, outlier).
  rewrite decode_encode_Z by auto.
  forward_while 
  (EX v : rep_type, EX m : nat, EX g' : graph, EX (t_info' : GCGraph.thread_info),
  PROP (is_in_graph g' outlier m v; (m <= n)%nat; 2 * Z.of_nat (n - m) < headroom t_info'; 
  gc_graph_iso g roots g' roots)
   LOCAL (temp _temp (rep_type_val g' v);
   temp _i (Vlong (Int64.repr (Z.of_nat (n - m))));
   temp _tinfo ti;
   gvars gv)
   SEP (full_gc g' t_info' roots outlier ti sh gv)
  ). 

  - (* Before the while *)
    Intros v. Exists v. Exists 0%nat. Exists g. Exists t_info.
    unfold full_gc. entailer!!. 
    split.
    * apply gc_graph_iso_refl.
    * repeat f_equal. lia.
  - (* Valid condition  *)
    entailer!. 
  - (* During the loop *)
    assert (n - m <> 0)%nat by lia.
    forward_call (gv, g', [v], (m%nat; tt) , roots, sh, ti, outlier, t_info').
    { split; simpl; auto. }
    Intros v'.  destruct v' as ((v'&g'')&ti').
    unfold fst, snd in *. 
    forward. 
    Exists (v', S m, g'', ti').
    entailer!!.
    split.
     * eapply gc_graph_iso_trans; eassumption.
     * repeat f_equal.  lia.
  - (* After the loop *)
    forward.  
    Exists v. Exists g'. Exists t_info'.
    entailer!!.
    enough (n- m = 0)%nat.
    { assert (n = m) by lia. subst. eauto. }
    apply repr_inj_unsigned64 in HRE; try rep_lia.
    unfold encode_Z in H0. rep_lia.
Qed.

#[export] Instance CCE: change_composite_env env_graph_gc.CompSpecs CompSpecs.
make_cs_preserve env_graph_gc.CompSpecs CompSpecs.
Defined.

Lemma test_semax_GC_SAVE1:
 forall (n: Z) (Espec : OracleKind)
  (gv : globals) (sh : share)
  (ti : val)
  (outlier : outlier_t)
  (v___ROOT__  v___FRAME__ : val)
  (SH : writable_share sh)
  (v0 : rep_type)
  (m : nat)
  (g : graph)
  (t_info : GCGraph.thread_info)
  (roots : roots_t)
  (ival: val)
  (Hn: 0 <= n <= Int64.max_signed)
  (H2 : is_in_graph g outlier m v0) 
  (GCP : gc_condition_prop g t_info roots outlier)
  (STARTptr : isptr (space_start (heap_head (ti_heap t_info)))),
semax (func_tycontext f_uint63_to_nat Vprog Gprog nil)
  (PROP ( )
   LOCAL (temp _nalloc (Vlong (Int64.repr n));
          temp _save0 (rep_type_val g v0); temp _i ival;
   lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
   lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; temp _tinfo ti; 
   gvars gv)
   SEP (full_gc g t_info roots outlier ti sh gv;
   frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info) 1;
   VST.floyd.library.mem_mgr gv))
  GC_SAVE1
  (normal_ret_assert
     (EX (g' : graph) (v0' : rep_type) (roots' : roots_t)
      (t_info' : GCGraph.thread_info),
      PROP (headroom t_info' >= n; is_in_graph g' outlier m v0';
      gc_condition_prop g' t_info' roots' outlier; 
      gc_graph_iso g roots g' roots';
      frame_shells_eq (ti_frames t_info) (ti_frames t_info'))
      LOCAL (temp _save0 (rep_type_val g' v0'); temp _i ival;
      lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
      lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; temp _tinfo ti; 
      gvars gv)
      SEP (full_gc g' t_info' roots' outlier ti sh gv;
      frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info') 1; 
      VST.floyd.library.mem_mgr gv))%argsassert).
Proof.
intros.
eapply semax_post_flipped'.
eapply semax_Delta_subsumption with GC_SAVE1_tycontext.
apply prove_tycontext_sub; try reflexivity; repeat split; auto.
change _nalloc with specs_general._nalloc.
match goal with |- context [full_gc _ _ _ _ ?ti _ _] =>
 match goal with |- context [temp ?tix ti] =>
   change tix with specs_general._tinfo
 end end.
apply_semax_GC_SAVE1.
simpl app.
apply andp_left2; repeat (let x := fresh "x" in (Intro x; Exists x));
  go_lowerx; autorewrite with norm; cancel.
Qed. 


Lemma body_uint63_to_nat: semax_body Vprog Gprog f_uint63_to_nat uint63_to_nat_spec.
Proof. 
start_function'.
unfold FM.t in x. destruct x as (n&n_lt).
cbn in H0. destruct p; try contradiction. subst.
change (Tpointer _ _) with int_or_ptr_type.
forward.
unfold full_gc. Intros. 
forward_call (gv, g, outlier). 
Intros v.
(* rewrite decode_encode_Z by auto. *)
forward.
forward.
unfold before_gc_thread_info_rep; limited_change_compspecs CompSpecs.
Intros.
forward.
forward.
rewrite Int.signed_repr by rep_lia.
deadvars!.
sep_apply_compspecs CompSpecs 
  (frame_rep__fold Tsh v___FRAME__ v___ROOT__ (ti_fp t_info) 1 (Vlong (Int64.repr 0))).
sep_apply_compspecs CompSpecs (before_gc_thread_info_rep_fold sh t_info ti).
sep_apply (full_gc_fold gv g t_info roots outlier ti sh).

forward_while 
(EX v : rep_type, EX m : nat, EX g' : graph, 
 EX (t_info' : GCGraph.thread_info), EX (roots': roots_t),
 PROP (is_in_graph g' outlier m v; (m <= n)%nat;
      gc_condition_prop g' t_info' roots' outlier;
      gc_graph_iso g roots g' roots';
      frame_shells_eq (ti_frames t_info) (ti_frames t_info'))
 LOCAL (temp _save0 (rep_type_val g' v);
      temp _i (Vlong (Int64.repr (Z.of_nat (n - m))));
      lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
      lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; 
      temp _tinfo ti;
      gvars gv)
SEP (full_gc g' t_info' roots' outlier ti sh gv;
    frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info') 1;
    VST.floyd.library.mem_mgr gv)
). 
- (* Before the while *)
   Exists v O g t_info roots.
   entailer!!. 
   split3.
    * apply gc_graph_iso_refl.
    * apply frame_shells_eq_refl.
    * repeat f_equal. admit. (*  lia. *)
- (* Valid condition  *)
  entailer!!. 
- (* During the loop *)
  rename H4 into GCP. rename H6 into H_frame_shells.
  assert (STARTptr := space_start_isptr' GCP).
  assert (m<n)%nat by lia. clear H3 HRE HRE'. rename H5 into H_iso.
  forward. 
  eapply semax_seq'.
 + eapply semax_Delta_subsumption with GC_SAVE1_tycontext.
   { apply prove_tycontext_sub; try reflexivity; repeat split; auto. }
   apply (@semax_cssub filteredCompSpecs).
   { apply prove_cssub; repeat split; auto; try reflexivity. }
   change _nalloc with specs_general._nalloc.
   match goal with |- context [full_gc _ _ _ _ ?ti _ _] =>
    match goal with |- context [temp ?tix ti] =>
      change tix with specs_general._tinfo
    end end.
   apply_semax_GC_SAVE1.
   { rewrite Int.signed_repr; rep_lia. }
  + simpl app. abbreviate_semax.
  Intros g'' v0' roots'' t_info''.
  rename H7 into H_iso'. 
  pose (m' := existT (fun _ => unit) m tt).
  forward_call (gv, g'', [v0'], m', roots'', sh, ti, outlier, t_info'').
   * split.
     -- split; auto. reflexivity. 
     -- clear - H3. rewrite Int.signed_repr in H3 by rep_lia. rep_lia.
   * Intros vret.
     destruct vret as [[ v2 g'''] t_info'''].
     simpl snd in *. simpl fst in *.
     assert_PROP (gc_condition_prop g''' t_info''' roots'' outlier) as GCP'
        by (unfold full_gc; entailer!!). 
     forward.
     Exists (v2, S m,g''',t_info''',roots''). simpl fst. simpl snd.

     unfold ti_fp.
     replace (Z.of_nat (n - S m)) with (Z.of_nat (n-m)-1) by lia.
     rewrite H11.

     entailer!!.
     split.
     -- eapply gc_graph_iso_trans; try eassumption.
     eapply gc_graph_iso_trans; eassumption.
     -- rewrite <- H11.
     eapply frame_shells_eq_trans; eassumption.
 - (* after the loop *)
   forward.
   assert (m=n). {
    clear - H3 H HRE. unfold encode_Z in H. 
    apply repr_inj_unsigned64 in HRE; try rep_lia. admit.  }
   subst m. unfold model_fn. simpl.
   Exists v0 g' roots' t_info' .
   unfold frame_rep_.
   entailer!!. destruct xs. apply H2. 
Admitted.
