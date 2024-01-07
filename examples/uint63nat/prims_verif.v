Require Import VeriFFI.examples.uint63nat.prims.
Require Import ZArith.
Require Import Psatz.
Require Import CertiGraph.CertiGC.spatial_gcgraph.

Require Import VeriFFI.examples.uint63nat.specs.

#[export] Instance CCE3: change_composite_env Verif_prog_general.CompSpecs CompSpecs.
make_cs_preserve Verif_prog_general.CompSpecs CompSpecs.
Defined.

Definition description_S := @desc _ S _. 

Lemma decode_encode_Z: 
  forall n, min_signed <= encode_Z (Z.of_nat n) <= max_signed ->
  Int64.shru (Int64.repr (encode_Z (Z.of_nat n)))
              (Int64.repr (Int.unsigned (Int.repr 1)))
               = Int64.repr (Z.of_nat n).
Proof.
intros.
unfold encode_Z, min_signed, max_signed in *.
autorewrite with norm. rewrite Int64.shru_div_two_p.
change (two_p _) with 2.
rewrite !Int64.unsigned_repr by  rep_lia.
rewrite Z.div_add_l by lia.
simpl Z.div; rewrite Z.add_0_r.
auto.
Qed.


Lemma body_uint63_from_nat:
  semax_body Vprog Gprog f_uint63_from_nat uint63_from_nat_spec.
Proof.
 start_function. 
 forward.
 fold (rep_type_val g p).
 forward.
 rewrite Int.signed_repr 
   by (unfold encode_Z, max_signed in H; rep_lia).
 forward_loop ( EX m : nat, EX p': rep_type,
        PROP ( (m <= n)%nat; is_in_graph g (n - m)%nat p';        
              nat_has_tag_prop (n - m)%nat (nat_get_desc (n-m)%nat))
        LOCAL (temp _i (Vlong (Int64.repr (Z.of_nat m))); 
               temp _temp (rep_type_val g p');
               temp _n (rep_type_val g p); gvars gv) 
        SEP (full_gc g t_info roots outlier ti sh gv)
    )
   break: (PROP()LOCAL(temp _i (Vlong (Int64.repr (Z.of_nat n))))
           SEP(full_gc g t_info roots outlier ti sh gv)).
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
      sep_apply (is_pointer_or_integer_rep_type_val g nm' q H6).
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
    f_equal. f_equal. lia.
- (* after the loop *)
 forward.
 apply prop_right.
 f_equal. 
 rewrite Int64.shl_mul_two_p, mul64_repr, add64_repr.
 reflexivity.
Qed.

Lemma body_uint63_to_nat_no_gc_spec :
  semax_body Vprog Gprog
             f_uint63_to_nat_no_gc
             uint63_to_nat_no_gc_spec.
Proof. 
  start_function.
  forward. unfold full_gc. Intros. 
  forward_call (gv, g).
  rewrite decode_encode_Z by auto.
  forward_while 
  (EX v : rep_type, EX m : nat, EX g' : graph, EX (t_info' : GCGraph.thread_info),
  PROP (is_in_graph g' m v; (m <= n)%nat; 2 * Z.of_nat (n - m) < headroom t_info'; 
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
    unfold full_gc. 
    unfold before_gc_thread_info_rep.
    unfold spatial_gcgraph.before_gc_thread_info_rep.
    forward_call (gv, g', [v], (m%nat; tt) , roots, sh, ti, outlier, t_info').
    split; simpl; auto.
    Intros v'.  destruct v' as ((v'&g'')&ti').
    unfold fst, snd in *. 
    forward. 
    Exists (v', S m, g'', ti').
    entailer!!.
    split.
     + eapply gc_graph_iso_trans; eassumption.
     + repeat f_equal.  lia.
  -
    forward.  
    Exists v. Exists g'. Exists t_info'.
    entailer!!.
    enough (n- m = 0)%nat.
    { assert (n = m) by lia. subst. eauto. }
    apply repr_inj_unsigned64 in HRE; try rep_lia.
    unfold encode_Z in H0.
    unfold min_signed, max_signed in H0. rep_lia.
Qed.

#[export] Instance CCE: change_composite_env env_graph_gc.CompSpecs CompSpecs.
make_cs_preserve env_graph_gc.CompSpecs CompSpecs.
Defined.

Lemma gc_preserved {A: Type} `{InG: InGraph A}:
  forall (g1 :graph) (roots1: list root_t)
         (g2: graph) (roots2: list root_t),
    gc_graph_iso g1 roots1 g2 roots2 ->
    graph_unmarked g2 /\ no_backward_edge g2 /\ no_dangling_dst g2 ->
    forall (a: A) (n: Z),
      0 <= n < Zlength roots1 ->
    @graph_predicate _ (@in_graph_pred _ InG) g1 a (rep_type_of_root_t (Znth n roots1)) ->
    @graph_predicate _ (@in_graph_pred _ InG) g2 a (rep_type_of_root_t (Znth n roots2)).
Admitted.

Lemma gc_preserved_nat: 
  forall (g1 :graph) (roots1: list root_t)
         (g2: graph) (roots2: list root_t),
    gc_graph_iso g1 roots1 g2 roots2 ->
    graph_unmarked g2 /\ no_backward_edge g2 /\ no_dangling_dst g2 ->
    forall (a: nat) (n: Z),
      0 <= n < Zlength roots1 ->
    @graph_predicate _ (@in_graph_pred _ InGraph_nat) g1 a (rep_type_of_root_t (Znth n roots1)) ->
    @graph_predicate _ (@in_graph_pred _ InGraph_nat) g2 a (rep_type_of_root_t (Znth n roots2)).
Proof.
apply @gc_preserved.  (* Kathrin: replace this proof with a real one *)
Qed.

(* OOPS!  Ideally, this should be moved to verification/specs_general.v,
  but unfortunately it depends on the specific
   func_tycontext f_uint63_to_nat Vprog Gprog nil.
 Ideally there is some sort of tycontext-inclusion principle
 for proving the general lemma in the minimal tycontext,
 and using it in specific tycontexts such as f_uint63_to_nat. *) 
Lemma semax_GC_SAVE1:
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
  (Hn: 0 <= n <= Int.max_signed)
  (H2 : is_in_graph g m v0) 
  (GCP : gc_condition_prop g t_info roots outlier)
  (STARTptr : isptr (space_start (heap_head (ti_heap t_info)))),
semax (func_tycontext f_uint63_to_nat Vprog Gprog nil)
  (PROP ( )
   LOCAL (temp _save0 (rep_type_val g v0);
   lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
   lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; temp _tinfo ti; 
   gvars gv)
   SEP (full_gc g t_info roots outlier ti sh gv;
   frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info) 1;
   library.mem_mgr gv))
  (GC_SAVE1 n)
  (normal_ret_assert
     (EX (g' : graph) (v0' : rep_type) (roots' : roots_t)
      (t_info' : GCGraph.thread_info),
      PROP (headroom t_info' >= n; is_in_graph g' m v0';
      gc_condition_prop g' t_info' roots' outlier; 
      gc_graph_iso g roots g' roots';
      frame_shells_eq (ti_frames t_info) (ti_frames t_info'))
      LOCAL (temp _save0 (rep_type_val g' v0');
      lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
      lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; temp _tinfo ti; 
      gvars gv)
      SEP (full_gc g' t_info' roots' outlier ti sh gv;
      frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info') 1; 
      library.mem_mgr gv))%argsassert).
Proof.
intros.
assert (H5 := I).
assert (H4 := I).
assert (H0 := I).
assert (H1 := I).
assert (H := I).
unfold GC_SAVE1.
abbreviate_semax.

  unfold full_gc.
  unfold before_gc_thread_info_rep;  limited_change_compspecs CompSpecs.
  Intros.
  forward.
  forward.
  destruct (space_start (heap_head (ti_heap t_info))) eqn:STARTeq; try contradiction.
  rename b into startb; rename i into starti.
  forward_if.
 + apply prop_right; simpl. destruct (peq startb startb); try contradiction. auto.
 +
  forward.
  forward.
  unfold frame_rep_; limited_change_compspecs CompSpecs.
  Intros.
  forward.
  forward.
  deadvars!.
  change (upd_Znth 0 _ _) with [rep_type_val g v0].
  change (Tpointer tvoid _) with int_or_ptr_type.
  assert_PROP (force_val (sem_add_ptr_int int_or_ptr_type Signed v___ROOT__ (Vint (Int.repr 1))) =
      offset_val (sizeof int_or_ptr_type * 1) v___ROOT__)  as H99;
      [ entailer! | rewrite H99; clear H99].

  sep_apply_compspecs CompSpecs 
      (frame_rep_fold sh v___FRAME__ v___ROOT__ (ti_fp t_info) 1 [rep_type_val g v0]).
  unfold ti_fp.
  sep_apply (frames_rep_cons sh v___FRAME__ v___ROOT__ [rep_type_val g v0] (ti_frames t_info)).
  compute; clear; congruence.
  set (frames'' := _ :: ti_frames t_info).
  pose (t_info' := {| ti_heap_p := ti_heap_p t_info; ti_heap := ti_heap t_info;
                      arg_size := arg_size t_info; ti_frames := frames'';
                      ti_nalloc := Ptrofs.repr n |}).
  change frames'' with (ti_frames t_info').
  rewrite Int.signed_repr by rep_lia.
  change (ti_args t_info) with (ti_args t_info').
  change (ti_heap_p t_info) with (ti_heap_p t_info').
  clear H3.
  forward_call (Ers, sh, gv, ti, g, t_info', root_t_of_rep_type v0 :: roots, outlier).
  *
   unfold before_gc_thread_info_rep; limited_change_compspecs CompSpecs.
   rewrite <- STARTeq.
   change (ti_heap t_info) with (ti_heap t_info').
   change (ti_fp t_info') with v___FRAME__.
   change (ti_nalloc t_info') with (Ptrofs.repr n).
   replace (Vptrofs (Ptrofs.repr n)) with (Vlong (Int64.repr n))
     by (rewrite Vptrofs_unfold_true by reflexivity;
         rewrite ptrofs_to_int64_repr by reflexivity; auto).
   cancel.
  * simpl.
    split3; try apply GCP.
    red in GCP.
    split3. apply GCP. 2: split; try apply GCP. 
    --
     subst frames''; clear t_info'.
     unfold frames2rootpairs. simpl concat.
     unfold rootpairs_compatible. simpl.
     f_equal.  destruct v0; auto.
     change (rootpairs_compatible g (frames2rootpairs (ti_frames t_info)) roots).
     apply GCP.
    -- decompose [and] GCP; clear GCP. 
       red in H7; decompose [and] H7; clear H7.
       destruct H11.
       split. 
       ++ clear t_info' frames'' STARTptr STARTeq startb starti.
          unfold root_t_of_rep_type.
          destruct v0; auto.
          red in H7|-*. simpl.
          change (?A :: ?B) with ([A]++B).
          apply incl_app; auto.
          unfold is_in_graph in H2.
          destruct m; simpl in H2; try contradiction.
          destruct H2 as [? [? ? ]  ]; contradiction.
       ++ destruct v0; try apply H11. constructor; auto.
          clear - H2. unfold is_in_graph in H2.
          apply has_v in H2; auto.
  * (* after the call to garbage_collect() *)
   Intros vret. destruct vret as [ [g3 t_info3] roots3].
   simpl snd in *. simpl fst in *.
   rename H9 into FSE. rename H10 into ROOM.
   forward.
   unfold before_gc_thread_info_rep; limited_change_compspecs CompSpecs.
   simpl in FSE. unfold frames'' in FSE.
   remember (ti_frames t_info3) as frames3.
   inversion FSE; clear FSE. subst r1 fr1.
   destruct fr2 as [a3 r3 s3]; simpl in H11, H12, H13.
   subst a3 r3.
   destruct s3 as [ | v0x s3]. exfalso; clear - H13; list_solve.
   destruct s3. 2: exfalso; clear - H13; list_solve.
   subst frames3.
   sep_apply (frames_rep_pop sh v___FRAME__ v___ROOT__ [v0x] r2).
   compute; clear; congruence.
   unfold frame_rep at 1.
   Intros. change (Zlength [_]) with 1.
   assert (roots_graph_compatible (root_t_of_rep_type v0 :: roots) g). {
       destruct GCP as [_ [ [ _ [ _ [ [ _ RGC ] _ ] ] ] _ ] ].
       destruct v0; try apply RGC.
       constructor; auto.
       red in H2.
       eapply has_v; eauto.
    }
   assert (ISO: gc_graph_iso g (root_t_of_rep_type v0 :: roots) g3 roots3). {
     red in H6; decompose [and] H6.
     apply garbage_collect_isomorphism; auto; try apply GCP.
    }
   assert (exists v0', exists roots3',
        v0x = rep_type_val g3 v0' /\ is_in_graph g3 m v0' /\ roots3 = root_t_of_rep_type v0' :: roots3'). {
       rewrite <- H14 in H3. simpl frames2rootpairs in H3.
    pose proof @gc_preserved _ InGraph_nat _ _ _ _ ISO ltac:(clear - H7; red in H7; tauto)
    m 0 ltac:(clear; Zlength_solve).
    rewrite Znth_0_cons,rep_type_of_root_t_of_rep_type in H10.
    specialize (H10 H2).
    exists (rep_type_of_root_t (Znth 0 roots3)), (sublist 1 (Zlength roots3) roots3).
    rewrite root_t_of_rep_type_of_root_t.
    split3; auto.
    destruct H3 as [_ [H3 _] ].
    red in H3. simpl in H3.
    assert (v0x = root2val g3 (Znth 0 roots3)) by list_solve.
    rewrite H11.
    destruct (Znth 0 roots3); try destruct s ; auto.
    apply graph_iso_Zlength in ISO.    
    clear - ISO. rewrite Zlength_cons in ISO. 
    destruct roots3; autorewrite with sublist in ISO. rep_lia.
    autorewrite with sublist.
    f_equal. rewrite sublist_S_cons by lia.
    rewrite Z.sub_diag. unfold Z.succ.
    rewrite sublist_same by lia. auto.
    }
   destruct H10 as [v0' [roots3' [ ? [? ?] ] ] ].
   subst v0x roots3.
   limited_change_compspecs CompSpecs.
   forward. entailer!!. rewrite Znth_0_cons. { 
        destruct v0'; simpl; auto. destruct g0; simpl; auto.
        apply has_v in H11. destruct H11 as [? _].
        pose proof (graph_has_gen_start_isptr _ _ H10).
        unfold vertex_address.
        destruct (gen_start g3 (vgeneration _)); auto.
    }
   forward.  
   forward.
   pose (t_info4 := {|
      ti_heap_p := ti_heap_p t_info3;
      ti_heap := ti_heap t_info3;
      ti_args := ti_args t_info3;
      arg_size := arg_size t_info3;
      ti_frames := r2;
      ti_nalloc := ti_nalloc t_info3
    |} ).
   Exists g3 v0' roots3' t_info4.
   rewrite Znth_0_cons.
    unfold full_gc.
    entailer!!.
    --  assert (gc_condition_prop g3 t_info4 roots3' outlier). {
      unfold gc_condition_prop, garbage_collect_condition.
      change (ti_heap t_info4) with (ti_heap t_info3).
      repeat simple apply conj; try apply GCP; try apply H7; auto.
      - destruct H3 as [? [? [ ?  ? ] ] ].
        destruct H12.
        red; unfold roots_compatible; repeat simple apply conj; auto.
        + rewrite <- H14 in H10.
            unfold frames2rootpairs in H10. simpl in H10.
            red in H10. simpl in H10. inversion H10; subst; auto.
        +  red in H12|-*.
            destruct (root_t_of_rep_type v0') as [ [ | ] | ]; simpl in H12; auto.
            eapply incl_app_inv_r with (l1:=[g0]); auto.
        + destruct (root_t_of_rep_type v0') as [ [ | ] | ]; simpl in H17; auto.
              red in H17|-*. simpl in H17. inversion H17; subst; auto. 
       - eapply gc_sound; eauto. apply GCP.
       - apply graph_unmarked_copy_compatible; apply H7.
    }
    repeat simple apply conj; auto.
      ++ simpl ti_heap.
         clear - Hn ROOM. simpl in ROOM.
         rewrite Ptrofs.unsigned_repr in ROOM by rep_lia.
         unfold headroom. simpl.  lia.
      ++ apply gc_graph_iso_cons_roots_inv in ISO; auto.
    -- unfold before_gc_thread_info_rep, frame_rep_.
      limited_change_compspecs CompSpecs.
      unfold ti_fp. 
      unfold t_info4; simpl.
      replace (Vlong (Ptrofs.to_int64 (ti_nalloc t_info3))) with (Vptrofs (ti_nalloc t_info3))
        by (rewrite Vptrofs_unfold_true by reflexivity; reflexivity).
      cancel.
      generalize (frame_rep_unfold sh v___FRAME__ v___ROOT__ (frames_p r2) 1 [rep_type_val g3 v0']);
        limited_change_compspecs CompSpecs; intro Hx; apply Hx; clear Hx; auto.
      compute; clear; congruence.
  + forward.
    apply headroom_check in H3; [ | rep_lia].
    Exists g v0 roots t_info.
    unfold full_gc, before_gc_thread_info_rep.
    rewrite <- STARTeq.
    limited_change_compspecs CompSpecs.
    entailer!!.
    split.
    apply gc_graph_iso_refl.
    apply frame_shells_eq_refl.
Qed.

Ltac apply_semax_GC_SAVE1 :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ (normal_ret_assert ?Post) =>
  let Q1 := get_rep_temps _tinfo Q in
  let Q2 := get_nonrep_temps _tinfo Q in
  let R1 := get_gc_mpreds R in
  let R2 := get_nongc_mpreds R in
 eapply (semax_frame_PQR'' Q1 Q2 R1 R2); 
  [solve [auto 50 with closed] 
  | solve [go_lowerx; autorewrite with norm; cancel]
  | apply perhaps_gc_1_live_root_aux
  | eapply semax_GC_SAVE1; eauto ]
 end.

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
  (Hn: 0 <= n <= Int.max_signed)
  (H2 : is_in_graph g m v0) 
  (GCP : gc_condition_prop g t_info roots outlier)
  (STARTptr : isptr (space_start (heap_head (ti_heap t_info)))),
semax (func_tycontext f_uint63_to_nat Vprog Gprog nil)
  (PROP ( )
   LOCAL (temp _save0 (rep_type_val g v0); temp _i ival;
   lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
   lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; temp _tinfo ti; 
   gvars gv)
   SEP (full_gc g t_info roots outlier ti sh gv;
   frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info) 1;
   library.mem_mgr gv))
  (GC_SAVE1 n)
  (normal_ret_assert
     (EX (g' : graph) (v0' : rep_type) (roots' : roots_t)
      (t_info' : GCGraph.thread_info),
      PROP (headroom t_info' >= n; is_in_graph g' m v0';
      gc_condition_prop g' t_info' roots' outlier; 
      gc_graph_iso g roots g' roots';
      frame_shells_eq (ti_frames t_info) (ti_frames t_info'))
      LOCAL (temp _save0 (rep_type_val g' v0'); temp _i ival;
      lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
      lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; temp _tinfo ti; 
      gvars gv)
      SEP (full_gc g' t_info' roots' outlier ti sh gv;
      frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info') 1; 
      library.mem_mgr gv))%argsassert).
Proof.
intros.
eapply semax_post_flipped'.
apply_semax_GC_SAVE1.
simpl app.
apply andp_left2; repeat (let x := fresh "x" in (Intro x; Exists x));
  go_lowerx; autorewrite with norm; cancel.
Qed.

Lemma body_uint63_to_nat: semax_body Vprog Gprog f_uint63_to_nat uint63_to_nat_spec.
Proof. 
start_function.
change (Tpointer _ _) with int_or_ptr_type.
forward. unfold full_gc. Intros.
forward_call (gv, g). 
Intros v.
rewrite decode_encode_Z by auto.
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
 PROP (is_in_graph g' m v; (m <= n)%nat;
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
    library.mem_mgr gv)
). 
- (* Before the while *)
   Exists v O g t_info roots.
   entailer!!. 
   split3.
    * apply gc_graph_iso_refl.
    * apply frame_shells_eq_refl.
    * repeat f_equal. lia.
- (* Valid condition  *)
  entailer!!. 
- (* During the loop *)
  rename H4 into GCP. rename H6 into H4.
  assert (STARTptr := space_start_isptr' GCP).
  assert (m<n)%nat by lia. clear H3 HRE HRE'. rename H6 into HRE.
  eapply semax_seq'.
  apply_semax_GC_SAVE1. rep_lia.
  simpl app.
  abbreviate_semax.
  Intros g4 v0' roots4 t_info4.
  pose (m' := existT (fun _ => unit) m tt).
  forward_call (gv, g4, [v0'], m', roots4, sh, ti, outlier, t_info4).
   * split; auto. reflexivity.
   * Intros vret.
     destruct vret as [ [ v2 g5] t_info5].
     simpl snd in *. simpl fst in *.
     assert_PROP (gc_condition_prop g5 t_info5 roots4 outlier) as GCP'
        by (unfold full_gc; entailer!!). 
     simpl in H10.
     forward.
     Exists (v2, S m,g5,t_info5,roots4). simpl fst. simpl snd.
     unfold ti_fp.
     replace (Z.of_nat (n - S m)) with (Z.of_nat (n-m)-1) by lia.
     rewrite H13.
     entailer!!.
     split.
     eapply gc_graph_iso_trans; try eassumption.
     eapply gc_graph_iso_trans; try eassumption.
     rewrite <- H13.
     eapply frame_shells_eq_trans; try eassumption.
 - (* after the loop *)
   forward.
   assert (m=n). {
    clear - H3 H HRE. unfold encode_Z, min_signed, max_signed in H. 
    apply repr_inj_unsigned64 in HRE; rep_lia.
   }
   subst m.
   Exists v0 g' t_info' roots'.
   unfold frame_rep_.
   entailer!!.
Qed.
