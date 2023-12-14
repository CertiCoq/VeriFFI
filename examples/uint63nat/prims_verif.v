Require Import VeriFFI.examples.uint63nat.prims.
Require Import ZArith.
Require Import Psatz.
Require Import VeriFFI.examples.uint63nat.specs.

Definition description_S := @desc _ S _. 

(* Lemma body_uint63_from_nat_spec :
  semax_body Vprog Gprog
             f_uint63_from_nat
             uint63_from_nat_spec.
Proof.
    start_function. 
    forward. replace (match p with
    | repZ y => odd_Z2val y
    | repOut p0 => GC_Pointer2val p0
    | repNode v => vertex_address g v
    end) with (rep_type_val g p) by reflexivity. 
    forward.
    (* TODO: forward_loop *)
    forward_loop.

    (* Issue report.
    TODO: What does this error tell me? Where should I look? *)
    forward_call (gv, g, p, n, roots, sh, ti, outlier, t_info). 
    forward_while ( EX   (m : nat) p',
        PROP ( is_in_graph g (n - m)%nat p';        
              nat_has_tag_prop (n - m)%nat (nat_get_desc (n-m)%nat))
        LOCAL (temp _t (Vint (Int.repr (Z.of_nat (ctor_tag (nat_get_desc (n - m))))));
        temp _i (Vlong (Int64.repr (Int.signed (Int.repr (Z.of_nat m))))); temp _temp (rep_type_val g p');
        temp _n (rep_type_val g p))  SEP (full_gc g t_info roots outlier ti sh)
    ). 
    - (* Before the loop. *)
      Exists 0%nat.  Exists p. 
      assert ((n -0)%nat = n)  as -> by lia; eauto. 
      entailer!. 
    - (* Condition *)
      entailer!. 
    - (* During the loop. *)
      forward.  autorewrite with norm.
      (* Todo: With HRE. *)
      assert (exists nm', S nm' = (n - m)%nat) as (nm'&eq_nm') by admit. 
      forward_call (gv, g, p', (nm'; tt), roots, sh, ti, outlier, f_info, t_info). 
      { rewrite <- eq_nm' in H1. apply H1. }
      Intros p_nm'.
      autorewrite with norm in *. 
      forward.
      { entailer!. admit. } (* structural stuff, should be easy *)
      forward_call (gv, g, p_nm', nm', roots, sh, ti, outlier, f_info, t_info).
         + sep_apply wand_frame_elim'; entailer!.
         +  admit. (* with H2 - same unfolding problem... *)
         + forward.
           autorewrite with norm. 
           Exists (S m, p_nm').
           entailer!. 
           split3. 
           * (* with H2 - same unfolding problem... *)
             admit. 
           * assert (nm' = n - S m)%nat as -> by lia. eauto.
           * split. 
            --  repeat f_equal. lia.
            -- f_equal. f_equal. admit. (*  autorewrite with norm.  lia.  *)
    - (* After the loop. *)
      assert (n = m)%nat by admit. subst.
      forward.
      { entailer!. }
      entailer!.  
      autorewrite with norm.
      f_equal. unfold encode_Z. 
      unfold encode_Z in H. unfold Int64.max_signed in H. 
      autorewrite with norm. 
      rewrite Int64.shl_mul_two_p. autorewrite with norm. unfold two_p. 
      unfold two_power_pos. 
      rewrite !Int.signed_repr; try rep_lia. 
      f_equal. 
      split; try rep_lia. unfold max_signed in *. unfold Int.max_signed. clear - H. simpl in *.
      rewrite Z.mul_comm in H. 

      (* Todo: Work on postcondition. *)
     admit.
Admitted. *)


Lemma body_uint63_to_nat_no_gc_spec :
  semax_body Vprog Gprog
             f_uint63_to_nat_no_gc
             uint63_to_nat_no_gc_spec.
Proof. 
  start_function.
  forward. unfold full_gc. Intros. 
  forward_call (gv, g). 
   assert ( Vlong (Int64.shru (Int64.repr (encode_Z (Z.of_nat n))) (Int64.repr (Int.unsigned (Int.repr 1)))) = Vlong (Int64.repr  (Z.of_nat n)))  as ->.
    { unfold encode_Z. 
    autorewrite with norm. rewrite Int64.shru_div_two_p. 
    unfold two_p. simpl. 
    
    admit. (* TODO *)  } 
  (*   Print bool_type. *)


  forward_while 
  (EX v : rep_type, EX m : nat, EX g' : graph, EX (t_info' : GCGraph.thread_info),
  PROP (is_in_graph g' m v; (m <= n)%nat; Z.of_nat (n - m) < headroom t_info; 
  gc_graph_iso g roots g' roots)
   LOCAL (temp _temp (rep_type_val g' v);
   temp _i (Vlong (Int64.repr (Z.of_nat (n - m))));
   temp _tinfo ti; temp _t (Vlong (Int64.repr (Z.of_nat n)));
   gvars gv)
   SEP (full_gc g' t_info' roots outlier ti sh gv)
  ). 

  - (* Before the while *)
    Intros v. Exists v. Exists 0%nat. Exists g. Exists t_info. entailer!. 
    + split3.
      * apply gc_graph_iso_refl.
      * repeat f_equal. lia.
      * admit. 
    +  unfold full_gc. entailer!. 
  - (* Valid condition  *)
    entailer!. 
  - (* During the loop *)
    assert (n - m <> 0)%nat by lia.
    unfold full_gc. 
    unfold before_gc_thread_info_rep.
    unfold spatial_gcgraph.before_gc_thread_info_rep.
    forward_call (gv, g', [v], (m%nat; tt) , roots, sh, ti, outlier, t_info'). 
    { (* Requiring to unfold. *)
       admit. }
    Intros v'.  destruct v' as ((v'&g'')&ti').
    unfold fst, snd in *. 
     forward. 
     Exists (v', S m, g'', ti').
     entailer!.
     split; eauto. 
     + eapply gc_graph_iso_trans; eauto.  
     + repeat f_equal.  lia. 

  -
    forward. 
  
    Exists v. Exists g'. Exists t_info'.
    entailer!.
    enough (n- m = 0)%nat.
    { assert (n = m) by lia. subst. eauto. }
    apply repr_inj_unsigned64 in HRE; try rep_lia.
    unfold encode_Z in H0.
    unfold min_signed, max_signed in H0. rep_lia.
all: fail.
Admitted.


#[export] Instance CCE: change_composite_env env_graph_gc.CompSpecs CompSpecs.
make_cs_preserve env_graph_gc.CompSpecs CompSpecs.
Defined.

#[export] Instance CCE2: change_composite_env env_graph_gc.CompSpecs CompSpecs.
make_cs_preserve env_graph_gc.CompSpecs CompSpecs.
Defined.

Lemma before_gc_thread_info_rep_fold:
  forall sh t_info (ti: val),
  data_at sh env_graph_gc.thread_info_type
   (offset_val (WORD_SIZE * used_space (heap_head (ti_heap t_info))) (space_start (heap_head (ti_heap t_info))),
    (offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info))) (space_start (heap_head (ti_heap t_info))),
     (ti_heap_p t_info,
      (ti_args t_info,
        (spatial_gcgraph.ti_fp t_info, (Vptrofs (ti_nalloc t_info), nullval)))))) ti
  * spatial_gcgraph.frames_rep sh (ti_frames t_info)
  * spatial_gcgraph.heap_struct_rep sh
      ((space_start (heap_head (ti_heap t_info)),
       (Vundef,
       (offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info))) (space_start (heap_head (ti_heap t_info))),
         offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info))) (space_start (heap_head (ti_heap t_info))))))
         :: map spatial_gcgraph.space_tri (tl (spaces (ti_heap t_info))))
      (ti_heap_p t_info)
  * spatial_gcgraph.heap_rest_rep (ti_heap t_info) 
  |-- before_gc_thread_info_rep sh t_info ti.
Proof.
 intros.
 unfold before_gc_thread_info_rep.
 unfold spatial_gcgraph.before_gc_thread_info_rep.
 change_compspecs CompSpecs.
 cancel.
Qed.

Lemma frames_rep_cons:
 forall vf vr vl frames
  (SIZE: WORD_SIZE * Zlength vl <= Ptrofs.max_signed),
 (frame_rep vf vr (spatial_gcgraph.frames_p frames) vl *
  spatial_gcgraph.frames_rep Tsh frames)%logic
 = spatial_gcgraph.frames_rep Tsh 
     ({|fr_adr:=vf; fr_root:=vr; fr_roots := vl|}::frames).
Proof.
intros.
unfold frame_rep.
simpl.
unfold tarray.
unfold spatial_gcgraph.frames_rep.
unfold frames2rootpairs.
simpl map.
change (concat (?A :: ?B)) with (A ++ concat B).
fold (frames2rootpairs frames).
unfold spatial_gcgraph.roots_rep.
rewrite iter_sepcon.iter_sepcon_app_sepcon.
unfold spatial_gcgraph.frames_shell_rep; fold (spatial_gcgraph.frames_shell_rep Tsh frames).
unfold frame2rootpairs.
simpl.
change gc_stack._stack_frame with _stack_frame.
change_compspecs CompSpecs.
match goal with |- ?A = ?B =>
 transitivity (!! (@field_compatible0 env_graph_gc.CompSpecs (tarray int_or_ptr_type (@Zlength val vl)) [] vr) && A)%logic
 end.
 { apply pred_ext; entailer!.
   apply field_compatible_field_compatible0.
   unfold tarray.
   apply field_compatible_change_composite; try apply H1.
 }
 normalize.
 apply andp_prop_ext. tauto.
 intro.
 rewrite spatial_gcgraph.iter_sepcon_frame2rootpairs' by auto.
replace  (field_address0 (tarray int_or_ptr_type (Zlength vl)) (SUB Zlength vl) vr)
with (offset_val (8 * Zlength vl) vr).
2:{ unfold field_address0.
  rewrite if_true. simpl. auto.
   eapply field_compatible0_cons_Tarray; [ | apply H| ].
   reflexivity. rep_lia.
}
change_compspecs CompSpecs.
apply pred_ext; cancel.
Qed.

Lemma frames_rep_push:
 forall vf vr vl frames
  (SIZE: WORD_SIZE * Zlength vl <= Ptrofs.max_signed),
frame_rep vf vr (spatial_gcgraph.frames_p frames) vl *
spatial_gcgraph.frames_rep Tsh frames
|-- spatial_gcgraph.frames_rep Tsh 
     ({|fr_adr:=vf; fr_root:=vr; fr_roots := vl|}::frames).
Proof.
intros.
rewrite frames_rep_cons by auto. auto.
Qed.


Lemma frames_rep_pop:
 forall vf vr vl frames
  (SIZE: WORD_SIZE * Zlength vl <= Ptrofs.max_signed),
 spatial_gcgraph.frames_rep Tsh 
     ({|fr_adr:=vf; fr_root:=vr; fr_roots := vl|}::frames)
|-- frame_rep vf vr (spatial_gcgraph.frames_p frames) vl *
    spatial_gcgraph.frames_rep Tsh frames.
Proof.
intros.
rewrite frames_rep_cons by auto. auto.
Qed.


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


Lemma gc_graph_iso_uncons:
   (* Shengyi will try to add this lemma to CertiGG *)
   forall (g1 : graph) (p1: root_t) (roots1 : roots_t) (g2 : graph) (p2: root_t) (roots2: roots_t),
   gc_graph_iso g1 (p1 :: roots1) g2 (p2 :: roots2) ->
   gc_graph_iso g1 roots1 g2 roots2.
Admitted.

Lemma frame_shells_eq_refl: forall frs, frame_shells_eq frs frs.
Proof.
induction frs.
constructor.
constructor; auto.
Qed.


Lemma frame_shells_eq_trans: transitive _ frame_shells_eq.
Proof.
hnf; intros.
revert z H0.
induction H; intros; auto.
inversion H3; clear H3; subst.
constructor; auto; congruence. 
Qed.

Lemma body_uint63_to_nat :
  semax_body Vprog Gprog
             f_uint63_to_nat
             uint63_to_nat_spec.
Proof. 
start_function.
forward. unfold full_gc. Intros.
 
forward_call (gv, g). 
Intros v.
assert ( Vlong (Int64.shru (Int64.repr (encode_Z (Z.of_nat n))) (Int64.repr (Int.unsigned (Int.repr 1)))) = Vlong (Int64.repr  (Z.of_nat n)))  as ->.
  { unfold encode_Z in *.
  f_equal.  
  autorewrite with norm. rewrite Int64.shru_div_two_p.
  rewrite !Int64.unsigned_repr by (unfold min_signed, max_signed in *; rep_lia).
  f_equal.
  unfold two_p.
  change (two_power_pos 1) with 2.
  rewrite Z.div_add_l by lia.
  simpl. lia.
 }
forward.
forward.
unfold before_gc_thread_info_rep, spatial_gcgraph.before_gc_thread_info_rep.
change_compspecs CompSpecs.
Intros.
forward.
   { sep_apply spatial_gcgraph.frames_rep_ptr_or_null. entailer!!. }
forward.
rewrite Int.signed_repr by rep_lia.
generalize (frame_rep__fold v___FRAME__ v___ROOT__ (spatial_gcgraph.ti_fp t_info) 1 (Vlong (Int64.repr 0)));
change_compspecs CompSpecs; intro Hx; sep_apply Hx; clear Hx.
sep_apply before_gc_thread_info_rep_fold.
sep_apply (full_gc_fold gv g t_info roots outlier ti sh).
forward_while 
(EX v : rep_type, EX m : nat, EX g' : graph, EX (t_info' : GCGraph.thread_info), EX (roots': roots_t),
PROP (is_in_graph g' m v; (m <= n)%nat;
gc_condition_prop g' t_info' roots' outlier;
gc_graph_iso g roots g' roots';
ti_heap_p t_info'=ti_heap_p t_info; (* not needed? *)
frame_shells_eq (ti_frames t_info) (ti_frames t_info'))
LOCAL (temp _temp (rep_type_val g' v);
temp _i (Vlong (Int64.repr (Z.of_nat (n - m))));
   lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
   lvar ___ROOT__
     (tarray int_or_ptr_type 1)
     v___ROOT__; 
temp _tinfo ti; temp _t (Vlong (Int64.repr (encode_Z (Z.of_nat n))));
gvars gv)
SEP (full_gc g' t_info' roots' outlier ti sh gv;
    frame_rep_ v___FRAME__ v___ROOT__ (spatial_gcgraph.ti_fp t_info') 1;
    library.mem_mgr gv)
). 
- (* Before the while *)
   Exists v. Exists 0%nat. Exists g. Exists t_info. Exists roots. entailer!. 
  + split3.
    * apply gc_graph_iso_refl.
    * apply frame_shells_eq_refl.
    * repeat f_equal. lia.
- (* Valid condition  *)
  entailer!!. 
- (* During the loop *)
  rename H4 into GCP. rename H7 into H4.
  assert (STARTptr: isptr (space_start (heap_head (ti_heap t_info')))). {
    red in GCP; decompose [and] GCP.
    destruct (heap_head_cons (ti_heap t_info')) as [s [l [C1 C2]  ] ].
    rewrite C2.
    replace s with (Znth 0 (spaces (ti_heap t_info'))) by (rewrite C1; reflexivity).
    apply space_start_isptr with g'; auto.
    rewrite C1; clear; list_solve.
    apply graph_has_gen_O.
  }
  assert (n - m <> 0)%nat by lia.
  unfold full_gc.
  unfold before_gc_thread_info_rep.
  unfold spatial_gcgraph.before_gc_thread_info_rep.
  Intros.
  change_compspecs CompSpecs.
  forward.
  forward.
  destruct (space_start (heap_head (ti_heap t_info'))) eqn:STARTeq; try contradiction.
  rename b into startb; rename i into starti.
  forward_if (
     EX g'': graph, EX v0':_, EX roots':_, EX t_info' : GCGraph.thread_info,
     PROP ( total_space (heap_head (ti_heap t_info')) - used_space (heap_head (ti_heap t_info')) >= 2;
            is_in_graph g'' m v0';
            gc_condition_prop g'' t_info' roots' outlier;
            gc_graph_iso g roots g'' roots';
            ti_heap_p t_info'=ti_heap_p t_info; (* not needed?*)
            frame_shells_eq (ti_frames t_info) (ti_frames t_info'))
     LOCAL (temp _temp (rep_type_val g'' v0');
     temp _i (Vlong (Int64.repr (Z.of_nat (n-m))));
     lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
     lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; 
     temp _tinfo ti; temp _t (Vlong (Int64.repr (encode_Z (Z.of_nat n))));
     gvars gv)
     SEP (full_gc g'' t_info' roots' outlier ti sh gv;
          frame_rep_ v___FRAME__ v___ROOT__ (spatial_gcgraph.ti_fp t_info') 1;
          library.mem_mgr gv))%assert.
 + apply prop_right; simpl. destruct (peq startb startb); try contradiction. auto.
 +
  forward.
  forward.
  unfold frame_rep_. Intros.
  change_compspecs CompSpecs.
  forward.
  forward.
  deadvars!.
  change (upd_Znth 0 _ _) with ([rep_type_val g' v0]).
  change (Tpointer tvoid _) with int_or_ptr_type.
  assert_PROP (force_val (sem_add_ptr_int int_or_ptr_type Signed v___ROOT__ (Vint (Int.repr 1))) =
      offset_val (sizeof int_or_ptr_type * 1) v___ROOT__)  as H99; [ entailer! | rewrite H99; clear H99].
  generalize (frame_rep_fold v___FRAME__ v___ROOT__ (spatial_gcgraph.ti_fp t_info') 1 [rep_type_val g' v0]);
   change_compspecs CompSpecs; intro Hx; sep_apply Hx; clear Hx.
  unfold spatial_gcgraph.ti_fp.
  replace (spatial_gcgraph.frames_rep sh) with (spatial_gcgraph.frames_rep Tsh)
     by admit.  (* This needs fixing *)
  sep_apply (frames_rep_cons v___FRAME__ v___ROOT__ [rep_type_val g' v0] (ti_frames t_info')).
  compute; clear; congruence.
  set (frames'' := _ :: ti_frames t_info').
  pose (t_info'' := {| ti_heap_p := ti_heap_p t_info'; ti_heap := ti_heap t_info';
                      arg_size := arg_size t_info'; ti_frames := frames'';
                      ti_nalloc := Ptrofs.repr 2 |}).
  change frames'' with (ti_frames t_info'').
  rewrite Int.signed_repr by rep_lia.
  change (ti_args t_info') with (ti_args t_info'').
  change (ti_heap_p t_info') with (ti_heap_p t_info'').
  clear H8.
  forward_call (Ers, sh, gv, ti, g', t_info'', root_t_of_rep_type v0 :: roots', outlier).
  *
   unfold spatial_gcgraph.before_gc_thread_info_rep.
   change_compspecs CompSpecs.
   replace (spatial_gcgraph.frames_rep sh) with (spatial_gcgraph.frames_rep Tsh)
      by admit.  (* This needs fixing *)
   rewrite <- STARTeq.
   change (ti_heap t_info') with (ti_heap t_info'').
   cancel.
  * simpl.
    split3.
    red. red in GCP.
    split3; [ tauto | | split; [ | tauto] ].
    --
     subst frames''; clear t_info''.
     unfold frames2rootpairs. simpl concat.
     unfold rootpairs_compatible. simpl.
     f_equal.  destruct v0; auto.
     change (rootpairs_compatible g' (frames2rootpairs (ti_frames t_info')) roots').
     tauto.
    -- decompose [and] GCP; clear GCP. destruct H15.
       split. 
       ++ clear t_info'' frames'' H7 STARTptr STARTeq startb starti H3 HRE' HRE.
          unfold root_t_of_rep_type.
          destruct v0; auto.
          red in H15|-*. simpl.
          change (?A :: ?B) with ([A]++B).
          apply incl_app; auto.
          unfold is_in_graph in H2.
          destruct m; simpl in H2; try contradiction.
          destruct H2 as [? [? ? ]  ]; contradiction.
       ++ destruct v0; try apply H18. constructor; auto.
          clear - H2. unfold is_in_graph in H2.
          apply has_v in H2; auto.
    -- red in GCP; decompose [and] GCP; split; auto.
    -- apply GCP.
  * (* after the call to garbage_collect() *)
   Intros vret. destruct vret as [ [g3 t_info3] roots3].
   simpl snd in *. simpl fst in *.
   assert (H50: ti_heap_p t_info3 = ti_heap_p t_info)
    by admit. (* should be a postcondition of garbage_collect *)
   assert (FSE: frame_shells_eq (ti_frames t_info'') (ti_frames t_info3)) 
       by admit. (* should be a postcondition of garbage_collect *)
   assert (ROOM: Ptrofs.unsigned (ti_nalloc t_info'') <= 
                 total_space (heap_head (ti_heap t_info3))
                    - used_space (heap_head (ti_heap t_info3)))
    by admit. (* should be a postcondition of garbage_collect *)
   forward.
   unfold spatial_gcgraph.before_gc_thread_info_rep.
   replace (spatial_gcgraph.frames_rep sh) with (spatial_gcgraph.frames_rep Tsh)
   by admit.  (* This needs fixing *)
   simpl in FSE. unfold frames'' in FSE.
   remember (ti_frames t_info3) as frames3.
   inversion FSE; clear FSE. subst r1 fr1.
   destruct fr2 as [a3 r3 s3]; simpl in H14, H15, H16.
   subst a3 r3.
   destruct s3. exfalso; clear - H16; list_solve.
   destruct s3. 2: exfalso; clear - H16; list_solve.
   subst frames3.
   sep_apply (frames_rep_pop v___FRAME__ v___ROOT__ [v1] r2).
   compute; clear; congruence.
   unfold frame_rep at 1.
   Intros. change (Zlength [_]) with 1.
   assert (roots_graph_compatible (root_t_of_rep_type v0 :: roots') g'). {
       red in GCP. destruct GCP as [_ [_ [_ [_ [_ [_ [_ [ [ _ ? ] _  ] ] ] ] ] ] ] ].
       destruct v0; try apply H12.
       constructor; auto.
       red in H2.
       eapply has_v; eauto.
    }
   assert (ISO: gc_graph_iso g' (root_t_of_rep_type v0 :: roots') g3 roots3). {
     red in H8; decompose [and] H8.
     apply garbage_collect_isomorphism; auto; try apply GCP.
    }
   assert (exists v0', exists roots3',
        v1 = rep_type_val g3 v0' /\ is_in_graph g3 m v0' /\ roots3 = root_t_of_rep_type v0' :: roots3'). {
       rewrite <- H17 in H8. simpl frames2rootpairs in H8.
    pose proof @gc_preserved _ InGraph_nat _ _ _ _ ISO ltac:(clear - H10; red in H10; tauto)
    m 0 ltac:(clear; Zlength_solve).
    rewrite Znth_0_cons,rep_type_of_root_t_of_rep_type in H13.
    specialize (H13 H2).
    exists (rep_type_of_root_t (Znth 0 roots3)), (sublist 1 (Zlength roots3) roots3).
    rewrite root_t_of_rep_type_of_root_t.
    split3; auto.
    destruct H8 as [_ [? _] ].
    red in H8. simpl in H8.
    assert (v1 = root2val g3 (Znth 0 roots3)) by list_solve.
    rewrite H14.
    destruct (Znth 0 roots3); try destruct s ; auto.
    apply graph_iso_Zlength in ISO.    
    clear - ISO. rewrite Zlength_cons in ISO. 
    destruct roots3; autorewrite with sublist in ISO. rep_lia.
    autorewrite with sublist.
    f_equal. rewrite sublist_S_cons by lia.
    rewrite Z.sub_diag. unfold Z.succ.
    rewrite sublist_same by lia. auto.
    }
   destruct H13 as [v0' [roots3' [ ? [? ?] ] ] ].
   subst v1 roots3.
   change_compspecs CompSpecs.
   forward. entailer!!. rewrite Znth_0_cons. { 
        destruct v0'; simpl; auto. destruct g0; simpl; auto.
        unfold vertex_address.
        apply has_v in H14. destruct H14 as [? _].
        pose proof (graph_has_gen_start_isptr _ _ H13).
        destruct (gen_start g3 (vgeneration _)); auto.
    }
   forward.  {
      sep_apply spatial_gcgraph.frames_rep_ptr_or_null;  entailer!!.
    }
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
      unfold gc_condition_prop.
      change (ti_heap t_info4) with (ti_heap t_info3).
      repeat simple apply conj; try apply GCP; try apply H10; auto;
        try apply H8.
        - destruct H8 as [? [? [ ?  ? ] ] ].
           clear - H15.
           destruct H15; split.
           +
            red in H|-*.
            destruct (root_t_of_rep_type v0') as [ [ | ] | ]; simpl in H; auto.
            eapply incl_app_inv_r with (l1:=[g]); auto.
           + destruct (root_t_of_rep_type v0') as [ [ | ] | ]; simpl in H0; auto.
              red in H0|-*. simpl in H0. inversion H0; subst; auto. 
        - destruct H8 as [_ [? _] ].
            rewrite <- H17 in H8.
            unfold frames2rootpairs in H8. simpl in H8.
            red in H8. simpl in H8. inversion H8; subst; auto.
        - eapply gc_sound; eauto. apply GCP.
        - apply graph_unmarked_copy_compatible; apply H10.
    }
    repeat simple apply conj; auto.
      ++ simpl ti_heap.
         clear - ROOM. subst t_info''. simpl in ROOM. rewrite Ptrofs.unsigned_repr in ROOM by rep_lia. lia.
      ++ apply gc_graph_iso_trans with g' roots'; auto.
         eapply gc_graph_iso_uncons; eassumption.
      ++ simpl. eapply frame_shells_eq_trans; eassumption.
    -- unfold before_gc_thread_info_rep, spatial_gcgraph.before_gc_thread_info_rep, frame_rep_.
      change_compspecs CompSpecs.
      replace (spatial_gcgraph.frames_rep sh) with (spatial_gcgraph.frames_rep Tsh)
      by admit.  (* This needs fixing *)
      unfold spatial_gcgraph.ti_fp. 
      unfold t_info4; simpl.
      replace (Vlong (Ptrofs.to_int64 (ti_nalloc t_info3))) with (Vptrofs (ti_nalloc t_info3))
        by (rewrite Vptrofs_unfold_true by reflexivity; reflexivity).
      cancel.
      unfold frame_rep_surplus. change (1 - Zlength _) with 0.
      change_compspecs CompSpecs.
      Intros.
      generalize H13; 
      rewrite (@field_compatible_change_composite env_graph_gc.CompSpecs CompSpecs CCE) by auto with typeclass_instances; intro.
      sep_apply data_at__data_at.
      sep_apply data_at_zero_array_eq.
      autorewrite with sublist.
      unfold field_address0. rewrite if_true; simpl. auto with field_compatible.
      auto with field_compatible.
      do 2 unfold_data_at (data_at _ (Tstruct gc_stack._stack_frame _) _ _).
      cancel.
  + forward.
    Exists g' v0 roots' t_info'.
    unfold full_gc, before_gc_thread_info_rep, spatial_gcgraph.before_gc_thread_info_rep.
    rewrite <- STARTeq.
    change_compspecs CompSpecs.
    entailer!!.
    set (hh := heap_head (ti_heap t_info')) in *.
    assert (ORDER := space_order hh).
    assert (UB := space_upper_bound hh).
    set (tot := total_space hh) in *. clearbody tot.
    set (use := used_space hh) in *. clearbody use.
    clear - H8 ORDER UB.
    simpl in H8.
    unfold sem_sub_pp in H8. simpl in *. rewrite if_true in H8 by auto. simpl in H8.
     rewrite Int.signed_repr in H8 by rep_lia.
    destruct (Int64.lt _ _) eqn:?H in H8; try discriminate.
    unfold Int64.lt in H.
    if_tac in H; try discriminate. clear H H8.
    rewrite !(Ptrofs.add_commut starti), Ptrofs.sub_shifted, ptrofs_sub_repr in H0.
    unfold MAX_SPACE_SIZE in *. simpl in UB.
    rewrite <- Z.mul_sub_distr_l in H0.
    change WORD_SIZE with 8 in *.
    rewrite ptrofs_divs_repr in H0 by rep_lia.
    rewrite ptrofs_to_int64_repr in H0 by reflexivity.
    rewrite Z.mul_comm, Z.quot_mul in H0 by lia.
    rewrite !Int64.signed_repr in H0 by rep_lia. auto.
  + Intros g4 v0' roots4 t_info4.
  pose (m' := existT (fun _ => unit) m tt).
  forward_call (gv, g4, [v0'], m', roots4, sh, ti, outlier, t_info4).
   * split.
      split; auto. reflexivity. unfold headroom. lia. 
   * Intros vret.
     destruct vret as [ [ v2 g5] t_info5].
     simpl snd in *. simpl fst in *.
     assert_PROP (gc_condition_prop g5 t_info5 roots4 outlier) as GCP'
        by (unfold full_gc; entailer!!). 
     assert (MISSING: ti_heap_p t_info5 = ti_heap_p t_info /\ 
             ti_frames t_info5 = ti_frames t_info4) by admit. (* missing from postcondition? *)
     destruct MISSING as [ M1 M2 ].
     simpl in H13.
     forward.
     Exists (v2, S m,g5,t_info5,roots4). simpl fst. simpl snd.
     unfold spatial_gcgraph.ti_fp.
     replace (Z.of_nat (n - S m)) with (Z.of_nat (n-m)-1) by lia.
     rewrite M1, M2.
     entailer!!.
     eapply gc_graph_iso_trans; eassumption.
 - (* after the loop *)
   forward.
   assert (m=n). {
    clear - H3 H HRE. unfold encode_Z in H. unfold min_signed, max_signed in H. simpl in H.
    apply repr_inj_unsigned64 in HRE; try rep_lia.     
   }
   subst m.
   Exists v0 g' t_info' roots'.
   unfold frame_rep_.
   entailer!!.
all:fail.
Admitted. 
