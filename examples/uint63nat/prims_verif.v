Require Import VeriFFI.examples.uint63nat.prims.
Require Import ZArith.
Require Import Psatz.
Require Import CertiGraph.CertiGC.spatial_gcgraph.

Require Import VeriFFI.examples.uint63nat.specs.

Ltac limited_change_compspecs' cs cs' :=
  lazymatch goal with
  | |- context [@data_at cs' ?sh ?t ?v1] => erewrite (@data_at_change_composite cs' cs _ sh t); [| apply JMeq_refl | prove_cs_preserve_type]
  | |- context [@field_at cs' ?sh ?t ?gfs ?v1] => erewrite (@field_at_change_composite cs' cs _ sh t gfs); [| apply JMeq_refl | prove_cs_preserve_type]
  | |- context [@data_at_ cs' ?sh ?t] => erewrite (@data_at__change_composite cs' cs _ sh t); [| prove_cs_preserve_type]
  | |- context [@field_at_ cs' ?sh ?t ?gfs] => erewrite (@field_at__change_composite cs' cs _ sh t gfs); [| prove_cs_preserve_type]
  end.

Ltac limited_change_compspecs cs :=
 match goal with |- context [?cs'] =>
   match type of cs' with compspecs =>
     try (constr_eq cs cs'; fail 1);
     limited_change_compspecs' cs cs';
     repeat limited_change_compspecs' cs cs'
   end
end.

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

Lemma is_pointer_or_integer_rep_type_val:
  forall {A} `{InG: InGraph A} g (n: A) p, 
   is_in_graph g n p ->
   graph_rep g |-- !! is_pointer_or_integer (rep_type_val g p).
Proof.
intros.
destruct p; simpl; auto.
destruct g0; simpl; auto.
apply has_v in H.
sep_apply (graph_rep_valid_int_or_ptr g v).
entailer!!.
hnf in H0|-*.
destruct (vertex_address g v); auto.
destruct Archi.ptr64; auto.
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

#[export] Instance Inhabitant_rep_type: Inhabitant rep_type.
constructor. apply 0.
Defined.


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
 forall sh vf vr vl frames
  (SIZE: WORD_SIZE * Zlength vl <= Ptrofs.max_signed),
 (frame_rep sh vf vr (spatial_gcgraph.frames_p frames) vl *
  spatial_gcgraph.frames_rep sh frames)%logic
 = spatial_gcgraph.frames_rep sh 
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
unfold spatial_gcgraph.frames_shell_rep; fold (spatial_gcgraph.frames_shell_rep sh frames).
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
 forall sh vf vr vl frames
  (SIZE: WORD_SIZE * Zlength vl <= Ptrofs.max_signed),
frame_rep sh vf vr (spatial_gcgraph.frames_p frames) vl *
spatial_gcgraph.frames_rep sh frames
|-- spatial_gcgraph.frames_rep sh 
     ({|fr_adr:=vf; fr_root:=vr; fr_roots := vl|}::frames).
Proof.
intros.
rewrite frames_rep_cons by auto. auto.
Qed.


Lemma frames_rep_pop:
 forall sh vf vr vl frames
  (SIZE: WORD_SIZE * Zlength vl <= Ptrofs.max_signed),
 spatial_gcgraph.frames_rep sh 
     ({|fr_adr:=vf; fr_root:=vr; fr_roots := vl|}::frames)
|-- frame_rep sh vf vr (spatial_gcgraph.frames_p frames) vl *
    spatial_gcgraph.frames_rep sh frames.
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


Lemma headroom_check: 
 forall (n: Z) (hh: space) (startb: block) (starti: ptrofs),
  Int.min_signed <= n <= Int.max_signed ->
  typed_false tint
       match
         sem_unary_operation Onotbool tint
           (force_val
              (both_long
                 (fun n1 n2 : int64 => Some (bool2val (negb (Int64.lt n2 n1))))
                 (sem_cast_i2l Signed) sem_cast_pointer 
                 (Vint (Int.repr n))
                 (force_val
                    (sem_sub_pp
                       int_or_ptr_type
                       (Vptr startb
                          (Ptrofs.add starti
                             (Ptrofs.repr
                                (WORD_SIZE
                                   * total_space hh))))
                       (Vptr startb
                          (Ptrofs.add starti
                             (Ptrofs.repr
                                (WORD_SIZE
                                   * used_space hh))))))))
       with
       | Some v' => v'
       | None => Vundef
       end ->
  total_space hh - used_space hh >= n.
Proof.
intros * H7 H8.
    assert (ORDER := space_order hh).
    assert (UB := space_upper_bound hh).
    set (tot := total_space hh) in *. clearbody tot.
    set (use := used_space hh) in *. clearbody use.
    simpl in H8.
    unfold sem_sub_pp in H8. simpl in *. rewrite if_true in H8 by auto. simpl in H8.
     rewrite Int.signed_repr in H8 by auto.
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
Qed.



Ltac sep_apply_compspecs cs H :=
  generalize H; limited_change_compspecs cs; 
  let Hx := fresh "Hx" in  intro Hx; sep_apply Hx; clear Hx.

Lemma space_start_isptr':
  forall [g tinfo roots outlier],
  gc_condition_prop g tinfo roots outlier ->
  isptr (space_start (heap_head (ti_heap tinfo))).
Proof.
 intros * GCP.
    red in GCP; decompose [and] GCP.
    destruct (heap_head_cons (ti_heap tinfo)) as [s [l [C1 C2]  ] ].
    rewrite C2.
    replace s with (Znth 0 (spaces (ti_heap tinfo))) by (rewrite C1; reflexivity).
    apply space_start_isptr with g; auto; try apply H1.
    rewrite C1; clear; list_solve.
    apply graph_has_gen_O.
Qed.

Definition GC_SAVE1 n := 
                (Ssequence
                  (Ssequence
                    (Sset __LIMIT
                      (Efield
                        (Ederef
                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                          (Tstruct _thread_info noattr)) _limit
                        (tptr (talignas 3%N (tptr tvoid)))))
                    (Sset __ALLOC
                      (Efield
                        (Ederef
                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                          (Tstruct _thread_info noattr)) _alloc
                        (tptr (talignas 3%N (tptr tvoid))))))
                  (Sifthenelse (Eunop Onotbool
                                 (Ebinop Ole (Econst_int (Int.repr n) tint)
                                   (Ebinop Osub
                                     (Etempvar __LIMIT (tptr (talignas 3%N (tptr tvoid))))
                                     (Etempvar __ALLOC (tptr (talignas 3%N (tptr tvoid))))
                                     tlong) tint) tint)
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                            (Tstruct _thread_info noattr)) _nalloc tulong)
                        (Econst_int (Int.repr n) tint))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                          (Tstruct _thread_info noattr)) _fp
                                        (tptr (Tstruct _stack_frame noattr)))
                                      (Eaddrof
                                        (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                        (tptr (Tstruct _stack_frame noattr))))
                                    (Sassign
                                      (Efield
                                        (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                        _next
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (Ebinop Oadd
                                        (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr (talignas 3%N (tptr tvoid))))))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                        (Econst_int (Int.repr 0) tint)
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (talignas 3%N (tptr tvoid)))
                                    (Etempvar _save0 (talignas 3%N (tptr tvoid)))))
                                (Scall None
                                  (Evar _garbage_collect (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _thread_info noattr))
                                                             Tnil) tvoid
                                                           cc_default))
                                  ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                                   nil)))
                              (Sset ___RTEMP__
                                (Ecast
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    (tptr tvoid))
                                  (talignas 3%N (tptr tvoid)))))
                            (Sset _save0
                              (Ederef
                                (Ebinop Oadd
                                  (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr (talignas 3%N (tptr tvoid))))
                                (talignas 3%N (tptr tvoid)))))
                          (Sset ___PREV__
                            (Efield
                              (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                              _prev (tptr (Tstruct _stack_frame noattr)))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                              (Tstruct _thread_info noattr)) _fp
                            (tptr (Tstruct _stack_frame noattr)))
                          (Etempvar ___PREV__ (tptr (Tstruct _stack_frame noattr))))))
                    Sskip)).


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

Local Open Scope logic.
Lemma semax_frame_PQR':
  forall Q2 R2 Espec {cs: compspecs} Delta R1 P Q S c,
     closed_wrt_modvars c (LOCALx Q2 (SEPx R2)) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R1))) c
                     (normal_ret_assert S) ->
     @semax cs Espec Delta (PROPx P (LOCALx (Q++Q2) (SEPx (R1++R2)))) c
                     (normal_ret_assert (sepcon S (PROPx nil (LOCALx Q2 (SEPx R2))))).
Proof.
intros.
replace (PROPx P (LOCALx (Q++Q2) (SEPx (R1 ++ R2))))
   with (PROPx P (LOCALx Q (SEPx (R1))) * (LOCALx Q2 (SEPx R2))).
eapply semax_pre_post; try (apply semax_frame; try eassumption).
apply andp_left2; auto.
apply andp_left2. intro rho; simpl; normalize.
 unfold PROPx, SEPx, LOCALx, local, lift1.
normalize.
simpl; normalize.
simpl; normalize.
simpl; normalize.
clear.
extensionality rho.
simpl.
unfold PROPx, LOCALx, local, lift1, SEPx.
rewrite fold_right_sepcon_app.
simpl. normalize.
f_equal.
rewrite map_app. rewrite fold_right_and_app.
apply pred_ext; normalize.
Qed.

Lemma semax_frame_PQR'':
  forall Q1 Q2 R1 R2 S1 Espec {cs: compspecs} Delta P Q R S c,
     closed_wrt_modvars c (LOCALx Q2 (SEPx R2)) ->
     PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx (Q1++Q2) (SEPx (R1++R2))) ->
     S1 * (PROPx nil (LOCALx Q2 (SEPx R2))) |-- S ->
     @semax cs Espec Delta (PROPx P (LOCALx Q1 (SEPx R1))) c
                     (normal_ret_assert S1) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c
                     (normal_ret_assert S).
Proof.
intros.
eapply semax_pre_post'; [ | | apply semax_frame_PQR' with (P:=P)].
apply andp_left2; eassumption.
apply andp_left2; eassumption.
auto.
auto.
Qed.

Ltac get_rep_temps ti Q :=
 lazymatch Q with
 | nil => constr:(Q)
 | temp ti ?v :: ?r => let r' := get_rep_temps ti r in constr:(temp ti v :: r')
 | temp ?i (rep_type_val ?g ?v) :: ?r => 
    let r' := get_rep_temps ti r in constr:(temp i (rep_type_val g v) :: r')
 | temp ?i ?v :: ?r => get_rep_temps ti r
 | ?t :: ?r => let r' := get_rep_temps ti r in constr:(t::r')
 end.

Ltac get_nonrep_temps ti Q :=
 lazymatch Q with
 | nil => constr:(Q)
 | temp ti _ :: ?r => get_nonrep_temps ti r 
 | temp ?i (rep_type_val ?g ?v) :: ?r => get_nonrep_temps ti r
 | temp ?i ?x :: ?r => let r' := get_nonrep_temps ti r in constr:(temp i x ::r')
 | _ :: ?r => get_nonrep_temps ti r
 end.

Ltac get_gc_mpreds R :=
 lazymatch R with
 | nil => constr:(R)
 | ?r1 :: ?r => 
   lazymatch r1 with
   | full_gc _ _ _ _ _ _ _  => let r' := get_gc_mpreds r in constr:(r1::r')
   | frame_rep_ _ _ _ _ _ => let r' := get_gc_mpreds r in constr:(r1::r')
   | library.mem_mgr _ => let r' := get_gc_mpreds r in constr:(r1::r')
   | is_in_graph _ _ => let r' := get_gc_mpreds r in constr:(r1::r')
   | _ => get_gc_mpreds r
   end
 end.

Ltac get_nongc_mpreds R :=
 lazymatch R with
 | nil => constr:(R)
 | ?r1 :: ?r => 
   lazymatch r1 with
   | full_gc _ _ _ _ _ _ _  => get_nongc_mpreds r
   | frame_rep_ _ _ _ _ _ => get_nongc_mpreds r
   | library.mem_mgr _ => get_nongc_mpreds r
   | is_in_graph _ _ => get_nongc_mpreds r
   | _ => let r' := get_nongc_mpreds r in constr:(r1::r')
   end
 end.

Lemma perhaps_gc_1_live_root_aux:
 forall P Q R Q2 R2,
  (EX (g': graph) (v0': rep_type) (roots': roots_t) (t_info': GCGraph.thread_info),
   PROPx (P g' v0' roots' t_info')
    (LOCALx (Q g' v0' roots' t_info')
     (SEPx (R g' v0' roots' t_info')))) * (PROPx nil (LOCALx Q2 (SEPx R2))) |--
  (EX (g': graph) (v0': rep_type) (roots': roots_t) (t_info': GCGraph.thread_info),
     PROPx (P g' v0' roots' t_info')
    (LOCALx (Q g' v0' roots' t_info' ++ Q2)
     (SEPx (R g' v0' roots' t_info' ++ R2)))).
Proof.
intros.
Intros a b c d; Exists a b c d.
rewrite PROP_combine.
rewrite app_nil_r.
auto.
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
sep_apply before_gc_thread_info_rep_fold.
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
