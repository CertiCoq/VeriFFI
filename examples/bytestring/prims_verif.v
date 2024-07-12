Require Import VeriFFI.examples.bytestring.prims.
Require Import ZArith.
Require Import Psatz.
Require Import CertiGraph.CertiGC.spatial_gcgraph.

Require Import VeriFFI.examples.bytestring.specs.

Lemma graph_rep_full_gc: 
  forall g t_info roots outlier ti sh gv,
    full_gc g t_info roots outlier ti sh gv = 
    (graph_rep g * (graph_rep g -* full_gc g t_info roots outlier ti sh gv))%logic.
Proof.
intros.
apply pred_ext.
unfold full_gc.
Intros.
normalize.
cancel.
apply -> wand_sepcon_adjoint.
cancel.
sep_apply modus_ponens_wand.
cancel.
Qed.


Definition MAX_SPACE_SIZE := two_p 57.  (* At the moment, this is smaller than
    the MAX_SPACE_SIZE defined in the runtime system, which is 2^58.  2^57 is the largest we can
    tolerate for the correctness proof of the bytestring "pack" operation, because
    an OCaml object header has only 54 bits to record the length (in words) of the
    record.  That means, 2^54 words = 2^57 bytes (with 8 bytes per word).  The
    longest _unpacked_ string one can tolerate, essentially a list of characters, would
    be (with 2 words = 16 bytes per character) 2^57 * 2*8 = 2^61 bytes.

    Thus, the maximum heap we can tolerate (if we want to guarantee packing bytestrings)
    is 2^58 words.  

    Since the maximum heap size is twice the MAX_SPACE_SIZE, as it is the sum of
    a powers-of-two geometric series, that means the max space size we can tolerate
    is 2^57 words.

    If we modify the runtime system to lower MAX_SPACE_SIZE to 2^57, then we can't
    run CertiCoq to exploit memories larger than 2 exabytes.  This limitation seems
    tolerable.  *)

Definition MAX_WORDS_IN_GRAPH := MAX_SPACE_SIZE * 2.  (* because each space is twice as big as previous,
       sum of geometric series.
     WARNING:  If we permit "outlier" data structures to be part of the graph, then
     it is invalid to assume that the graph size is bounded.  If outliers are only
     used for abstract types, not traversable as constructors, then it's OK.
 *)

Definition MAX_LEN := MAX_WORDS_IN_GRAPH/3.
    (* because each char in string is represented by a "String" constructor of 3 words
       (including header).  You might (erroneously) think that each one also needs
       an "Ascii" constructor of 9 words (including header), but in fact they can all
       share the same character *)


Lemma representable_string_max_length:
 (* PROVABLE! but not easy.  Rely on the fact that every node in the graph
   must exist in some generation (if it's really true that the graph cannot extend into
   outliers), and the total of all generation sizes is bounded. *)
  forall (s: string) (g: graph) outlier (p: rep_type),
   is_in_graph g outlier s p ->
   graph_rep g |-- !! (Z.of_nat (String.length s) < MAX_LEN).
Admitted.

(* copied from examples/uint63nat/Verif_prog_general.v *)
Lemma spaces_g0 g t_info roots outlier :
    gc_condition_prop g t_info roots outlier
    -> isptr (space_start (heap_head (ti_heap t_info)))
      /\  writable_share (space_sh (heap_head (ti_heap t_info)))
      /\ generation_space_compatible g (0%nat, nth_gen g 0, heap_head (ti_heap t_info)).
Proof.
   destruct (heap_head_cons (ti_heap t_info)) as (g0&space_rest&SPACE_NONEMPTY&g0_eq). rewrite !g0_eq in *.
  intros gc_cond.
  unfold nth_gen.
    destruct (graph_model.glabel g) eqn: glabel_g.
    simpl GCGraph.g_gen.
    destruct g_gen; try congruence. 
    simpl nth.
    unfold gc_condition_prop in *.
    destruct gc_cond as (gc1&gc2&gc3&gc4&gc5).
    red in gc2.
    destruct gc2 as (?&?&?&?).
    red in H; destruct H as  (gc61&gc62&gc63).
    simpl in *. rewrite !glabel_g in gc61. simpl in *.
    rewrite !SPACE_NONEMPTY in *.
    apply Forall_inv in gc61. destruct gc61 as (?&?&?).
    destruct g1; simpl in *.
    split3; eauto; congruence.
Qed.

Local Hint Resolve AP_edge_compat : core.
Local Hint Resolve AP_incl_outlier : core.
Local Hint Resolve graph_has_gen_O: core.
Local Hint Resolve AP_compat : core.

Lemma heap_congr: forall h1 h2 : heap, spaces h1 = spaces h2 -> h1=h2.
Proof.
intros.
destruct h1, h2. simpl in *. subst spaces0. f_equal. proof_irr; auto.
Qed.

Lemma add_node_space_alloc_in_nursery:
 forall (h: heap) (n: Z) ENUF ENUF', 
upd_Znth 0 (spaces h) (add_node_space 0 (nth 0 (spaces h) null_space) n ENUF) = 
allocate_in_nursery n (heap_head h) ENUF' :: tl (spaces h).
Proof.
intros.
destruct h; simpl.
destruct spaces.
inversion spaces_size.
rewrite upd_Znth0.
simpl.
f_equal. 
unfold add_node_space, allocate_in_nursery.
f_equal.
apply proof_irr.
Qed.

Lemma raw_vertex_block_congr:
  forall a b : raw_vertex_block,
  raw_mark a = raw_mark b ->
  copied_vertex a = copied_vertex b ->
  raw_fields a = raw_fields b ->
  raw_color a = raw_color b ->
  raw_tag a = raw_tag b ->
  a=b.
Proof.
intros.
destruct a,b; simpl in *; subst.
f_equal; apply proof_irr.
Qed.

Lemma body_bump_allocptr:
  semax_body Vprog Gprog f_bump_allocptr bump_allocptr_spec.
Proof.
start_function.
unfold full_gc, before_gc_thread_info_rep.
Intros.
limited_change_compspecs CompSpecs.
destruct (spaces_g0 _ _ _ _ H) as [? [? ?]].
forward.
forward.
forward.
set (tinfo := AP_ti pp) in *.
unfold full_gc, before_gc_thread_info_rep.
limited_change_compspecs CompSpecs.
simpl ti_args. simpl ti_heap_p. simpl ti_frames.
set (hh := heap_head (ti_heap tinfo)).
set (hh' := heap_head _).
simpl.
rewrite !sepcon_assoc.
change (total_space (heap_head (ti_heap tinfo))) with (total_space hh).
change (space_start (heap_head (ti_heap tinfo))) with (space_start hh).
change (ti_fp (bump_alloc _)) with (ti_fp tinfo).
change (used_space (heap_head (ti_heap tinfo))) with (used_space hh).
set (FRAMES := frames_rep _ _). clearbody FRAMES.
set (OUTLIER := outlier_rep (AP_outlier pp)); clearbody OUTLIER.
change 8 with WORD_SIZE.
rewrite <- Z.mul_add_distr_l.
unfold heap_rest_rep.
subst hh hh'.
clear H6 H5 H3.
unfold alloc_at.
assert (HEADROOM := AP_enough pp).
unfold headroom in HEADROOM.
simpl spaces.
destruct (heap_head_cons (ti_heap tinfo)) as [nursery [rest [? ?]]].
fold tinfo.
change (iter_sepcon.iter_sepcon (?A :: ?B) ?F) with
  (sepcon (F A) (iter_sepcon.iter_sepcon B F)).
unfold allocate_in_nursery.
set (EN := AP_enough pp). clearbody EN.
unfold space_rest_rep at 2.
simpl ti_heap.
simpl space_start.
rewrite add_node_heap_start0.
simpl ti_heap.
rewrite add_node_heap_used_space0.
rewrite add_node_heap_total0.
fold tinfo.
rewrite H5.
set (DA := data_at _ env_graph_gc.thread_info_type _ _). clearbody DA.
change (iter_sepcon.iter_sepcon (?A :: ?B) ?F) with
  (sepcon (F A) (iter_sepcon.iter_sepcon B F)).
rewrite H3 at 2.
change (iter_sepcon.iter_sepcon (?A :: ?B) ?F) with
  (sepcon (F A) (iter_sepcon.iter_sepcon B F)).
unfold space_rest_rep at 1.
rewrite if_false
  by (intro Hx; rewrite H5,Hx in H0; contradiction H0).
set (K := _ - _).
set (n := AP_n pp).
saturate_local. rename H6 into FC'.
fold tinfo in HEADROOM; rewrite H5 in HEADROOM.
rewrite (split2_data_at__Tarray_app n K) by lia.
rewrite <- !sepcon_assoc.
limited_change_compspecs CompSpecs.
assert (Hsh: nth_sh (AP_g pp) 0 = space_sh nursery). {
  destruct H as [_ [? _  ]].
  destruct H as [? _ ].
  red in H. 
  rewrite H3 in H.
  destruct H2 as [_ [? _  ]].
  unfold nth_sh. rewrite H2. rewrite H5. auto.
 }
rewrite Hsh.
cancel.
apply allp_right; intro ap.
apply -> wand_sepcon_adjoint.
rewrite andp_comm, prop_true_andp.
-
subst nursery.
set (nursery := heap_head (ti_heap tinfo)) in *.
set (TT1 := ti_token_rep _ _).
set (TT2 := ti_token_rep _ _).
assert (TT2 = TT1) as ->. {
 subst TT2; subst TT1.
 unfold ti_token_rep; simpl.
 f_equal.
 rewrite add_node_space_alloc_in_nursery with (ENUF' := HEADROOM).
 rewrite H3.
 simpl.
 f_equal.
}
clearbody TT1.
cancel.
rewrite add_node_space_alloc_in_nursery with (ENUF' := EN).
simpl iter_sepcon.iter_sepcon.
rewrite if_false
 by (fold tinfo; fold nursery; intro Hx; rewrite Hx in H0; contradiction).
simpl tl.
limited_change_compspecs CompSpecs.
cancel.
set (HS := heap_struct_rep _ _ _). clearbody HS.
fold tinfo.
fold nursery.
rewrite H3. simpl tl.
fold space_rest_rep.
fold n.
rewrite Z.sub_add_distr.
fold K.
unfold field_address0.
rewrite if_true by auto with field_compatible.
simpl. change 8%Z with WORD_SIZE.
rewrite offset_offset_val.
rewrite <- Z.mul_add_distr_l.
cancel.
unfold AP_newg.
destruct H.
destruct H as [? [? [? ? ]]].
destruct H5.
rewrite <- Hsh.
rewrite add_node_spatial; simpl; auto.
* red; intros.
destruct H9 as [H10a [H10b H10c]].
apply H10c in H10.
specialize (H10 H11).
destruct H10.
auto.
*
apply AP_compat.
-

assert (ENUF: 0 <= n <=
  total_space (nth 0 (spaces (ti_heap (AP_ti pp))) null_space)
    - used_space (nth 0 (spaces (ti_heap (AP_ti pp))) null_space))
  by (fold tinfo; rewrite H3; simpl; rewrite <- H5;  apply (AP_enough pp)).
unfold AP_newg, bump_alloc.
red in H; decompose [and] H; clear H.
split3; [ | | split3]; simpl; auto.
destruct H6 as [? [ ? [? ?]]].
split; [ | split3]; auto.
+
apply add_node_graph_unmarked; auto.
+
apply add_node_no_backward_edge; auto; try apply AP_edge_compat; apply AP_compat.
+
apply add_node_no_dangling_dst; auto; try apply AP_edge_compat; apply AP_compat.
+
apply add_node_ti_size_spec; auto.
unfold tinfo in *; clear - H3; rewrite H3; list_solve.
+
destruct H8 as [? [? [? ? ]]].
split; [ | split3].
*
apply add_node_graph_heap_compatible; auto.
rewrite Z.add_comm. symmetry. apply AP_len.
apply H6.
*
fold tinfo.
red in H8|-*. rewrite <- H8.
destruct H10 as [ _  ? ].
red in H10.
clear - H10.
induction roots.
reflexivity.
simpl.
specialize (IHroots (Forall_filter_sum_right_cons_e _ _ _ H10)).
f_equal; auto.
destruct a; simpl; auto.
inv H10.
apply add_node_vertex_address_old; auto.
*
destruct H10; split; auto.
red in H13|-*.
eapply Forall_impl; try apply H13.
intros.
apply add_node_graph_has_v_impl; auto.
*
apply add_node_outlier_compatible; auto.
+
apply add_node_safe_to_copy0; auto.
+
apply sound_gc_graph; auto; try apply AP_edge_compat; apply AP_compat.
+
replace (AP_rvb pp ap)
 with (newRaw (new_copied_v (AP_g pp) 0) (raw_tag (AP_rvb pp ap)) (raw_fields (AP_rvb pp ap)) 
  (raw_tag_range _) (raw_fields_range _) (tag_no_scan _))
 by (apply raw_vertex_block_congr; simpl; auto).
apply add_node_copy_compatible; auto.
Qed.

Lemma Zlength_bytes_of_string:
  forall s, Zlength (bytes_of_string s) = Z.of_nat (String.length s).
Proof.
intros.
unfold bytes_of_string.
unfold list_byte_of_string.
rewrite !Zlength_map.
rewrite Zlength_correct.
f_equal.
induction s; simpl; auto.
Qed.

Lemma substring_sublist:
  forall i j s, 0 <= i -> 0 <= j <= Zlength (bytes_of_string s)-i ->
       bytes_of_string (substring (Z.to_nat i) (Z.to_nat j) s) = sublist i (i+j) (bytes_of_string s).
Proof.
intros.
unfold bytes_of_string, list_byte_of_string in *.
rewrite map_map.
rewrite Zlength_map in H0.
revert i j H H0; induction s; simpl; intros.
-
change (Zlength _) with 0 in H0.
assert (j=0) by lia. subst j. assert (i=0) by lia. subst. simpl. reflexivity.
-
rewrite Zlength_cons in H0.
destruct (Z.to_nat i) eqn:?H.
assert (i=0) by lia; subst i.
destruct (Z.to_nat j) eqn:?H.
assert (j=0) by lia. subst j.
autorewrite with sublist.
reflexivity.
simpl.
rewrite sublist_0_cons by lia.
f_equal.
specialize (IHs 0 (Z.of_nat n)) .
rewrite Nat2Z.id, Z.add_0_l in IHs.
change (Z.to_nat 0) with O in IHs.
unfold compose in IHs.
rewrite IHs; try lia.
f_equal.
lia.
specialize (IHs (i-1) j).
unfold compose in IHs.
replace (Z.to_nat (i-1)) with n in IHs by lia.
rewrite IHs; try lia.
rewrite sublist_pos_cons by lia.
f_equal.
lia.
Qed.

Lemma bytes_of_string_inj: forall r s, bytes_of_string r = bytes_of_string s -> r=s.
Proof.
intros ? ?.
unfold bytes_of_string, list_byte_of_string.
rewrite !map_map.
set (f := fun _ => _).
revert s;
induction r; destruct s; simpl; intros; auto; try discriminate.
f_equal.
-
assert (f a = f a0) by congruence.
clear - H0.
subst f.
simpl in *.
rewrite <- (Ascii.ascii_of_byte_of_ascii a), <- (Ascii.ascii_of_byte_of_ascii a0).
f_equal.
apply bytestring.to_N_inj.
forget (Ascii.byte_of_ascii a) as x. forget (Ascii.byte_of_ascii a0) as y.
pose proof (Byte.to_N_bounded x).
pose proof (Byte.to_N_bounded y).
apply N2Z.inj.
rewrite <- Byte.unsigned_repr by rep_lia.
rewrite <- (Byte.unsigned_repr (Z.of_N (Byte.to_N x))) by rep_lia.
f_equal.
auto.
-
apply IHr.
congruence.
Qed.

Local Lemma bytes_to_words_length': forall n: nat,
  forall bl, Zlength bl < Z.of_nat n ->
   Zlength (bytes_to_words bl) = Zlength bl / 8.
Proof.
 induction n; intros. rep_lia.
 do 8 (destruct bl as [ | ?b bl]; [reflexivity | ] ).
 unfold bytes_to_words. fold (bytes_to_words bl).
 set (j := Int64.repr _). clearbody j.
 rewrite !Zlength_cons.
 unfold Z.succ.
 rewrite <- !Z.add_assoc.
 change (1 + _) with (1*8).
 rewrite Z.div_add by lia.
 rewrite <- IHn. auto.
 rewrite !Zlength_cons in H. lia.
Qed.
 
Lemma bytes_to_words_length: forall bl, 
   Zlength (bytes_to_words bl) = Zlength bl / 8.
Proof.
 intros.
 apply (bytes_to_words_length' (S (Z.to_nat (Zlength bl)))).
 lia.
Qed.

Lemma data_at_int_or_ptr_int:
 forall {CS: compspecs} sh i p,
  data_at sh int_or_ptr_type (Vptrofs i) p
  = data_at sh size_t (Vptrofs i) p.
Proof.
 intros.
 unfold data_at, field_at.
 simpl. f_equal.
 f_equal.
 unfold field_compatible.
 f_equal.
 f_equal.
 f_equal.
 f_equal.
 unfold align_compatible.
 destruct p; auto.
 apply prop_ext; split; intro;
  eapply align_compatible_rec_by_value_inv in H;
   try reflexivity;
  try (eapply align_compatible_rec_by_value; eauto).
  reflexivity.
  reflexivity.
Qed.


Local Opaque Int64.repr.

Lemma bytestring_contents_lemma1:
  forall g g' bytes k, map (field2val BYTESTRING_TAG g) 
       (make_fields' (map (fun i : int64 => Some (inl (Int64.unsigned i))) (bytes_to_words bytes))
             g' k) = 
    map Vlong (bytes_to_words bytes).
Proof.
intros.
set (n := length bytes).
assert (Zlength bytes <= Z.of_nat n).
rewrite Zlength_correct; lia.
clearbody n.
revert bytes H k; induction n; intros.
destruct bytes. reflexivity. exfalso. list_solve.
do 8 (destruct bytes; simpl; [ reflexivity | ]).
rewrite if_false by (intro; discriminate).
specialize (IHn bytes ltac:(list_solve)).
f_equal; auto.
f_equal; auto.
rewrite Int64.unsigned_repr
 by (unfold decode_int, rev_if_be; destruct Archi.big_endian; simpl ; rep_lia).
set (a := decode_int _).
auto.
Qed.

Lemma Vlong_inj
     : forall x y : int64, Vlong x = Vlong y -> x = y.
Proof.
intros.
inv H. auto.
Qed.

Section Foo.

Import predicates_hered predicates_sl res_predicates normalize.
Lemma address_mapsto_8bytes_aux: 
 forall (sh : Share.t)
   (b0 b1 b2 b3 b4 b5 b6 b7: byte)
   (b : block) (i : ptrofs)
   (SZ : Ptrofs.unsigned i + 8 < Ptrofs.modulus)
   (r : readable_share sh),

predicates_sl.sepcon
  (predicates_sl.sepcon
     (predicates_sl.sepcon
        (predicates_sl.sepcon
           (predicates_sl.sepcon
              (predicates_sl.sepcon
                 (predicates_sl.sepcon
                    (predicates_hered.allp
                       (res_predicates.jam
                          (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk Mint8unsigned))
                          (fun loc : address =>
                           res_predicates.yesat compcert_rmaps.RML.R.NoneP
                             (compcert_rmaps.VAL
                                (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned i)))
                                   [Byte b0] Undef)) sh loc) res_predicates.noat))
                    (predicates_hered.allp
                       (res_predicates.jam
                          (adr_range_dec
                             (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))
                             (size_chunk Mint8unsigned))
                          (fun loc : address =>
                           res_predicates.yesat compcert_rmaps.RML.R.NoneP
                             (compcert_rmaps.VAL
                                (nth
                                   (Z.to_nat
                                      (snd loc
                                         - snd
                                             (b,
                                              Ptrofs.unsigned
                                                (Ptrofs.add i (Ptrofs.repr 1)))))
                                   [Byte b1] Undef)) sh loc) res_predicates.noat)))
                 (predicates_hered.allp
                    (res_predicates.jam
                       (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))
                          (size_chunk Mint8unsigned))
                       (fun loc : address =>
                        res_predicates.yesat compcert_rmaps.RML.R.NoneP
                          (compcert_rmaps.VAL
                             (nth
                                (Z.to_nat
                                   (snd loc
                                      - snd
                                          (b,
                                           Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))))
                                [Byte b2] Undef)) sh loc) res_predicates.noat)))
              (predicates_hered.allp
                 (res_predicates.jam
                    (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))
                       (size_chunk Mint8unsigned))
                    (fun loc : address =>
                     res_predicates.yesat compcert_rmaps.RML.R.NoneP
                       (compcert_rmaps.VAL
                          (nth
                             (Z.to_nat
                                (snd loc
                                   - snd
                                       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))))
                             [Byte b3] Undef)) sh loc) res_predicates.noat)))
           (predicates_hered.allp
              (res_predicates.jam
                 (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4)))
                    (size_chunk Mint8unsigned))
                 (fun loc : address =>
                  res_predicates.yesat compcert_rmaps.RML.R.NoneP
                    (compcert_rmaps.VAL
                       (nth
                          (Z.to_nat
                             (snd loc
                                - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4)))))
                          [Byte b4] Undef)) sh loc) res_predicates.noat)))
        (predicates_hered.allp
           (res_predicates.jam
              (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 5)))
                 (size_chunk Mint8unsigned))
              (fun loc : address =>
               res_predicates.yesat compcert_rmaps.RML.R.NoneP
                 (compcert_rmaps.VAL
                    (nth
                       (Z.to_nat
                          (snd loc
                             - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 5)))))
                       [Byte b5] Undef)) sh loc) res_predicates.noat)))
     (predicates_hered.allp
        (res_predicates.jam
           (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 6)))
              (size_chunk Mint8unsigned))
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth
                    (Z.to_nat
                       (snd loc - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 6)))))
                    [Byte b6] Undef)) sh loc) res_predicates.noat)))
  (predicates_hered.allp
     (res_predicates.jam
        (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 7)))
           (size_chunk Mint8unsigned))
        (fun loc : address =>
         res_predicates.yesat compcert_rmaps.RML.R.NoneP
           (compcert_rmaps.VAL
              (nth
                 (Z.to_nat
                    (snd loc - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 7)))))
                 [Byte b7] Undef)) sh loc) res_predicates.noat)) = 
predicates_hered.allp
  (res_predicates.jam (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk Mint64))
     (fun loc : address =>
      res_predicates.yesat compcert_rmaps.RML.R.NoneP
        (compcert_rmaps.VAL
           (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned i)))
              [Byte b0; Byte b1; Byte b2; Byte b3; Byte b4; Byte b5; Byte b6; Byte b7]
              Undef)) sh loc) res_predicates.noat).
Proof.
intros.

     simpl snd.
    simpl size_chunk.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
  change [Byte b0; Byte b1; Byte b2; Byte b3; Byte b4; Byte b5; Byte b6; Byte b7] 
  with (map Byte [b0;b1;b2;b3;b4;b5;b6;b7]).
   

repeat lazymatch goal with |- _ = ?R =>
 lazymatch R with context [nth _ (map Byte ?al)] =>
  lazymatch al with _ :: _ =>
   let len := constr:(Zlength al) in let len := eval compute in len in 
   let part1 := constr:(sublist.sublist 0 (len-1) al) in let part1 := eval compute in part1 in
   let part2 := constr:(sublist.sublist (len-1) len al) in let part2 := eval compute in part2 in
   rewrite  (res_predicates.allp_jam_split2 _ _ _ 
           (fun loc : address =>
            yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    (map Byte al) Undef)) sh loc)
           (fun loc : address =>
            yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    (map Byte part1) Undef)) sh loc)
           (fun loc : address =>
            yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - ((len-1)+Ptrofs.unsigned i)))
                    (map Byte part2) Undef)) sh loc)
           (adr_range_dec (b, Ptrofs.unsigned i) len)
           (adr_range_dec (b, Ptrofs.unsigned i) (len-1))
           (adr_range_dec (b, (len-1) + Ptrofs.unsigned i) 1));
  [ 
  | eexists; apply res_predicates.is_resource_pred_YES_VAL'
  | eexists; apply res_predicates.is_resource_pred_YES_VAL'
  | eexists; apply res_predicates.is_resource_pred_YES_VAL'
  | clear; split; intros [? ?]; simpl; intuition rep_lia
  |intros; f_equal; f_equal;
       destruct l; destruct H; subst; simpl snd;
       change al with (List.app (sublist.sublist 0 (len-1) al) (sublist.sublist (len-1) len al));
       rewrite map_app, app_nth1 by (simpl; lia);
       reflexivity
  | intros; f_equal; f_equal; 
       destruct l; destruct H; subst; simpl snd;
       change al with (List.app (sublist.sublist 0 (len-1) al) (sublist.sublist (len-1) len al));
       rewrite map_app, app_nth2 by (simpl; lia);simpl sublist.sublist;
       simpl length;
       match type of H0 with ?a <= _ < _ => assert (z=a) by lia end; subst z;
       rewrite Z.sub_diag;
       replace (_ - _) with (len-1) by lia;
       reflexivity
  |intros; left; destruct H0; hnf in H0; rewrite H0 in H1; clear H0;
        destruct l, H; subst; simpl snd in *;
    rewrite nth_map'  with (d' :=  Byte.zero) in H1 by (simpl; lia);
    inv H1; apply I
  ];
  f_equal; really_simplify (len-1)   
  end end end.
Qed.


Lemma address_mapsto_8bytes_forward:
 forall 
    (AP: Archi.ptr64 = true)  (* Perhaps this premise could be eliminated. *)
   (sh : Share.t)
    (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
    (b : block)
    (i : ptrofs)
    (SZ : Ptrofs.unsigned i + 8 < Ptrofs.modulus)
    (AL : (8 | Ptrofs.unsigned i))
    (r : readable_share sh),
predicates_hered.derives
 (predicates_sl.sepcon
 (predicates_sl.sepcon
  (predicates_sl.sepcon
   (predicates_sl.sepcon
    (predicates_sl.sepcon
     (predicates_sl.sepcon
      (predicates_sl.sepcon
       (res_predicates.address_mapsto Mint8unsigned 
           (Vubyte b0) sh (b, Ptrofs.unsigned i))
       (res_predicates.address_mapsto Mint8unsigned 
           (Vubyte b1) sh
           (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))))
       (res_predicates.address_mapsto Mint8unsigned 
         (Vubyte b2) sh (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b3) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b4) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b5) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 5)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b6) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 6)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b7) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 7)))))
 (res_predicates.address_mapsto Mint64
  (Vlong (Int64.repr (decode_int [b0; b1; b2; b3; b4; b5; b6; b7]))) sh
  (b, Ptrofs.unsigned i)).
Proof.
intros.
      unfold res_predicates.address_mapsto. rewrite <- !exp_equiv.
    repeat change (seplog.exp ?A) with (predicates_hered.exp A).
    normalize.normalize.
    intros bl7 [A7 [B7 _]] bl6 bl5 bl4 bl3 bl2 bl1 bl0.
    normalize.normalize.
    destruct H as [A6 [ B6 _]].
    destruct H0 as [A5 [ B5 _]].
    destruct H1 as [A4 [ B4 _]].
    destruct H2 as [A3 [ B3 _]].
    destruct H3 as [A2 [ B2 _]].
    destruct H4 as [A1 [ B1 _]].
    destruct H5 as [A0 [ B0 _]].
    destruct bl0 as [ | c0 [|]]; inv A0; inv B0. 
    destruct bl1 as [ | c1 [|]]; inv A1; inv B1.
    destruct bl2 as [ | c2 [|]]; inv A2; inv B2. 
    destruct bl3 as [ | c3 [|]]; inv A3; inv B3.
    destruct bl4 as [ | c4 [|]]; inv A4; inv B4. 
    destruct bl5 as [ | c5 [|]]; inv A5; inv B5.
    destruct bl6 as [ | c6 [|]]; inv A6; inv B6. 
    destruct bl7 as [ | c7 [|]]; inv A7; inv B7.
    destruct c0; try discriminate H0.
    destruct c1; try discriminate H1.
    destruct c2; try discriminate H2.
    destruct c3; try discriminate H3.
    destruct c4; try discriminate H4.
    destruct c5; try discriminate H5.
    destruct c6; try discriminate H6.
    destruct c7; try discriminate H7.
    apply decode_val_Vubyte_inj in H0,H1,H2,H3,H4,H5,H6,H7; subst.
   apply (predicates_hered.exp_right (map Byte [b0;b1;b2;b3;b4;b5;b6;b7])).
     rewrite predicates_hered.prop_true_andp.
      2:{ split3. reflexivity. reflexivity. apply AL. }
   rewrite address_mapsto_8bytes_aux; auto.
Qed.

Lemma address_mapsto_8bytes:
 forall 
    (AP: Archi.ptr64 = true)  (* Perhaps this premise could be eliminated. *)
   (sh : Share.t)
    (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
    (b : block)
    (i : ptrofs)
    (SZ : Ptrofs.unsigned i + 8 < Ptrofs.modulus)
    (AL : (8 | Ptrofs.unsigned i))
    (r : readable_share sh),

 predicates_sl.sepcon
 (predicates_sl.sepcon
  (predicates_sl.sepcon
   (predicates_sl.sepcon
    (predicates_sl.sepcon
     (predicates_sl.sepcon
      (predicates_sl.sepcon
       (res_predicates.address_mapsto Mint8unsigned 
           (Vubyte b0) sh (b, Ptrofs.unsigned i))
       (res_predicates.address_mapsto Mint8unsigned 
           (Vubyte b1) sh
           (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))))
       (res_predicates.address_mapsto Mint8unsigned 
         (Vubyte b2) sh (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b3) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b4) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b5) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 5)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b6) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 6)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b7) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 7))))
 = 
res_predicates.address_mapsto Mint64
  (Vlong (Int64.repr (decode_int [b0; b1; b2; b3; b4; b5; b6; b7]))) sh
  (b, Ptrofs.unsigned i).
Proof.
intros.
      unfold res_predicates.address_mapsto. rewrite <- !exp_equiv.
      apply predicates_hered.pred_ext.
  - repeat change (seplog.exp ?A) with (predicates_hered.exp A).
    normalize.normalize.
    intros bl7 [A7 [B7 _]] bl6 bl5 bl4 bl3 bl2 bl1 bl0.
    normalize.normalize.
    destruct H as [A6 [ B6 _]].
    destruct H0 as [A5 [ B5 _]].
    destruct H1 as [A4 [ B4 _]].
    destruct H2 as [A3 [ B3 _]].
    destruct H3 as [A2 [ B2 _]].
    destruct H4 as [A1 [ B1 _]].
    destruct H5 as [A0 [ B0 _]].
    destruct bl0 as [ | c0 [|]]; inv A0; inv B0. 
    destruct bl1 as [ | c1 [|]]; inv A1; inv B1.
    destruct bl2 as [ | c2 [|]]; inv A2; inv B2. 
    destruct bl3 as [ | c3 [|]]; inv A3; inv B3.
    destruct bl4 as [ | c4 [|]]; inv A4; inv B4. 
    destruct bl5 as [ | c5 [|]]; inv A5; inv B5.
    destruct bl6 as [ | c6 [|]]; inv A6; inv B6. 
    destruct bl7 as [ | c7 [|]]; inv A7; inv B7.
    destruct c0; try discriminate H0.
    destruct c1; try discriminate H1.
    destruct c2; try discriminate H2.
    destruct c3; try discriminate H3.
    destruct c4; try discriminate H4.
    destruct c5; try discriminate H5.
    destruct c6; try discriminate H6.
    destruct c7; try discriminate H7.
    apply decode_val_Vubyte_inj in H0,H1,H2,H3,H4,H5,H6,H7; subst.
   apply (predicates_hered.exp_right (map Byte [b0;b1;b2;b3;b4;b5;b6;b7])).
     rewrite predicates_hered.prop_true_andp.
      2:{ split3. reflexivity. reflexivity. apply AL. }
   rewrite address_mapsto_8bytes_aux; auto.
 -
  repeat change (seplog.exp ?A) with (predicates_hered.exp A).
  normalize.normalize.
  intros bl [? [? ?]]. simpl snd in H1.
  destruct bl as [|c0 [| c1 [| c2 [| c3 [|c4 [| c5 [| c6 [| c7 [|]]]]]]]]]; inv H.
  unfold decode_val, proj_bytes in H0. rewrite AP in H0. clear AP.
  destruct c0; [ discriminate H0 | | ] .
  2: {
   unfold Val.load_result in H0.
   unfold proj_value in H0.
   destruct (check_value _ _ _ _) eqn:?H in H0; [ | discriminate].
   destruct v; try discriminate.
   apply Vlong_inj in H0; subst i0. clear - H.
   simpl in H.

Local Ltac foo H := 
   destruct (Val.eq _ _) in H; try discriminate; simpl in H;
   destruct (quantity_eq Q64 _) in H; try discriminate; subst;
   match type of H with context [Nat.eqb ?i ?n] => 
       destruct (Nat.eqb_spec i n); try discriminate
   end;
   simpl in H; clear - H.
   foo H.
  repeat
   match type of H with match ?c with _ => _ end = _ => destruct c; try discriminate; foo H end.
   simpl snd.
   shelve.  (* NOT TRUE.  This lemma works only in the forward direction,
              because of Fragment.   For bytestring "pack", we only need the forward direction,
               but for "unpack" it will cause some annoyance.  One workaround for tha
               possible annoyance is that the C program can avoid using byte addressing
              to read the bytes, but instead use word addressing and shifting.  Ugh.  *)
  }
       destruct c1; [ discriminate H0 | | discriminate H0 ].
       destruct c2; try discriminate H0.
       destruct c3; try discriminate H0.
       destruct c4; try discriminate H0.
       destruct c5; try discriminate H0.
       destruct c6; try discriminate H0.
       destruct c7; try discriminate H0.
       apply Vlong_inj in H0.
       pose proof (decode_int_range [b0;b1;b2;b3;b4;b5;b6;b7]).
       pose proof (decode_int_range [i0;i1;i2;i3;i4;i5;i6;i7]).
       change (two_p _) with Int64.modulus in H,H2.
       apply repr_inj_unsigned64 in H0; try rep_lia.
       apply decode_int_inj in H0.
      clear H H2. inv H0.
     apply predicates_hered.exp_right with [Byte b7].
      normalize.normalize.
     apply predicates_hered.exp_right with [Byte b6].
      normalize.normalize.
     apply predicates_hered.exp_right with [Byte b5].
      normalize.normalize.
     apply predicates_hered.exp_right with [Byte b4].
      normalize.normalize.
     apply predicates_hered.exp_right with [Byte b3].
      normalize.normalize.
     apply predicates_hered.exp_right with [Byte b2].
      normalize.normalize.
     apply predicates_hered.exp_right with [Byte b1].
      normalize.normalize.
     apply predicates_hered.exp_right with [Byte b0].
     rewrite !predicates_hered.prop_true_andp by 
     (split3; [ reflexivity |  | apply Z.divide_1_l  ];
     unfold decode_val, Vubyte; simpl; f_equal;
     rewrite decode_int_single;
     apply zero_ext_inrange; change (two_p _ - 1) with 255;
     rewrite Int.unsigned_repr by rep_lia; rep_lia).
  match goal with |- predicates_hered.derives ?A ?B => 
        assert (EQ: B=A); [ | rewrite EQ; apply predicates_hered.derives_refl]
    end.
  apply address_mapsto_8bytes_aux; auto.
  reflexivity.
Abort.


Lemma nonlock_permission_8bytes:
 forall (sh : Share.t)
     (b : block) (i : ptrofs) 
     (SZ : Ptrofs.unsigned i + 8 < Ptrofs.modulus),
(res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 5))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 6))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 7))) 1)%logic = 
res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 8.
Proof.
intros.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
 rewrite (res_predicates.nonlock_permission_bytes_split2 7 1 8 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 6 1 7 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 5 1 6 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 4 1 5 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 3 1 4 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 2 1 3 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 1 1 2 sh) by lia.
 repeat change (predicates_sl.sepcon ?A ?B) with (A * B)%logic.
 rewrite !(Z.add_comm (Ptrofs.unsigned i)).
 f_equal.
Qed.

End Foo.

Lemma data_at_long_bytes_forward: 
  forall 
    (AP: Archi.ptr64 = true)  (* Perhaps this premise could be eliminated. *)
  sh 
   (b0 b1 b2 b3 b4 b5 b6 b7: byte) p,
  field_compatible tulong [] p  ->
  (data_at sh tuchar (Vubyte b0) p *
  data_at sh tuchar (Vubyte b1) (offset_val 1 p) *
  data_at sh tuchar (Vubyte b2) (offset_val 2 p) *
  data_at sh tuchar (Vubyte b3) (offset_val 3 p) *
  data_at sh tuchar (Vubyte b4) (offset_val 4 p) *
  data_at sh tuchar (Vubyte b5) (offset_val 5 p) *
  data_at sh tuchar (Vubyte b6) (offset_val 6 p) *
  data_at sh tuchar (Vubyte b7) (offset_val 7 p))%logic |--
  data_at sh tulong (Vlong (Int64.repr (decode_int [b0;b1;b2;b3;b4;b5;b6;b7]))) p.
Proof.
  intros AP sh b0 b1 b2 b3 b4 b5 b6 b7 p. unfold data_at. unfold field_at.
  intro. normalize. clear - H. simpl.
 destruct H as [H0 [_ [SZ [AL _]]]]. red in SZ. simpl sizeof in SZ.
   destruct p; inversion H0. clear H0.
 assert (8 | Ptrofs.unsigned i)
   by (eapply align_compatible_rec_by_value_inv in AL; [ | reflexivity]; assumption).
 clear AL.
 unfold at_offset. 
 rewrite !offset_offset_val. rewrite !Z.add_0_r.
 simpl offset_val. rewrite !ptrofs_add_repr_0_r.
 rewrite !data_at_rec_eq. simpl.
 change (unfold_reptype ?x) with x.
 unfold mapsto.
 simpl access_mode; simpl type_is_volatile; cbv iota.
 rewrite !(prop_true_andp _ _ (tc_val_Vubyte _)).
 rewrite !(prop_false_andp (_ = _)) by (intro Hx; inv Hx).
 rewrite !(prop_true_andp (tc_val tulong _)) by (apply Logic.I).
 rewrite ?prop_and_mpred.
 rewrite ?(prop_true_andp _ _ (tc_val_tc_val' _ _ (tc_val_Vubyte _))).
 rewrite !(prop_true_andp (tc_val' tulong _)) by (apply tc_val_tc_val'; apply Logic.I).
 rewrite ?(prop_true_andp _ _ (Z.divide_1_l _)).
 rewrite !orp_FF.
 rewrite (prop_true_andp (_ | _)) by apply H.
 if_tac.
-
 rewrite derives_eq.
 apply address_mapsto_8bytes_forward; auto.
- rewrite nonlock_permission_8bytes; auto.
  apply derives_refl.
Qed.


Lemma data_at_long_bytes: 
  forall 
    (AP: Archi.ptr64 = true)  (* Perhaps this premise could be eliminated. *)
  sh 
   (b0 b1 b2 b3 b4 b5 b6 b7: byte) p,
  field_compatible tulong [] p  ->
  (data_at sh tuchar (Vubyte b0) p *
  data_at sh tuchar (Vubyte b1) (offset_val 1 p) *
  data_at sh tuchar (Vubyte b2) (offset_val 2 p) *
  data_at sh tuchar (Vubyte b3) (offset_val 3 p) *
  data_at sh tuchar (Vubyte b4) (offset_val 4 p) *
  data_at sh tuchar (Vubyte b5) (offset_val 5 p) *
  data_at sh tuchar (Vubyte b6) (offset_val 6 p) *
  data_at sh tuchar (Vubyte b7) (offset_val 7 p))%logic =
  data_at sh tulong (Vlong (Int64.repr (decode_int [b0;b1;b2;b3;b4;b5;b6;b7]))) p.
Proof.
  intros AP sh b0 b1 b2 b3 b4 b5 b6 b7 p. unfold data_at. unfold field_at.
  intro.
  rewrite !prop_true_andp by auto with field_compatible.
 destruct H as [H0 [_ [SZ [AL _]]]]. red in SZ. simpl sizeof in SZ.
   destruct p; inversion H0. clear H0.
 assert (8 | Ptrofs.unsigned i)
   by (eapply align_compatible_rec_by_value_inv in AL; [ | reflexivity]; assumption).
 clear AL.
 unfold at_offset. 
 rewrite !offset_offset_val. rewrite !Z.add_0_r.
 simpl offset_val. rewrite !ptrofs_add_repr_0_r.
 rewrite !data_at_rec_eq. simpl.
 change (unfold_reptype ?x) with x.
 unfold mapsto.
 simpl access_mode; simpl type_is_volatile; cbv iota.
 rewrite !(prop_true_andp _ _ (tc_val_Vubyte _)).
 rewrite !(prop_false_andp (_ = _)) by (intro Hx; inv Hx).
 rewrite !(prop_true_andp (tc_val tulong _)) by (apply Logic.I).
 rewrite ?prop_and_mpred.
 rewrite ?(prop_true_andp _ _ (tc_val_tc_val' _ _ (tc_val_Vubyte _))).
 rewrite !(prop_true_andp (tc_val' tulong _)) by (apply tc_val_tc_val'; apply Logic.I).
 rewrite ?(prop_true_andp _ _ (Z.divide_1_l _)).
 rewrite !orp_FF.
 rewrite (prop_true_andp (_ | _)) by apply H.
 if_tac.
- shelve.  (* apply address_mapsto_8bytes; auto.*)
- apply nonlock_permission_8bytes; auto.
Abort.


Lemma bytestring_array_conversion:
 forall sh (x: list byte) pad_length bytes p,
  field_compatible (tarray int_or_ptr_type ((Zlength x + pad_length) / 8)) [] p ->
  pad_length = 8 - (Zlength x) mod 8 ->
  Zlength bytes = Zlength x + pad_length -> 
 data_at sh (tarray tuchar (Zlength x + pad_length)) (map Vubyte bytes) p
 |-- data_at sh (tarray int_or_ptr_type ((Zlength x + pad_length) / 8))
        (map Vlong (bytes_to_words bytes)) p.
Proof.
intros.
pose proof bytes_to_words_length bytes.
set (n := _ + _) in *.
assert (Z.divide 8 n).
subst n pad_length.
replace (Zlength x  + (8 - Zlength x mod 8)) with (Zlength x - Zlength x mod 8 + 8) by lia.
apply Z.divide_add_r.
apply Zmod_divide_minus; lia.
exists 1 ; lia.
clearbody n.
clear H0 pad_length.
destruct H3 as [k ?].
subst n.
rewrite H0 in *.
rewrite Z.div_mul in * by lia.
assert (exists j: nat, k = Z.of_nat j).
exists (Z.to_nat k). list_solve.
destruct H1 as [j ?].
rewrite H1 in *.
clear H1 k.
revert p bytes H0 H H2; induction j; intros.
destruct bytes; try list_solve.
simpl.
rewrite !data_at_zero_array_eq by auto. auto.
rewrite inj_S in *.
unfold tarray in *.

erewrite (split2_data_at_Tarray sh tuchar (Z.succ (Z.of_nat j) * 8) (1*8)
               (map Vubyte bytes) (map Vubyte bytes)); try reflexivity; try list_solve.
erewrite (split2_data_at_Tarray sh int_or_ptr_type (Z.succ (Z.of_nat j)) 1
               (map Vlong (bytes_to_words bytes)) (map Vlong (bytes_to_words bytes))); try reflexivity; try list_solve.
apply sepcon_derives; auto.
-
assert (8 <= Zlength bytes) by lia.
clear - H H1 H2.
do 8 (destruct bytes as [ | ?b bytes] ; [ exfalso; list_solve | ]).
rewrite !sublist_map.
rewrite !sublist_0_cons by reflexivity.
simpl.
fold (tarray int_or_ptr_type 1).
erewrite data_at_singleton_array_eq by reflexivity.
assert (Vlong (Int64.repr (decode_int [b; b0; b1; b2; b3; b4; b5; b6]))
     =  Vptrofs (Ptrofs.repr (decode_int [b; b0; b1; b2; b3; b4; b5; b6]))).
  rewrite Vptrofs_unfold_true, ptrofs_to_int64_repr by reflexivity; auto.
rewrite H0.
rewrite data_at_int_or_ptr_int.
rewrite <- H0.
change size_t with tulong.
eapply derives_trans; [ | apply data_at_long_bytes_forward]; auto.
2:{
clear - H.
destruct H as [? [? [? [? ? ]]]]; split3; auto.
split3; auto.
destruct p; try contradiction; red in H1|-*. simpl sizeof in H1.
rewrite Z.max_r in H1 by lia. simpl sizeof. lia.
red in H2|-*. destruct p; auto.
apply align_compatible_rec_Tarray_inv with (i:=0) in H2; try lia.
simpl in H2.
eapply align_compatible_rec_by_value_inv in H2; try reflexivity.
eapply align_compatible_rec_by_value; try reflexivity.
rewrite Z.add_0_r in H2.
auto.
}
fold (tarray tuchar 8).
rewrite !sepcon_assoc.
repeat 
lazymatch goal with |- data_at _ (tarray _ ?n) (_ :: ?l) _ |-- _ =>
   change n with (Zlength l + 1);
   rewrite data_at_tarray_split_1 by reflexivity;
   rewrite ?offset_offset_val; 
   apply sepcon_derives; [ apply derives_refl | simpl Z.add]; simpl sizeof
end.
change (Zlength [_]) with 1.
rewrite data_at_tuchar_singleton_array_eq.
apply derives_refl.
-
specialize (IHj (offset_val 8 p) (sublist 8 (Zlength bytes) bytes)).
replace (Z.succ (Z.of_nat j) * 8 - 1 * 8) with (Z.of_nat j * 8)  by lia.
replace (Z.succ (Z.of_nat j) - 1) with (Z.of_nat j) by lia.
change (1*8) with 8.
rewrite <- H0.
unfold field_address0.
rewrite if_true.
2:{
clear - H H2 H0.
destruct H as [? [? [? [? ? ]]]]; split3; auto.
split3; auto.
red in H3|-*. destruct p; auto. simpl in H3|-*. 
rewrite Z.max_r in * by rep_lia.
rep_lia.
destruct p; auto.
apply align_compatible_rec_Tarray.
2: split; hnf; auto; rep_lia.
intros.
eapply align_compatible_rec_by_value; try reflexivity.
apply Z.divide_1_l.
}
rewrite if_true by auto with field_compatible.
simpl.
rewrite !sublist_map.
replace (sublist 1 (Z.succ (Z.of_nat j)) (bytes_to_words bytes))
  with (bytes_to_words (sublist 8 (Zlength bytes) bytes)). 2:{
  clear - H0 H2.
  do 8 (destruct bytes as [ | ?b bytes] ; [ exfalso; list_solve | ]).
 simpl.
 rewrite !sublist_pos_cons by reflexivity.
 rewrite !Zlength_cons.
 rewrite !Z.sub_diag.
 unfold Z.succ.
 replace  (Zlength bytes + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1)
   with (Zlength bytes) by lia.
 replace (Z.of_nat j + 1 - 1) with (Z.of_nat j) by lia.
 rewrite sublist_same by lia.
 rewrite sublist_same; auto.
 simpl in H2. list_solve.
}
apply IHj.
list_solve.
clear - H. {
 fold (tarray int_or_ptr_type (Z.succ (Z.of_nat j))) in H.
 fold (tarray int_or_ptr_type (Z.of_nat j)).
 pose proof H.
 rewrite field_compatible_Tarray_split with (i:=1) in H0 by rep_lia.
 destruct H0 as [_ ?].
 unfold field_address0 in H0.
 rewrite if_true in H0 by auto with field_compatible.
 simpl in H0.
 replace (Z.succ (Z.of_nat j) - 1) with (Z.of_nat j) in H0 by lia.
 auto.
}
rewrite bytes_to_words_length.
rewrite Zlength_sublist by list_solve.
rewrite H0.
clear.
unfold Z.succ.
change 8 with (1*8) at 2.
rewrite <- Z.mul_sub_distr_r.
rewrite Z.div_mul by lia.
lia.
Qed.

Lemma body_pack:
  semax_body Vprog Gprog f_pack specs.pack_spec.
Proof.
 start_function'.
 forward.
 forward.
 change (Tpointer _ _) with int_or_ptr_type. simpl snd.
 unfold full_gc.
 unfold before_gc_thread_info_rep.
 Intros.
 limited_change_compspecs CompSpecs.
 forward.
 forward.
 forward.
 forward.
 change (temp _temp _) with (temp _temp (rep_type_val g p)).
 sep_apply (representable_string_max_length x g outlier p); auto.
 Intros.
 rewrite Int.signed_repr by rep_lia.
 sep_apply_compspecs CompSpecs 
  (frame_rep__fold Tsh v___FRAME__ v___ROOT__ (ti_fp t_info) 1 (Vlong (Int64.repr 0))).
 sep_apply_compspecs CompSpecs (before_gc_thread_info_rep_fold sh t_info ti).
 sep_apply (full_gc_fold gv g t_info roots outlier ti sh).
 forward_loop
   (EX s:string, EX ps: rep_type,
     PROP (Z.of_nat (String.length s) <= Z.of_nat (String.length x);
           is_in_graph g outlier s ps)
     LOCAL (temp _len (Vlong (Int64.repr 
               (Z.of_nat (String.length x) - Z.of_nat (String.length s))));
            temp _temp (rep_type_val g ps);
            lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
            lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; 
            gvars gv; temp _tinfo ti; temp _save0 (rep_type_val g p))
     SEP (full_gc g t_info roots outlier ti sh gv; library.mem_mgr gv;
          frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info) 1))
   break: 
    (PROP ()
     LOCAL (temp _len (Vlong (Int64.repr (Z.of_nat (String.length x))));
            lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
            lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; 
            gvars gv; temp _tinfo ti; temp _save0 (rep_type_val g p))
     SEP (full_gc g t_info roots outlier ti sh gv; library.mem_mgr gv;
          frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info) 1)).
 - Exists x p. entailer!!. f_equal. f_equal. lia.
 - Intros s ps.
   rewrite graph_rep_full_gc.
   forward_call (g,outlier,ps,s). cancel.
   forward_if.
   + (* then *)
   destruct s; try discriminate H5.
   forward.
   forward_call (g,outlier,ps,(a,s)).
   Intros vret; destruct vret as [[p0 p1] sh']. simpl snd in *; simpl fst in *.
   assert_PROP (is_pointer_or_integer (rep_type_val g p0)). {
    sep_apply modus_ponens_wand. 
    sep_apply (is_pointer_or_integer_rep_type_val g outlier a p0). entailer!!.
   }
   assert_PROP (is_pointer_or_integer (rep_type_val g p1)). {
    sep_apply modus_ponens_wand.
    sep_apply (is_pointer_or_integer_rep_type_val g outlier s p1). entailer!!.
   }
   forward.
   sep_apply modus_ponens_wand.
   sep_apply modus_ponens_wand.
   Exists s p1.
   simpl in H3.
   entailer!!.
   f_equal. f_equal. simpl. lia.
  + (* else *)
   forward.
   destruct s; simpl in H5; try congruence.
   sep_apply modus_ponens_wand.
   entailer!!.
 - change (Tpointer _ _) with int_or_ptr_type.
   forward.
   change (Tpointer _ _) with int_or_ptr_type.
   forward.
   forward.
   deadvars!.
  set (len := Z.of_nat (String.length x)) in *.
  assert (LEN: 0 <= len < MAX_LEN) by (clear - H2; lia). clear H2.
  revert LEN; really_simplify MAX_LEN; intro.
  set (pad_length := 8 - len mod 8).
  assert (PAD: 0 < pad_length <= 8) by (clear; pose proof (Z.mod_pos_bound len 8); lia).
  set (n := (len + pad_length) / 8 + 1).
  replace (Int64.sub _ _) with (Int64.repr pad_length). 2:{
    change (Ptrofs.to_int64 _) with (Int64.repr 8).
    unfold Int64.modu.
    rewrite Int64.unsigned_repr
       by (clear - LEN;  clearbody len; simpl in *; rep_lia).
    rewrite Int64.unsigned_repr by rep_lia.
     rewrite sub64_repr. f_equal; auto.
  }
  rewrite add64_repr.
  change (Ptrofs.to_int64 _) with (Int64.repr 8).
  rewrite divu_repr64;
    [ | clear - LEN PAD; revert LEN; really_simplify Int64.max_unsigned; intros; simpl in LEN; lia
      | rep_lia].
  rewrite add64_repr. fold n.
  eapply semax_seq'.
  +
   eapply semax_Delta_subsumption with GC_SAVE1_tycontext.
   apply prove_tycontext_sub; try reflexivity; repeat split; auto.
   apply (@semax_cssub filteredCompSpecs).
   apply prove_cssub; repeat split; auto; try reflexivity.

  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ (normal_ret_assert ?Post) =>
  let Q1 := get_rep_temps _tinfo _nalloc Q in
  let Q2 := get_nonrep_temps _tinfo _nalloc Q in
  let R1 := get_gc_mpreds R in
  let R2 := get_nongc_mpreds R in
 eapply (semax_frame_PQR'' Q1 Q2 R1 R2); 
  [solve [auto 50 with closed] 
  | solve [go_lowerx; autorewrite with norm; cancel]
  | apply perhaps_gc_1_live_root_aux
  |  ]
 end.
eapply semax_pre; [ | 
  apply (semax_GC_SAVE1 n Espec gv sh ti outlier v___ROOT__ v___FRAME__ H p _ x); try eassumption].
entailer!!.
* clear - LEN. clearbody len. subst n. subst pad_length.
    assert (0 <= len < Int64.modulus / 4).
    revert LEN.
    really_simplify (Int64.modulus / 4).
    really_simplify (Int64.max_unsigned / 4). intro. lia.
    assert (0 <= (len + (8 - len mod 8)) / 8 + 1 < Int64.modulus/2).
    2:{destruct H0; split; auto.
       unfold Int64.max_signed, Int64.half_modulus. lia.
    }
    clear LEN.
    change Int64.modulus with ((Int64.modulus/8)*8) in *.
    change (Int64.modulus / 8 * 8 / 4) with (2*(Int64.modulus/8)) in H.
    change (Int64.modulus/8*8/2) with (4*(Int64.modulus/8)).
    assert (8 < Int64.modulus/8) by (simpl; lia).
    set (N := Int64.modulus / 8) in *. clearbody N.
    assert (0 <= len mod 8 < 8) by (apply Z.mod_bound_pos; lia).    
    assert (0 <= (len + (8 - len mod 8)) / 8) by (apply Z_div_nonneg_nonneg; lia).
    split; [lia | ].
    assert (len + (8 - len mod 8) <= len + 8) by lia.
    apply Z.le_lt_trans with ((len + 8)/8 + 1).
    apply Z.add_le_mono_r.
    apply Z.div_le_mono; try lia.
    change 8 with (1*8) at 1; rewrite Z.div_add by lia.
    clear - H H0.
    apply Z.le_lt_trans with ((len+2) + (2*N-2)); try lia.
    replace (len + 2 + (2*N-2)) with (len + (2*N-2) + 2) by lia.
    rewrite <- Z.add_assoc. change (1+1) with 2.
    apply Z.add_le_mono_r.
    assert (len / 8 <= len) by (apply Z.div_le_upper_bound; lia).
    lia.
* eapply space_start_isptr'; eassumption.

+
 Intros g' v0' roots' t_info'.
 abbreviate_semax.
 simpl app. 
 assert (0 < n). {
   subst n.
   assert (len mod 8 < 8) by (apply Z_mod_lt; lia).
   assert (0 <= pad_length) by lia.  
   assert (0 <= (len + pad_length) / 8) by (apply Z.div_pos; lia).
   lia.
  }
 assert (HEADROOM: 0 <= n <= headroom t_info') by lia.
 pose (pp := Build_alloc_prepackage g' t_info' outlier n HEADROOM).
 forward_call (gv,roots',sh,ti,pp).
 simpl. cancel.
 simpl.  
 set (sh' := nth_sh g' 0).
 assert (Hsh' : writable_share sh'). {
   subst sh'.
   clear.
   unfold nth_sh. unfold generation_sh.
   destruct (nth_gen g' 0); auto.
 }
 set (t_info3 := bump_alloc pp).
 change (ti_fp t_info') with (ti_fp t_info3).
 
 assert (isptr (space_start (heap_head (ti_heap t_info')))) by 
   (eapply space_start_isptr'; eassumption).
 simpl fst. simpl snd.
 change (Tpointer _ _) with int_or_ptr_type.
 set (new0 := alloc_at t_info').
 set (WAND := allp _).
 simpl AP_n.
 assert_PROP (field_compatible (tarray int_or_ptr_type n) nil new0) as FC by entailer!.
 rewrite (split2_data_at__Tarray_app 1) by lia. 
 Intros.
 forward.
 change (default_val (tarray int_or_ptr_type 1)) with [Vundef].
 rewrite upd_Znth0 by lia.
 set (new1 := field_address0 (tarray int_or_ptr_type n) (SUB 1) new0).
 sep_apply data_at__memory_block_cancel.
 assert (0 <= 8 * (n - 1) < Ptrofs.modulus). {
   pose proof (total_space_tight_range (heap_head (ti_heap t_info'))).
   pose proof (space_order (heap_head (ti_heap t_info'))).
   clear - H7 H9 H10 HEADROOM. unfold MAX_SPACE_SIZE in H9. simpl in H9, HEADROOM.
   unfold headroom in HEADROOM.
   really_simplify Ptrofs.modulus.
   set (tot := total_space _) in *. set (use := used_space _) in *.
   clearbody tot. clearbody use. clearbody n. clear - H7 H9 H10 HEADROOM.
   revert H9.
   really_simplify GCGraph.MAX_SPACE_SIZE.
   split; try lia.   
 }
 sep_apply memory_block_data_at__tarray_tuchar.
 simpl. rewrite Z.max_r by lia. auto. 
 simpl sizeof. rewrite Z.max_r by lia.
 replace (8 * (n-1)) with (len + pad_length).
2:{
 subst n.
 rewrite <- Z.add_sub_assoc.
 change (1-1) with 0.
 rewrite Z.add_0_r.
 rewrite <- Z_div_exact_2; try lia.
 subst pad_length.
 rewrite Z.add_sub_assoc.
 rewrite Z.add_comm.
 rewrite <- Z.add_sub_assoc.
 rewrite Zplus_mod.
 simpl.
 rewrite Zminus_mod.
 rewrite !Zmod_mod.
 rewrite Z.sub_diag. reflexivity.
 }
 forward.
 forward.
 fold (rep_type_val g' v0').
 deadvars!. change (Tpointer _ _) with int_or_ptr_type.
 rewrite Int64.shl_mul_two_p.
 rewrite Int.signed_repr by rep_lia.
 rewrite Int.unsigned_repr by rep_lia.
 rewrite !Int64.unsigned_repr by rep_lia.
 rewrite sub64_repr, mul64_repr, add64_repr.
 replace (force_val (sem_binary_operation' _ _ _ _ _)) with new1.
 2:{ clear - H8 FC H7.
     hnf in new0.
     unfold alloc_at; simpl.
     set (s := space_start _) in *.
     subst new0 new1.
     clearbody s. destruct s; try contradiction.
     unfold field_address0.
     rewrite if_true; auto with field_compatible.
 }
 simpl AP_ti.
 fold new0. fold new1.
 freeze FR1 := - (data_at_ sh' (tarray tuchar (len + pad_length)) new1) 
    (graph_rep g').
 assert (FC1: field_compatible (tarray tuchar (len + pad_length)) nil new1). {   
   destruct new0; generalize FC; intros [HH _]; try contradiction HH.
   subst new1.
   unfold field_address0.
   rewrite if_true by auto with field_compatible. simpl. 
   clear - FC LEN PAD H9.
   destruct FC as [? [? [? [? ?]]]].
   split3; auto. split3; auto.
   red in H1|-*. simpl in H1|-*. rewrite Z.max_r by lia. rewrite Z.mul_1_l.
   rewrite Z.max_r in H1 by lia.
   rewrite <- (Ptrofs.repr_unsigned i). rewrite ptrofs_add_repr.
   rewrite Ptrofs.unsigned_repr by rep_lia.
   assert (8 + (len + pad_length) <= 8*n); [ | lia].
   subst n. rewrite Z.mul_add_distr_l.
   rewrite <- Zdivide_Zdiv_eq. lia. lia.
   subst pad_length. replace (len + (8 - len mod 8)) with (8 + (len - len mod 8)) by lia.
   apply Z.divide_add_r.
   exists 1; lia.
   apply Zmod_divide_minus; auto. lia.
   apply align_compatible_rec_Tarray; intros.
   eapply align_compatible_rec_by_value. reflexivity. apply Z.divide_1_l.
 } 

 forward_loop 
  (EX i, EX v: rep_type, 
   PROP (0 <= i <= len; is_in_graph g' outlier (substring (Z.to_nat i) (Z.to_nat (len-i)) x) v)
   LOCAL (temp _temp (rep_type_val g' v); 
          temp _ptr (field_address0 (tarray tuchar (len+pad_length)) (SUB i) new1);
          temp _argv new0;
   lvar specs_general.___FRAME__ (Tstruct specs_general._stack_frame noattr) v___FRAME__;
   lvar specs_general.___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__;
   gvars gv; temp _pad_length (Vlong (Int64.repr pad_length)))
   SEP (FRZL FR1; graph_rep (AP_g pp);
        data_at sh' (tarray tuchar (len+pad_length)) 
            (app (map Vubyte (sublist 0 i (bytes_of_string x))) (Zrepeat Vundef (len+pad_length-i)))
            new1))
  break: 
   (PROP ()
   LOCAL (temp _ptr (field_address0 (tarray tuchar (len+pad_length)) (SUB len) new1);
          temp _argv new0;
   lvar specs_general.___FRAME__ (Tstruct specs_general._stack_frame noattr) v___FRAME__;
   lvar specs_general.___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__;
   gvars gv; temp _pad_length (Vlong (Int64.repr pad_length)))
   SEP (FRZL FR1; graph_rep (AP_g pp);
        data_at sh' (tarray tuchar (len+pad_length)) 
            (app (map Vubyte (bytes_of_string x)) (Zrepeat Vundef pad_length)) new1)).
* Exists 0. Exists v0'. change (Z.to_nat 0) with O.
  unfold len at 3. rewrite Z.sub_0_r. rewrite Nat2Z.id.
  rewrite (proj1 (prefix_correct x x))
    by (clear; induction x; simpl; auto; rewrite if_true; auto).
 entailer!!.
  --
   rewrite arr_field_address0; try lia; auto.
   destruct FC1 as [HH _]. simpl. apply isptr_offset_val_zero; auto. 
 --
   simpl. cancel.
* 
  Intros i v.
  set (s := substring (Z.to_nat i) (Z.to_nat (len-i)) x) in *.
   forward_call (g',outlier,v,s). simpl AP_g. cancel.
   forward_if; fold len in H12; fold s in H12.
   -- (* then clause *)
      pose proof (string_desc_has_tag_prop s).
       destruct s as [ | ch r] eqn:?H; try discriminate H12.
       abbreviate_semax. deadvars!.
   forward_call (g',outlier,v,(ch,r)).
   Intros vret; destruct vret as [[p0 p1] sh'']. simpl snd in *; simpl fst in *.
   assert_PROP (is_pointer_or_integer (rep_type_val g' p0)). {
    sep_apply modus_ponens_wand. unfold full_gc. Intros.
    sep_apply (is_pointer_or_integer_rep_type_val g' outlier ch  p0). entailer!!.
   }
   assert_PROP (is_pointer_or_integer (rep_type_val g' p1)). {
    sep_apply modus_ponens_wand. unfold full_gc. Intros.
    sep_apply (is_pointer_or_integer_rep_type_val g' outlier r p1). entailer!!.
   }
   forward.
   sep_apply modus_ponens_wand.
   rewrite Znth_0_cons.
   forward_call (g',outlier,p0,ch).
   assert_PROP (field_address0 (tarray tuchar (len + pad_length)) (SUB i) new1 = 
                field_address (tarray tuchar (len+pad_length)) (SUB i) new1
           /\ isptr (field_address0 (tarray tuchar (len + pad_length)) (SUB i) new1)).
    {entailer!.
     apply field_address0_isptr.
     apply arr_field_compatible0; auto.
     lia.
     }
   deadvars!.
   clear p0 p1 H17 H16 H18 H19 sh'' H15.
   destruct H20.
   forward.
   forward.
   assert (Zlength (bytes_of_string x) = len) by (rewrite Zlength_bytes_of_string; auto).
   assert (i < len). {
     clear - H10 H14.
    destruct (len - i) eqn:?H; try lia.
    subst s. simpl in H14.
    exfalso. clear - H14. forget (Z.to_nat i) as j.
    revert j H14; induction x; destruct j; simpl; intros; try discriminate; eauto.
   }
   rewrite upd_Znth_app2 by list_solve.
   autorewrite with sublist.
   replace (len + pad_length - i) with (1 + (len + pad_length - (i+1))) by lia.
   rewrite <- Zrepeat_app by lia.
   rewrite upd_Znth_app1 by list_solve.
   change (upd_Znth 0 _ ?a) with ([a]).
   rewrite app_assoc.
   replace [Vint (Int.zero_ext _ _)] with (map Vubyte (sublist i (i+1) (bytes_of_string x))).
 2:{ rewrite sublist_one; try lia. 
     clear - H17 H18 H10 H14. subst s.
     unfold Vubyte, bytes_of_string.
     simpl. f_equal. f_equal.
     pose proof substring_sublist i (len-i) x ltac:(lia) ltac:(lia).
     rewrite H14 in H; clear H14.
     replace (i + (len - i)) with len in H by lia.
     assert (Znth 0 (sublist i len (bytes_of_string x)) = 
             Znth 0 (bytes_of_string (String ch r))) by congruence.
     rewrite Znth_sublist in H0 by lia.
     rewrite Z.add_0_l in H0. unfold bytes_of_string in H0.
     rewrite H0; clear H0.
     unfold list_byte_of_string, list_ascii_of_string. simpl.
     rewrite Znth_0_cons.
     replace (Ascii.N_of_ascii ch) with (Byte.to_N (Ascii.byte_of_ascii ch)).
       2:{ apply Byte.to_of_N. symmetry; apply Ascii.byte_of_ascii_via_N. }
     clear.
     forget (Ascii.byte_of_ascii ch) as b.
     pose proof (Byte.to_N_bounded b).
     rewrite Byte.unsigned_repr by rep_lia.
     rewrite zero_ext_inrange; auto.
     rewrite Int.unsigned_repr by rep_lia.
     simpl. lia.
    }
   rewrite <- map_app. rewrite sublist_rejoin by lia.
   forward_call (g',outlier,v,(ch,r)).
   Intros vret; destruct vret as [[p0 p1] sh'']. simpl snd in *; simpl fst in *.
   assert_PROP (is_pointer_or_integer (rep_type_val g' p0)). {
    sep_apply modus_ponens_wand. unfold full_gc. Intros.
    sep_apply (is_pointer_or_integer_rep_type_val g' outlier ch p0). entailer!!.
   }
   assert_PROP (is_pointer_or_integer (rep_type_val g' p1)). {
    sep_apply modus_ponens_wand. unfold full_gc. Intros.
    sep_apply (is_pointer_or_integer_rep_type_val g' outlier r p1). entailer!!.
   }
   forward.
   sep_apply modus_ponens_wand.
   Exists (i+1) p1.
   entailer!!.
   split.
   ++
     replace (substring _ _ _) with r; auto.
     clear - H17 H14 H18 H10.
     pose proof substring_sublist i (Z.of_nat (String.length x)-i) x ltac:(lia) ltac:(lia).
     rewrite H14 in H.
     change (bytes_of_string (String ch r)) 
     with ((Byte.repr oo Z.of_N oo Byte.to_N) (Ascii.byte_of_ascii ch) :: bytes_of_string r) in H.
     rewrite (sublist_split i (i+1)) in H by lia.
     rewrite sublist_one in H by lia.
     simpl in H. inv H.
     replace (i + (_ - i)) with (Z.of_nat (String.length x)) in H2 by lia.
     pose proof substring_sublist (i+1) (Z.of_nat (String.length x)-(i+1)) x ltac:(lia) ltac:(lia).
     set (s := substring _ _ x). fold s in H.
     apply bytes_of_string_inj.
     rewrite H,H2.
     f_equal; lia.
   ++
    unfold field_address0.
     rewrite !if_true by auto with field_compatible.
     simpl. rewrite offset_offset_val. f_equal. lia.
   ++ apply derives_refl.
 -- (* else clause *)
  pose proof (string_desc_has_tag_prop s).
  forward.
  destruct s eqn:?H; try (contradiction H12; reflexivity). subst s.
  assert (i=len). { clear - H10 H14. subst len.
     rewrite <- (Z2Nat.id i) by lia. f_equal.
     replace (Z.to_nat ( _ - _)) with (String.length x - (Z.to_nat i))%nat in H14 by lia.
     assert (Z.to_nat i <= String.length x)%nat by lia.
     forget (Z.to_nat i) as j. clear H10 i.
     revert j H14 H; induction x; simpl; intros; try lia.
     destruct j; try discriminate.
     f_equal. apply IHx; auto. lia.
  }
  subst i.
  entailer!!.
  apply derives_refl'; f_equal. 
  replace (len + pad_length - len) with pad_length by lia.
  f_equal. f_equal. f_equal.
  apply sublist_same; try lia.
  clear. rewrite Zlength_bytes_of_string; auto.
* 
 forward_for_simple_bound (pad_length - 1) 
  (EX i, 
   PROP ( )
   LOCAL (temp _argv new0;
   temp _ptr (field_address0 (tarray tuchar (len + pad_length)) [ArraySubsc len] new1); 
   lvar specs_general.___FRAME__ (Tstruct specs_general._stack_frame noattr) v___FRAME__;
   lvar specs_general.___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__;
   gvars gv; temp _pad_length (Vlong (Int64.repr pad_length)))
   SEP (FRZL FR1; graph_rep g';
   data_at sh' (tarray tuchar (len + pad_length)) 
     (app (map Vubyte (bytes_of_string x))
       (app (Zrepeat (Vubyte Integers.Byte.zero) i) (Zrepeat Vundef (pad_length-i)))) new1)).
 -- entailer!!.
    apply derives_refl.
 --
  assert (force_val
   (sem_add_ptr_long tschar (field_address0 (tarray tuchar (len + pad_length)) (SUB len) new1)
      (Vlong (Int64.repr i))) = 
      field_address (tarray tuchar (len + pad_length)) [ArraySubsc (len+i)] new1). {
   rewrite sem_add_pl_ptr_special;
   [ | reflexivity
    | unfold field_address0; rewrite if_true by auto with field_compatible;
       auto with field_compatible].
   simpl. unfold field_address; rewrite if_true by auto with field_compatible. simpl.
   unfold field_address0; rewrite if_true by auto with field_compatible.
   simpl. rewrite offset_offset_val. f_equal. lia.
  }
 forward.
 entailer!!. 
 unfold field_address0. rewrite if_true by auto with field_compatible. simpl.
 destruct FC1 as [HH _]; destruct new1; try contradiction; simpl; auto.
 entailer!!.
 unfold data_at.
 apply derives_refl'. f_equal.
 change (Int.zero_ext _ _) with Int.zero.
 assert (Zlength (bytes_of_string x) = len) by apply Zlength_bytes_of_string.
 rewrite !upd_Znth_app2 by Zlength_solve.
 rewrite !Zlength_map, Zlength_Zrepeat, H12 by lia.
 f_equal.
 replace (len + i - len - i) with 0 by lia.
 replace (pad_length - i) with (1 + (pad_length - (i+1))) by lia.
 rewrite <- !Zrepeat_app by lia.
 rewrite <- !app_assoc.
 f_equal.
 rewrite upd_Znth_app1 by Zlength_solve.
 f_equal.
--
 assert (force_val
   (sem_add_ptr_long tuchar (field_address0 (tarray tuchar (len + pad_length)) (SUB len) new1)
      (Vlong (Int64.repr (pad_length - 1)))) = 
      field_address (tarray tuchar (len + pad_length)) [ArraySubsc (len+(pad_length-1))] new1). {
   rewrite sem_add_pl_ptr_special;
   [ | reflexivity
    | unfold field_address0; rewrite if_true by auto with field_compatible;
       auto with field_compatible].
   simpl. unfold field_address; rewrite if_true by auto with field_compatible. simpl.
   unfold field_address0; rewrite if_true by auto with field_compatible.
   simpl. rewrite offset_offset_val. f_equal. lia.
  }
 forward.
 entailer!!. 
 unfold field_address0. rewrite if_true by auto with field_compatible. simpl.
 destruct FC1 as [HH _]; destruct new1; try contradiction; simpl; auto.
 rewrite upd_Znth_app2
  by (autorewrite with sublist; rewrite Zlength_bytes_of_string; lia).
 rewrite upd_Znth_app2
  by (autorewrite with sublist; rewrite Zlength_bytes_of_string; lia).
 replace (pad_length - (pad_length - 1)) with 1 by lia.
 replace (len + (pad_length - 1) - Zlength (map Vubyte (bytes_of_string x))
           - Zlength (Zrepeat (Vubyte Byte.zero) (pad_length - 1))) 
  with 0
  by (autorewrite with sublist; rewrite Zlength_bytes_of_string; lia).
 change (Zrepeat Vundef 1) with [Vundef].
 rewrite upd_Znth0.
 rewrite Int64.unsigned_repr by rep_lia.
 rewrite <- (map_Zrepeat Vubyte).
 rewrite zero_ext_inrange
   by (rewrite Int.unsigned_repr by rep_lia; really_simplify (two_p 8); lia).
 replace (Vint (Int.repr (pad_length-1))) with (Vubyte (Byte.repr (pad_length-1)))
   by (unfold Vubyte; rewrite Byte.unsigned_repr by rep_lia; auto).
 change [Vubyte ?x] with (map Vubyte [x]).
 rewrite <- !map_app.
 set (bytes := (_ ++ _ ++ _)%list).

 assert (bytes_len: Zlength (bytes_to_words bytes) = n-1). {
    rewrite bytes_to_words_length. unfold n.
    unfold bytes. rewrite !Zlength_app. 
   rewrite Zlength_bytes_of_string.
   rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
   f_equal. autorewrite with sublist. reflexivity.
 }
 thaw FR1.
 unfold full_gc.
 unfold before_gc_thread_info_rep.
 Intros.
 change (Tpointer _ _) with int_or_ptr_type.
 pose (rawf := map (fun i => Some (inl (Int64.unsigned i))) (bytes_to_words bytes) : list raw_field).
 assert (RAWF_LEN: 0 < Zlength rawf < two_p (WORD_SIZE * 8 - 10)). {
   unfold rawf. rewrite Zlength_map, bytes_len.
   clear - LEN PAD. subst n.
   really_simplify (two_p (WORD_SIZE * 8 - 10)).
   rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
   subst pad_length.
   pose proof (Z_div_mod_eq_full len 8).
   replace (len + (8 - len mod 8)) with (8 * (len/8) + (8*1)) by lia.
   rewrite <- Z.mul_add_distr_l.
   rewrite Z.mul_comm, Z.div_mul by lia.
   clearbody len. clear - LEN.
   assert (0 <= len / 8) by (apply Z_div_nonneg_nonneg; lia).
   split. lia.
   match goal with |- _ < ?A => 
     change A with ((A-2) * 8 / 8 + 2)%Z;
     assert (len / 8 <= (A-2)*8/8); [ | lia]
   end.
   apply Z.div_le_mono; try lia.
 }
 assert (JJ: NO_SCAN_TAG <= BYTESTRING_TAG -> ~In None rawf). {
   clear - H7. subst rawf. intros ? ?. list_solve.
 }
 assert (Htag_range: 0 <= BYTESTRING_TAG < 256) by (unfold BYTESTRING_TAG; clear; lia).
 assert (APN: AP_n pp = 1 + Zlength rawf). {
   simpl. unfold rawf. rewrite Zlength_map, bytes_len. lia.
 }
 assert (ANC: add_node_compatible (AP_g pp) (new_copied_v (AP_g pp) 0) []). {
   red; intros. inversion H11.
 }
 assert (EC: edge_compatible (AP_g pp) 0 rawf nil). {
   hnf; intros. simpl; clear. split; try contradiction.
   subst rawf.
   set (j:=O). unfold j at 1. clearbody j.
   revert j; induction (bytes_to_words bytes); intros. contradiction.
   apply IHl in H. auto.
 }
 assert (OUT: incl (List_ext.filter_sum_right (List_ext.filter_option rawf))
     (AP_outlier pp)). {
   simpl. subst rawf. clear.
   intros ? ?. exfalso.
   induction (bytes_to_words bytes); simpl in H; auto.
 }
 pose (ap := Build_alloc_package pp rawf BYTESTRING_TAG Htag_range RAWF_LEN JJ nil APN ANC EC OUT).
 assert (WAND |-- 
         graph_rep (AP_g pp)
          * vertex_at (nth_sh (AP_g pp) 0)
              (vertex_address (AP_newg pp ap) (new_copied_v (AP_g pp) 0))
              (header_new (AP_rvb pp ap))
              (fields_new (AP_newg pp ap) (AP_rvb pp ap) (new_copied_v (AP_g pp) 0)) -*
        full_gc (AP_newg pp ap) t_info3 roots' outlier ti sh gv). {
  unfold WAND. apply allp_left with ap. simpl. fold sh'. cancel.
 }
 sep_apply H11. clear WAND H11.
 simpl AP_g.
 assert (VOFF: vertex_offset g' (new_copied_v g' 0) = used_space (heap_head (ti_heap t_info')) + 1). {
   clear - H4.
   destruct H4 as [? [? [? ? ]]] .
   destruct H0 as [? [? [? ? ]]].
   unfold vertex_offset.
   simpl.
   destruct H0.
   clear - H0.
   unfold nth_gen.
  destruct (heap_head_cons (ti_heap t_info')) as [? [? [? ? ]]].
  rewrite H1. rewrite H in H0.
  pose proof (g_gen_not_nil (graph_model.glabel g')).
  destruct (g_gen (graph_model.glabel g')) eqn:?H; try contradiction.
 inv H0.
  destruct H6 as [_ [_ ? ]].
  simpl.
  rewrite H0. f_equal.
 }
 assert (SSTART: space_start (heap_head (ti_heap t_info')) = gen_start g' 0). {
  clear - H4. destruct H4. clear H. destruct H0 as [[? _]  _].
  destruct (heap_head_cons (ti_heap t_info')) as [? [? [? ? ]]].
  rewrite H1.
  unfold gen_start.
  rewrite if_true by (apply graph_has_gen_O).
  unfold nth_gen.
  pose proof (g_gen_not_nil (graph_model.glabel g')).
  destruct (g_gen (graph_model.glabel g')) eqn:?H; try contradiction.
  simpl.
  destruct H.
  rewrite H3 in *.
  rewrite H0 in *. 
  inv H.
  inv H4.
  destruct H7. auto.
 }
 assert (data_at sh' (tarray int_or_ptr_type 1) [Vlong (Int64.repr ((n - 1) * two_p 10 + BYTESTRING_TAG))] new0
        * field_at sh' (tarray tuchar (len + pad_length)) []  (map Vubyte bytes) new1
    |-- vertex_at (nth_sh g' 0) (vertex_address (AP_newg pp ap) (new_copied_v g' 0))
              (header_new (AP_rvb pp ap))
              (fields_new (AP_newg pp ap) (AP_rvb pp ap) (new_copied_v g' 0))). {
   subst ap. simpl. unfold AP_newg. simpl.
   rewrite add_node_vertex_address_new by apply graph_has_gen_O.
   unfold vertex_address, header_new, fields_new, add_node, make_fields,
       update_vlabel, raw_fields; simpl.
   rewrite if_true by reflexivity. simpl.
   unfold vertex_at. simpl.
   apply sepcon_derives.
   - fold sh'.
    erewrite data_at_singleton_array_eq by reflexivity.
    set (i := ((n - 1) * two_power_pos 10 + BYTESTRING_TAG)).
    replace (BYTESTRING_TAG + 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * Zlength rawf))))))))))
     with i
    by (unfold rawf,i; rewrite Zlength_map, bytes_len;
        really_simplify (two_power_pos 10); lia).
    unfold Z2val.
    replace (Vlong (Int64.repr i)) with (Vptrofs (Ptrofs.repr i))
     by (rewrite Vptrofs_unfold_true, ptrofs_to_int64_repr by reflexivity; auto).
    rewrite VOFF, <- SSTART.
   rewrite data_at_int_or_ptr_int.
   change size_t with tulong.
   unfold Z2val.
   rewrite offset_offset_val.
    rewrite Z.mul_add_distr_l.
     rewrite <- Z.add_assoc.
     change (_*1 + _) with 0.
     rewrite Z.add_0_r.
   apply derives_refl.
 - fold (data_at sh' (tarray tuchar (len + pad_length)) (map Vubyte bytes) new1).
   fold sh'.
   rewrite VOFF, <- SSTART.
   replace (offset_val (WORD_SIZE * (used_space (heap_head (ti_heap t_info')) + 1))
         (space_start (heap_head (ti_heap t_info')))) with new1. 2:{
     unfold new1, new0.
     unfold field_address0; rewrite if_true by auto with field_compatible.
     unfold alloc_at.
     simpl. rewrite offset_offset_val.
     f_equal.
     rewrite Z.mul_add_distr_l; f_equal.
   }
   rewrite Zlength_map, make_fields'_eq_Zlength.
   unfold rawf at 1.
   rewrite Zlength_map, bytes_len.
  unfold n. rewrite Z.add_simpl_r.
  unfold rawf.
  rewrite bytestring_contents_lemma1.
  limited_change_compspecs CompSpecs.
  replace len with (Zlength (bytes_of_string x))
    by (rewrite Zlength_bytes_of_string; lia).
  apply bytestring_array_conversion; rewrite ?Zlength_bytes_of_string; auto.
  clearbody new0.
  clear - FC H7. 
  subst new1. fold len. replace (_ / 8) with (n-1) by lia. clearbody n.
  rewrite (field_compatible_Tarray_split int_or_ptr_type 1) in FC by lia.
  destruct FC; auto.
  unfold bytes. rewrite !Zlength_app, Zlength_bytes_of_string, Zlength_Zrepeat by lia.
  change (Zlength [_]) with 1. lia.
 }
 sep_apply H11; clear H11.
 match goal with |- context [SEPx (?a :: _) ] => 
     assert (Hx: graph_rep g' * a |-- graph_rep g' * a) by apply derives_refl;
     sep_apply Hx; clear Hx;
     set (GG := (graph_rep g' * a)%logic) in *
 end.
 sep_apply modus_ponens_wand.
 clear GG.

 Local Ltac entailer_for_return ::= entailer!!.
 forward.
 unfold ti_heap.
 Exists (repNode (new_copied_v (AP_g pp) 0)) (AP_newg pp ap) roots' t_info3.
 unfold full_gc.
 entailer!!. 
 2: unfold frame_rep_; limited_change_compspecs CompSpecs; entailer!!.
 simpl.
 unfold AP_newg in H11|-*. simpl AP_rvb in H11|-*. simpl AP_fields in H11|-*.
 destruct xs.
 clear new1 FC FC1 H10.
 subst new0. unfold alloc_at. 
 split3.
 ++ split. rewrite <- add_node_graph_has_v by auto. right. reflexivity.
    rewrite add_node_vlabel. split; auto.
    reflexivity.
 ++ eapply gc_graph_iso_trans. apply H5.
    destruct H4 as [[? [? [? ?]]] [[? [? [[? ?] ?]]] [? [[? [? [? ?]]] ? ]]]].
    apply add_node_iso; simpl; auto.
    apply new_node_roots with outlier.
    split; auto.
 ++ unfold vertex_address. rewrite offset_offset_val.
    f_equal.
    ** change 8 with (WORD_SIZE * 1). rewrite <- Z.mul_add_distr_l. f_equal.
       rewrite <- VOFF.
       unfold vertex_offset.
       f_equal.
       symmetry; apply add_node_previous_vertices_size.
       red; simpl; clear; lia. 
    ** rewrite add_node_gen_start by auto. simpl.
       unfold gen_start. rewrite if_true by auto.
       destruct (spaces_g0 _ _ _ _ H4) as [_ [_ [? _ ]]].
       symmetry; auto.
Qed.
