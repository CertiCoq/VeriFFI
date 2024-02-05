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
       sum of geometric series *)

Definition MAX_LEN := MAX_WORDS_IN_GRAPH/3.
    (* because each char in string is represented by a "String" constructor of 3 words
       (including header).  You might (erroneously) think that each one also needs
       an "Ascii" constructor of 9 words (including header), but in fact they can all
       share the same character *)


Lemma representable_string_max_length:
 (* PROVABLE! but not easy.  Rely on the fact that every node in the graph
   must exist in some generation, and the total of all generation sizes is  
   bounded. *)
  forall (s: string) (g: graph) (p: rep_type),
   is_in_graph g s p ->
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

Lemma body_bump_allocptr:
  semax_body Vprog Gprog f_bump_allocptr bump_allocptr_spec.
Proof.
start_function.
unfold full_gc, before_gc_thread_info_rep.
Intros.
limited_change_compspecs CompSpecs.
destruct (spaces_g0 _ _ _ _ H) as [? [? ?] ].
forward.
forward.
forward.
set (tinfo := AP_ti pp) in *.
unfold full_gc, before_gc_thread_info_rep.
limited_change_compspecs CompSpecs.
simpl ti_args. simpl ti_heap_p. simpl ti_frames.
(*rewrite prop_true_andp by (simpl; split; auto).*)
set (hh := heap_head (ti_heap tinfo)).
set (hh' := heap_head _).
simpl.
rewrite !sepcon_assoc.
change (total_space (heap_head (ti_heap tinfo))) with (total_space hh).
change (space_start (heap_head (ti_heap tinfo))) with (space_start hh).
change (ti_fp (bump_alloc _)) with (ti_fp tinfo).
change (used_space (heap_head (ti_heap tinfo))) with (used_space hh).
set (FRAMES := frames_rep _ _). clearbody FRAMES.
set (OUTLIER := outlier_rep outlier); clearbody OUTLIER.
change 8 with WORD_SIZE.
rewrite <- Z.mul_add_distr_l.
unfold heap_rest_rep.
subst hh hh'.
clear H6 H5 H3.
unfold alloc_at.
assert (HEADROOM := AP_enough pp).
unfold headroom in HEADROOM.
simpl spaces.
destruct (heap_head_cons (ti_heap tinfo)) as [nursery [rest [? ?] ] ].
fold tinfo.
change (iter_sepcon.iter_sepcon (?A :: ?B) ?F) with
  (sepcon (F A) (iter_sepcon.iter_sepcon B F)).
unfold allocate_in_nursery.
set (EN := AP_enough pp). clearbody EN.
unfold space_rest_rep at 2.
simpl space_start.
rewrite if_false
  by (intro Hx; rewrite Hx in H0; contradiction H0).
simpl used_space. simpl total_space. simpl space_sh.
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
saturate_local. clear H6.
fold tinfo in HEADROOM; rewrite H5 in HEADROOM.
rewrite (split2_data_at__Tarray_app n K) by lia.
rewrite <- !sepcon_assoc.
limited_change_compspecs CompSpecs.
cancel.
change (@data_at_ env_graph_gc.CompSpecs (space_sh nursery) (tarray int_or_ptr_type n)
      (offset_val (WORD_SIZE * used_space nursery) (space_start nursery)))
 with (@data_at_ CompSpecs (space_sh nursery) (tarray int_or_ptr_type n)
      (offset_val (WORD_SIZE * used_space nursery) (space_start nursery))).
assert (Hsh: nth_sh (AP_g pp) 0 = space_sh nursery). {
  destruct H as [_ [? _  ] ].
  destruct H as [? _ ].
  red in H. 
  rewrite H3 in H.
  destruct H2 as [_ [? _  ] ].
  unfold nth_sh. rewrite H2. rewrite H5. auto.
 }
rewrite Hsh.
pull_left (data_at_ (space_sh nursery) (tarray int_or_ptr_type n)
      (offset_val (WORD_SIZE * used_space nursery) (space_start nursery))).
rewrite !sepcon_assoc.
apply sepcon_derives.
rewrite H5. auto.
apply allp_right; intro ap.
apply -> wand_sepcon_adjoint.
rewrite andp_comm, prop_true_andp.
-
limited_change_compspecs CompSpecs.
subst nursery.
set (nursery := heap_head (ti_heap tinfo)) in *.
set (TT1 := ti_token_rep _ _).
set (TT2 := ti_token_rep _ _).
assert (TT2 = TT1) as ->. {
 subst TT2; subst TT1.
 unfold ti_token_rep; simpl.
 f_equal.
 rewrite H3.
 simpl. f_equal.
}
clearbody TT1.
rewrite Vptrofs_unfold_true by reflexivity.
set (DA := data_at _ _ _ _). clearbody DA.
rewrite Z.sub_add_distr.
fold K.
rewrite H3.
simpl tl.
cancel.
rewrite !sepcon_assoc.
apply sepcon_derives.
+
apply derives_refl'; f_equal.
unfold field_address0.
rewrite if_true by auto with field_compatible.
simpl. change 8%Z with WORD_SIZE.
rewrite offset_offset_val. f_equal. lia.
+
unfold AP_newg.

destruct H.
destruct H as [? [? [? ? ] ] ].
destruct H5.
rewrite <- Hsh.
rewrite add_node_spatial; simpl; auto.
apply graph_has_gen_O.
admit.
admit.
-
destruct H as [? [? [? [? ?] ] ] ].
admit.
Admitted.


Definition bytes_of_string (s: string) : list Integers.Byte.int :=
  map (Integers.Byte.repr oo Z.of_N oo Strings.Byte.to_N) (list_byte_of_string s).

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


Fixpoint bytes_to_words (bl: list byte) : list Int64.int :=
 match bl with
 | b0 :: b1 :: b2 :: b3 :: b4 ::b5 :: b6 :: b7 :: b' =>
     Int64.repr (fold_left (fun i b => i*256+Byte.unsigned b) 
                  ((if Archi.big_endian then (@id (list byte)) else (@rev byte))
                  [b0;b1;b2;b3;b4;b5;b6;b7]) 0) 
     :: bytes_to_words b'
 | _ => nil
 end.

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
Lemma bytestring_contents_lemma1:
  forall g g' bytes, map (field2val g) 
       (make_fields' (map (fun i : int64 => Some (inl (Int64.unsigned i))) (bytes_to_words bytes))
             g' 0) = 
    map Vlong (bytes_to_words bytes).
Admitted.
Lemma bytestring_array_conversion:
 forall {CS: compspecs} sh (x: list byte) pad_length bytes p,
  field_compatible (tarray int_or_ptr_type ((Zlength x + pad_length) / 8)) [] p ->
  pad_length = 8 - (Zlength x) mod 8 ->
  Zlength bytes = Zlength x + pad_length -> 
 data_at sh (tarray tuchar (Zlength x + pad_length)) (map Vubyte bytes) p
 |-- data_at sh (tarray int_or_ptr_type ((Zlength x + pad_length) / 8))
        (map Vlong (bytes_to_words bytes)) p.
Admitted.


Lemma body_pack:
  semax_body Vprog Gprog f_pack pack_spec.
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
 sep_apply (representable_string_max_length x g p); auto.
 Intros.
 rewrite Int.signed_repr by rep_lia.
 sep_apply_compspecs CompSpecs 
  (frame_rep__fold Tsh v___FRAME__ v___ROOT__ (ti_fp t_info) 1 (Vlong (Int64.repr 0))).
 sep_apply_compspecs CompSpecs (before_gc_thread_info_rep_fold sh t_info ti).
 sep_apply (full_gc_fold gv g t_info roots outlier ti sh).
 forward_loop
   (EX s:string, EX ps: rep_type,
     PROP (Z.of_nat (String.length s) <= Z.of_nat (String.length x);
           is_in_graph g s ps)
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
   forward_call (g,ps,s). cancel.
   forward_if.
   + (* then *)
   destruct s; try discriminate H5.
   forward.
   forward_call (g,ps,(a,s)).
   Intros vret; destruct vret as [ [p0 p1] sh']. simpl snd in *; simpl fst in *.
   assert_PROP (is_pointer_or_integer (rep_type_val g p0)). {
    sep_apply modus_ponens_wand. (* unfold full_gc. Intros.*)
    sep_apply (is_pointer_or_integer_rep_type_val g a p0). entailer!!.
   }
   assert_PROP (is_pointer_or_integer (rep_type_val g p1)). {
    sep_apply modus_ponens_wand. (*unfold full_gc. Intros. *)
    sep_apply (is_pointer_or_integer_rep_type_val g s p1). entailer!!.
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
 assert (HEADROOM: 0 <= n <= headroom t_info'). lia.
 pose (pp := Build_alloc_prepackage g' t_info' n HEADROOM).
 forward_call (gv,roots',sh,ti,outlier,pp).
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
   destruct FC as [? [? [? [? ?] ] ] ].
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
   PROP (0 <= i <= len; is_in_graph g' (substring (Z.to_nat i) (Z.to_nat (len-i)) x) v)
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
   forward_call (g',v,s). simpl AP_g. cancel.
   forward_if; fold len in H12; fold s in H12.
   -- (* then clause *)
       destruct s as [ | ch r] eqn:?H; try discriminate H12.
       abbreviate_semax. deadvars!.
   forward_call (g',v,(ch,r)).
   Intros vret; destruct vret as [ [p0 p1] sh'']. simpl snd in *; simpl fst in *.
   assert_PROP (is_pointer_or_integer (rep_type_val g' p0)). {
    sep_apply modus_ponens_wand. unfold full_gc. Intros.
    sep_apply (is_pointer_or_integer_rep_type_val g' ch  p0). entailer!!.
   }
   assert_PROP (is_pointer_or_integer (rep_type_val g' p1)). {
    sep_apply modus_ponens_wand. unfold full_gc. Intros.
    sep_apply (is_pointer_or_integer_rep_type_val g' r p1). entailer!!.
   }
   forward.
   sep_apply modus_ponens_wand.
   rewrite Znth_0_cons.
   forward_call (g',p0,ch).
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
    elimtype False. clear - H14. forget (Z.to_nat i) as j.
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
   forward_call (g',v,(ch,r)).
   Intros vret; destruct vret as [ [p0 p1] sh'']. simpl snd in *; simpl fst in *.
   assert_PROP (is_pointer_or_integer (rep_type_val g' p0)). {
    sep_apply modus_ponens_wand. unfold full_gc. Intros.
    sep_apply (is_pointer_or_integer_rep_type_val g' ch p0). entailer!!.
   }
   assert_PROP (is_pointer_or_integer (rep_type_val g' p1)). {
    sep_apply modus_ponens_wand. unfold full_gc. Intros.
    sep_apply (is_pointer_or_integer_rep_type_val g' r p1). entailer!!.
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
 assert (JJ: NO_SCAN_TAG <= 252 -> ~In None rawf). {
   clear - H7. subst rawf. intros ? ?. list_solve.
 }
 pose (rvb := Build_raw_vertex_block false (O,O(*wrong *)) rawf 0 252 ltac:(lia) ltac:(lia)
                RAWF_LEN JJ).
 assert (APN: AP_n pp = 1 + Zlength (raw_fields rvb)). {
   simpl. unfold rawf. rewrite Zlength_map, bytes_len. lia.
 }
 assert (ANC: add_node_compatible (AP_g pp) (new_copied_v (AP_g pp) 0) []). {
   red; intros. inversion H11.
 }
 pose (ap := Build_alloc_package pp rvb nil APN ANC).
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
   destruct H4 as [? [? [? ? ] ] ] .
   destruct H0 as [? [? [? ? ] ] ].
   unfold vertex_offset.
   simpl.
   destruct H0.
   clear - H0.
   unfold nth_gen.
  destruct (heap_head_cons (ti_heap t_info')) as [? [? [? ? ] ] ].
  rewrite H1. rewrite H in H0.
  pose proof (g_gen_not_nil (graph_model.glabel g')).
  destruct (g_gen (graph_model.glabel g')) eqn:?H; try contradiction.
 inv H0.
  destruct H6 as [_ [_ ? ] ].
  simpl.
  rewrite H0. f_equal.
 }
 assert (SSTART: space_start (heap_head (ti_heap t_info')) = gen_start g' 0). {
  clear - H4. destruct H4. clear H. destruct H0 as [ [? _]  _].
  destruct (heap_head_cons (ti_heap t_info')) as [? [? [? ? ] ] ].
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
 assert (data_at sh' (tarray int_or_ptr_type 1) [Vlong (Int64.repr ((n - 1) * two_p 10 + 252))] new0
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
    set (i := ((n - 1) * two_power_pos 10 + 252)).
    replace (252 + 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * Zlength rawf))))))))))
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
 clearbody rvb. (* temporary *)
 clear H10 JJ. destruct xs.
 clear new0 new1 FC FC1.
 split3.
 ++
  admit.
 ++ admit.
 ++ unfold alloc_at, vertex_address. rewrite offset_offset_val.
    f_equal.
    ** change 8 with (WORD_SIZE * 1). rewrite <- Z.mul_add_distr_l. f_equal.
       admit.
    ** admit.

Unshelve.

all: fail.
Abort.
