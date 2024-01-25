Require Import VeriFFI.examples.bytestring.prims.
Require Import ZArith.
Require Import Psatz.
Require Import CertiGraph.CertiGC.spatial_gcgraph.

Require Import VeriFFI.examples.bytestring.specs.

Lemma representable_string_max_length:
 (* NOT PROVABLE! *)
  forall (s: string) (g: graph) (p: rep_type),
   is_in_graph g s p ->
   graph_rep g |-- !! (Z.of_nat (String.length s) < Ptrofs.max_unsigned/4).
Admitted.

Lemma allocate_in_nursery_pf {n: Z} {nursery : space}
   (H: 0 <= n <= nursery.(total_space)-nursery.(used_space)) :
  0 <= nursery.(used_space)+n <= nursery.(total_space).
Proof.
intros.
pose proof space_order nursery.
lia.
Qed.

Definition allocate_in_nursery (n: Z) (nursery : space)
   (H: 0 <= n <= nursery.(total_space)-nursery.(used_space)) :=
  {| space_start := nursery.(space_start);
     used_space := nursery.(used_space) + n;
     total_space := nursery.(total_space);
     space_sh := nursery.(space_sh);
     space_order := allocate_in_nursery_pf H;
     space_upper_bound := nursery.(space_upper_bound) |}.

Lemma allocate_in_full_gc_aux:
  forall n nursery H h,
Zlength (allocate_in_nursery n nursery H :: tl (spaces h)) = MAX_SPACES.
Proof.
intros.
pose proof spaces_size h.
destruct (spaces h).
inversion H0.
simpl.
rewrite Zlength_cons in *.
auto.
Qed.

Lemma allocate_in_full_gc :
 forall (n: Z) g t_info roots outlier ti sh gv
  (H: 0 <= n <= headroom t_info),
 full_gc g t_info roots outlier ti sh gv |--
  let nursery := heap_head (ti_heap t_info) in
  let t_info' := {| ti_heap_p := t_info.(ti_heap_p);
                    ti_heap := {| spaces := allocate_in_nursery n nursery H ::
                                      tl (spaces (ti_heap t_info));
                                  spaces_size := allocate_in_full_gc_aux n nursery H _ |};
                    ti_args := t_info.(ti_args);
                    arg_size := t_info.(arg_size);
                    ti_frames := t_info.(ti_frames);
                    ti_nalloc := t_info.(ti_nalloc) |}
 in @data_at_ env_graph_gc.CompSpecs sh (tarray int_or_ptr_type n)
      (offset_val (WORD_SIZE * used_space (heap_head (ti_heap t_info'))) 
       (space_start (heap_head (ti_heap t_info'))))
   * full_gc g t_info' roots outlier ti sh gv.
Proof.
intros.
unfold full_gc.
Intros.
destruct H0 as [? [? ? ] ].
entailer!!.
-
 split3; auto; simpl.
 + admit.
 + destruct H1 as [? [ ? [? ?] ] ].
   split3; [ | | split]; auto.
   admit.
-
  simpl.
  admit.
Admitted.

 Lemma get_tinfo_alloc:
  forall g t_info roots outlier ti sh gv,
  full_gc g t_info roots outlier ti sh gv |--
  @field_at env_graph_gc.CompSpecs sh env_graph_gc.thread_info_type (DOT _alloc) 
       (offset_val (WORD_SIZE * used_space (heap_head (ti_heap t_info)))
             (space_start (heap_head (ti_heap t_info)))) ti
    * (@field_at env_graph_gc.CompSpecs sh env_graph_gc.thread_info_type (DOT _alloc) 
       (offset_val (WORD_SIZE * used_space (heap_head (ti_heap t_info)))
             (space_start (heap_head (ti_heap t_info)))) ti -* 
       full_gc g t_info roots outlier ti sh gv).
Proof.
 intros.
 unfold full_gc.
 Intros.
 rewrite prop_true_andp by auto.
 unfold before_gc_thread_info_rep.
 unfold_data_at (data_at _ _ _ _).
 cancel.
 rewrite <- wand_sepcon_adjoint.
 cancel.
Qed.

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
Fail forward_call. (*
The command has indeed failed with message:
Tactic failure: Your Gprog contains no funspec with the name
_get_Coq_Strings_String_string_tag (level 98).
*)
   admit.
 - change (Tpointer _ _) with int_or_ptr_type.
   forward.
   change (Tpointer _ _) with int_or_ptr_type.
   forward.
   forward.
   deadvars!.
  set (len := Z.of_nat (String.length x)) in *.
  assert (LEN: 0 <= len < Int64.max_unsigned / 4) by rep_lia. clear H2.
  set (pad_length := 8 - len mod 8).
  assert (PAD: 0 < pad_length <= 8) by admit.
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
  rewrite divu_repr64, add64_repr. fold n.
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

 assert (H99: 0 <= n <=
  total_space (heap_head (ti_heap t_info')) - used_space (heap_head (ti_heap t_info'))).
 { clear - H2 H7. unfold headroom in H2. lia. }
 sep_apply (allocate_in_full_gc n g' t_info' roots' outlier ti sh gv H99).
 cbv zeta.
 match goal with |- context [full_gc g' ?A] =>  set (t_info3 := A) end.
 change (ti_fp t_info') with (ti_fp t_info3).
 
 assert (isptr (space_start (heap_head (ti_heap t_info')))) by 
   (eapply space_start_isptr'; eassumption).
 sep_apply get_tinfo_alloc.
 Intros.
 set (JJ :=  _ -* _).
 limited_change_compspecs CompSpecs.
 forward.
 subst JJ.
 set (KK := field_at _ _ _ _ _).
 sep_apply (modus_ponens_wand KK).
 clear KK.
 change (Tpointer _ _) with int_or_ptr_type.
 set (new0 := offset_val _ _).
 assert_PROP (field_compatible0 (tarray int_or_ptr_type n) (SUB 1) new0) as FC by entailer!. 
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
   clear - H7 H9 H10 H99. unfold MAX_SPACE_SIZE in H9. simpl in H9.
   really_simplify Ptrofs.modulus.
   set (tot := total_space _) in *. set (use := used_space _) in *.
   clearbody tot. clearbody use. clearbody n. clear - H7 H9 H10 H99.
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
 2:{ clear - H8 FC.
     simpl in new0.
     set (s := space_start _) in *.
     subst new0 new1.
     clearbody s. destruct s; try contradiction.
     unfold field_address0.
     rewrite if_true; auto.
 }
 freeze FR1 := - (data_at_ sh (tarray tuchar (len + pad_length)) new1).
 assert (FC1: field_compatible (tarray tuchar (len + pad_length)) nil new1). {   
   destruct new0; generalize FC; intros [HH _]; try contradiction HH.
   subst new1.
   unfold field_address0.
   rewrite if_true; auto. simpl. 
   clear - FC LEN PAD H9.
   destruct FC as [? [? [? [? [?  ?] ] ] ] ].
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

Definition bytes_of_string (s: string) : list Integers.Byte.int :=
  map (Integers.Byte.repr oo Z.of_N oo Strings.Byte.to_N) (list_byte_of_string s).

(* assert_PROP (FC1: field_compatible0 (tarray int_or_ptr_type n)*)
 forward_loop 
  (EX i, EX v: rep_type, 
   PROP (0 <= i <= len; is_in_graph g' (substring (Z.to_nat i) (String.length x) x) v)
   LOCAL (temp _temp (rep_type_val g' v); 
          temp _ptr (field_address0 (tarray tuchar (len+pad_length)) (SUB i) new1);
          temp _argv new0;
   temp specs_general._nalloc (Vlong (Int64.repr n));
   lvar specs_general.___FRAME__ (Tstruct specs_general._stack_frame noattr) v___FRAME__;
   lvar specs_general.___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__;
   temp specs_general._tinfo ti; gvars gv; temp _pad_length (Vlong (Int64.repr pad_length)))
   SEP (FRZL FR1; 
        data_at sh (tarray tuchar (len+pad_length)) 
            (app (map Vbyte (sublist 0 i (bytes_of_string x))) (Zrepeat Vundef (len+pad_length-i)))
            new1))
  break: 
   (PROP ()
   LOCAL (temp _temp (rep_type_val g' v0'); 
          temp _ptr (field_address0 (tarray tuchar (len+pad_length)) (SUB len) new1);
          temp _argv new0;
   temp specs_general._nalloc (Vlong (Int64.repr n));
   lvar specs_general.___FRAME__ (Tstruct specs_general._stack_frame noattr) v___FRAME__;
   lvar specs_general.___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__;
   temp specs_general._tinfo ti; gvars gv; temp _pad_length (Vlong (Int64.repr pad_length)))
   SEP (FRZL FR1; 
        data_at sh (tarray tuchar (len+pad_length)) 
            (app (map Vbyte (bytes_of_string x)) (Zrepeat Vundef pad_length)) new1)).
* Exists 0. Exists v0'. change (Z.to_nat 0) with O.
  rewrite (proj1 (prefix_correct x x))
    by (clear; induction x; simpl; auto; rewrite if_true; auto).
 entailer!!.
  --
   rewrite arr_field_address0; try lia; auto.
   destruct FC1 as [HH _]. simpl. apply isptr_offset_val_zero; auto. 
 --
   simpl app. apply derives_refl.
* 
  Intros i v.
Fail forward_call. (*
The command has indeed failed with message:
Tactic failure: Your Gprog contains no funspec with the name
_get_Coq_Strings_String_string_tag (level 98).
*)
   admit.
* 
 forward_for_simple_bound (pad_length - 1) 
  (EX i, 
   PROP ( )
   LOCAL (temp _temp (rep_type_val g' v0');
   temp _ptr (field_address0 (tarray tuchar (len + pad_length)) [ArraySubsc len] new1); 
   temp _argv new0; temp specs_general._nalloc (Vlong (Int64.repr n));
   lvar specs_general.___FRAME__ (Tstruct specs_general._stack_frame noattr) v___FRAME__;
   lvar specs_general.___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__;
   temp specs_general._tinfo ti; gvars gv; temp _pad_length (Vlong (Int64.repr pad_length)))
   SEP (FRZL FR1;
   data_at sh (tarray tuchar (len + pad_length)) 
     (app (map Vbyte (bytes_of_string x))
       (app (Zrepeat (Vbyte Integers.Byte.zero) i) (Zrepeat Vundef (pad_length-i)))) new1)).
 -- entailer!!.
    apply derives_refl'. f_equal.
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
 assert (Zlength (bytes_of_string x) = len). {
   unfold bytes_of_string.
   admit.
  }
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
 thaw FR1.
 unfold full_gc.
 unfold before_gc_thread_info_rep.
 Intros.
 forward.
 change (Tpointer _ _) with int_or_ptr_type.
 replace (force_val (sem_add_ptr_long int_or_ptr_type new0 (Vlong (Int64.repr n))))
  with  (offset_val (WORD_SIZE * used_space (heap_head (ti_heap t_info3)))
        (space_start (heap_head (ti_heap t_info3)))). 2:{
  simpl.
  admit.
  }
 sep_apply (before_gc_thread_info_rep_fold sh t_info3 ti).
 sep_apply (full_gc_fold gv g' t_info3 roots' outlier ti sh).
 Local Ltac entailer_for_return ::= entailer!!.
 forward.
 unfold ti_heap.
 assert (ING: exists g3: graph, exists x': rep_type,
  full_gc g' t_info3 roots' outlier ti sh gv  
 * data_at sh (tarray int_or_ptr_type 1) [Vlong (Int64.repr ((n - 1) * two_p 10 + 252))] new0
 * field_at sh (tarray tuchar (len + pad_length)) []
      (upd_Znth (len + (pad_length - 1))
         (map Vbyte (bytes_of_string x) ++
          Zrepeat (Vbyte Byte.zero) (pad_length - 1) ++
          Zrepeat Vundef (pad_length - (pad_length - 1)))%list
         (Vint (Int.zero_ext 8 (Int.repr (pad_length - 1))))) new1
 |-- full_gc g3 t_info3 roots' outlier ti sh gv 
   && !! (is_in_graph g3 (model_fn Bytestring_Proofs.pack_desc (x; xs)) x'
          /\ gc_graph_iso g roots g3 roots')).
   admit.
 destruct ING as [g3 [x' ING] ].
 sep_apply ING.
 Exists x' g3 roots' t_info3.
 entailer!!.
 ++ admit.
 ++
 unfold frame_rep_.
 limited_change_compspecs CompSpecs.
 cancel.
+ clear - LEN PAD.
  revert LEN; really_simplify Int64.max_unsigned; intros. simpl in LEN. lia.
+ rep_lia.

all: fail.
 
Abort.
