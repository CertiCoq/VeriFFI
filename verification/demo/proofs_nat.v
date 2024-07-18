(** * Proofs for nat 

Contains 
- a proof that make_nat_0 satisfies its specification 
- a proof that add_node preserves the nat_in_graph predicate. TODO: Shouldn't this be a consequence of isomorphism?

*) 

From VeriFFI Require Export specs proofs_library.


(** ** Proof that make_nat_0 satisfies its specification *)

Print f_alloc_make_Coq_Init_Datatypes_nat_S. 

(** ** General f_alloc *) 

Definition rec_assign (offset : Z) _arg := 
(Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
              (Econst_int (Int.repr offset) tint) (tptr tulong)) tulong)
          (Etempvar _arg tulong)).


Definition rest (n: Z) :=  (Ssequence
            (Ssequence
              (Sset _t'1
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _alloc (tptr tulong))
                (Ebinop Oadd (Etempvar _t'1 (tptr tulong))
                  (Econst_int (Int.repr n) tint) (tptr tulong))))
            (Sreturn (Some (Ebinop Oadd (Etempvar _argv (tptr tulong))
                             (Econst_int (Int.repr 1) tint) (tptr tulong))))).

Fixpoint rec_code (z : Z) (args : list ident) := 
  match args with 
  | nil => rest z
  | arg :: args' => Ssequence (rec_assign z arg) (rec_code (1 + z) args')
end.


Definition f_alloc_make_general (args: list ident) (tag : Z) := {|
  fn_return := (tptr tulong);
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                map (fun x => (x, tulong)) args );
  fn_vars := nil;
  fn_temps := ((_argv, (tptr tulong)) :: (_t'3, (tptr tulong)) ::
               (_t'2, (tptr tulong)) :: (_t'1, (tptr tulong)) :: nil);
  fn_body :=
(Ssequence
  (Sset _argv
    (Efield
      (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _limit (tptr tulong)))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
        (Sifthenelse (Ebinop Olt
                       (Ebinop Osub (Etempvar _t'2 (tptr tulong))
                         (Etempvar _t'3 (tptr tulong)) tlong (* TODO: NOT SURE *) )
                       (Econst_int (Int.repr (2 + Zlength args)) tint) tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
            (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong)
        (Econst_int (Int.repr tag) tint))
        (rec_code 1 args))))
|}.

Hint Unfold f_alloc_make_general rest rec_assign f_alloc_make_Coq_Init_Datatypes_list_cons.


Goal f_alloc_make_general [_arg0; _arg1] 2048 = f_alloc_make_Coq_Init_Datatypes_list_cons. 
Proof. autounfold. reflexivity. Qed. 

Goal f_alloc_make_general [_arg0] 1024 = f_alloc_make_Coq_Init_Datatypes_nat_S. 
Proof. autounfold. reflexivity. Qed. 

Lemma make_nat_O_proof : semax_body Vprog Gprog f_make_Coq_Init_Datatypes_nat_O make_nat_0_spec.
Proof. 
  start_function. 
  forward.
  Exists (repZ 0). entailer!. 
  cbv. intuition (try congruence).
Admitted.

(** ** 2. Proof that
    + apply IHn; eauto. rewrite <- H_p in H0. subst.  add_node preserves the nat_in_graph predicate *) 

(** When there was a node in the old graph, there is also one in the new one. 
TODO: This proof has to be repeated for each file.
I could maybe avoid this with the right signature.

TODO: Shouldn't this be a consequence of the isomorphism? 
Lemma iso_nat_in_graph g g' roots roots' p n :
  nat_in_graph g n p -> In p roots -> gc_graph_iso g (map roots_rep_type roots) g' roots' -> exists p', nat_in_graph g' n p'. 

Lemma add_node_iso roots g to lb es: 
  ~ In (inr (new_copied_v g to)) roots -> gc_graph_iso g roots (add_node g to lb es) roots.

TODO: Do we need p?
*)

Lemma nat_in_graph_has g n v: 
  nat_in_graph g n (repNode v) -> graph_has_v g v. 
Proof. 
  intros H. destruct n; simpl in *.
  - contradiction.  
  - destruct H as (?&?). intuition. 
Qed.
       


(* TODO: In p roots is too strong, it should be reachable. *) 
Lemma iso_nat_in_graph g g' roots roots' p n :
  vertex_valid g -> vertex_valid g' -> nat_in_graph g n p -> In p roots -> gc_graph_iso g (map roots_rep_type roots) g' roots' -> exists p', nat_in_graph g' n p'. 
Proof.
  intros VV VG'. intros.
  destruct H1 as (vmap12&vmap21&emap12&emap21&H11&H12). 
  (* TODO: lift should be a general definition. *) 
  pose (lift p := match p with 
     | repNode v' => repNode (vmap12 v')
     | _ => p
    end).
  exists (lift p).

  (* TODO: In p roots has to be generalized to being reachable from the roots. *) 
  assert ( match p with
                              | repNode v' => path_lemmas.reachable_through_set g (filter_sum_right (map roots_rep_type roots)) v'
                              | _ => True
                              end ).
  { destruct p; eauto. exists v. split. 
            +  rewrite <- filter_sum_right_In_iff. rewrite in_map_iff.  exists (repNode v).
            split; eauto.
            +  apply path_lemmas.reachable_refl. apply VV.  eapply nat_in_graph_has. eauto. } 
  clear H0. 
  revert p H H1.
  (* Induction on the nat *) 
  induction n; intros p H H0; simpl in *; eauto.  
  - destruct p; simpl in *; try contradiction. eauto. 
  - destruct H as (p'&H21&H22). destruct p eqn: H_p; try contradiction. 
    destruct H22 as (_&H22&H23). 
    exists (lift p'). split. 
    + apply IHn; eauto. destruct (vlabel g v) eqn: Hl.
      destruct raw_mark; try contradiction. 
      destruct raw_color; try contradiction. destruct H23 as (?&?&?).
      inversion H2. subst. inversion H6. subst. 
      unfold field_rep. destruct x; eauto. 
      * destruct s; eauto. 
      * simpl.
        eapply path_lemmas.reachable_through_set_step. 
        2 : eapply H0. 
        -- admit. 
        -- eapply out_edges_step. unfold out_edges. 
           admit.
    + simpl. split3; eauto.  
      * assert (vvalid (subgraph2.reachable_sub_labeledgraph g (filter_sum_right (map roots_rep_type roots))) v).
        { simpl. unfold predicate_vvalid. split.  unfold vertex_valid in VV. eapply VV. assumption.
          eauto. } 
        eapply graph_isomorphism.vvalid_bij in H. 2 : eapply H12.
        unfold vertex_valid in *. rewrite <- VG'. 
        simpl in H. unfold predicate_vvalid in H. eapply H.
      * assert (vlabel g v = vlabel g' (vmap12 v)).  
        { assert (vlabel g v = vlabel (subgraph2.reachable_sub_labeledgraph g (filter_sum_right (map roots_rep_type roots))) v) as -> by reflexivity.
          erewrite graph_isomorphism.vlabel_iso. 2 : eapply H12. reflexivity. 
          simpl. unfold predicate_vvalid. split. 
          - apply VV. eauto. 
          - eauto.  }
        rewrite <- H. 
        destruct (vlabel g v); eauto. 
        destruct raw_mark; try contradiction. 
        destruct raw_color; try contradiction. 
        intuition. 
        -- admit. (* ??? *)
        -- inversion H4. subst. inversion H7. subst. 
           constructor. constructor.
           unfold lift. simpl. unfold field_rep. destruct x; try eauto. 
           ++ destruct s; eauto. 
           ++ assert (dst g (copied_vertex, 0%nat) = dst (subgraph2.reachable_sub_labeledgraph g (filter_sum_right (map roots_rep_type roots))) (copied_vertex, 0%nat)) as -> by reflexivity. 
              erewrite graph_isomorphism.dst_bij with (g0 := subgraph2.reachable_sub_labeledgraph _ _ ). 2 : eapply H12. 
              ** simpl. unfold dst.  admit. (* TODO *)  
              ** simpl. unfold predicate_evalid. admit. 
 Admitted.


Lemma add_node_monotone g to lb e n p: 
add_node_compatible g (new_copied_v g to) e -> graph_has_gen g to -> nat_in_graph g n p -> nat_in_graph (add_node g to lb e) n p. 
Proof. 
  intros C G. revert p. induction n; eauto. 
  - intros p (p1&H1&H2). 
    exists p1. split.
    + eauto. 
    + unfold graph_cRep in *. simpl in *. 
      destruct p; eauto. 
      destruct H2 as (_&H21&H22). 
      repeat split; eauto. 
      * rewrite add_node_graph_has_gen; eauto. unfold graph_has_v in H21. apply H21. 
      * unfold graph_has_v in *. destruct H21 as (H211&H212).
        pose (number_of_vertices_increases g (fst v) to lb e G). 
        unfold gen_has_index in *. unfold vgeneration in *. lia. 
      * unfold update_vlabel. 
        if_tac. 
        -- exfalso.  
           destruct H21 as (H211&H212). 
           unfold gen_has_index in H212. 
           unfold new_copied_v in H. 
           unfold Equivalence.equiv in H.
           subst. simpl in H212. lia. 
        -- destruct (vlabel g v). simple_if_tac; eauto. 
           destruct raw_color; eauto. intuition. 
           apply compatible_add_node; eauto. 
Qed.


(** ** 3. Proof of alloc_make_nat_S *)
 
Lemma alloc_make_nat_S_proof : semax_body Vprog Gprog f_alloc_make_Coq_Init_Datatypes_nat_S alloc_make_nat_S_spec.
Proof. 
  start_function.
  unfold thread_info_rep, full_gc, before_gc_thread_info_rep. Intros. rename H0 into gc_cond. 

  (** General properties *) 
  assert (graph_has_gen_0 := graph_has_gen_O g).
  assert (~ In (inr (new_copied_v g 0)) roots) as ROOTS_IN by (eapply new_node_roots; eapply gc_cond). 
  destruct (heap_head_cons (ti_heap t_info)) as (g0&space_rest&SPACE_NONEMPTY&g0_eq). rewrite !g0_eq in *.
  assert (isptr (space_start g0) /\  writable_share (space_sh g0) /\ generation_space_compatible g (0%nat, nth_gen g 0, g0)) as (isptr_g0&wsh_g0&comp_g0) by (subst; eapply spaces_g0; eauto).  
   assert ( 0 <= used_space g0 <= total_space g0) as SP1 by apply space_order. 
   assert (match p with | repNode v => v <> new_copied_v g 0 | _ => True end) as H_uneq. 
   { destruct p; try reflexivity. intros ->. apply nat_in_graph_has in H. 
        eapply graph_has_v_not_eq; eauto. }

   assert (total_space g0 < MAX_SPACE_SIZE) as SP2 by apply space_upper_bound.
   rewrite MAX_SPACE_SIZE_eq in SP2. simpl in SP2.
   remember ( space_start g0) as s0. destruct s0; try contradiction. 

   (** Start of the proof *) 
   do 3 forward. 
   (* GEN: 2 is the number of spaces. *) 
   forward_if  (2 <= total_space g0 - used_space g0).
      { (** First condition if, denote_tc_samebase. *) 
       unfold denote_tc_samebase. cbn. entailer!. }
      { forward_call (1). entailer!. }
      { forward. entailer!.  rename H0 into H_tf. 
        (** Show the condition. *) 
        unfold typed_false, strict_bool_val, tint, force_val, both_int, sem_sub_pp, eq_block, peq in H_tf. simpl in H_tf.
        destruct (Pos.eq_dec b b) eqn:?; try congruence; simpl in *.
        unfold Val.of_bool in H_tf. destruct (Int.lt _ _) eqn:HHH; simpl in *; try congruence. apply lt_false_inv in HHH.
        revert HHH. autorewrite with norm. 

        remember (heap_head (ti_heap t_info)) as g0.
        remember WORD_SIZE as WS. clear HeqWS. 
        assert (WS = 8) by admit. 
        assert (Ptrofs.unsigned i = 0) by admit.
        unfold Ptrofs.divs, Ptrofs.sub, Ptrofs.add. autorewrite with norm. 
        rewrite (Ptrofs.signed_repr 8); try rep_lia.
        rewrite !(Ptrofs.unsigned_repr (WS * _)); try rep_lia.  
        rewrite !Ptrofs.unsigned_repr; try rep_lia.  
        assert (Ptrofs.unsigned i + WS * total_space g0 - (Ptrofs.unsigned i + WS * used_space g0) = (total_space g0 -  used_space g0) * WS) as -> by lia.
        rewrite Ptrofs.signed_repr.  
        rewrite H0, Z.quot_mul; try rep_lia.
        autorewrite with norm. lia.
        clear H0. assert (WS = 4) as -> by admit. rep_lia.  }


  (** After the if. *) 
   Intros.
   rewrite !Heqs0 in *.
   remember (offset_val (WORD_SIZE * used_space g0) (space_start g0)) as alloc. 
   remember (offset_val (WORD_SIZE * total_space g0) (space_start g0)) as limit.
   remember (total_space g0 - used_space g0) as space. 

   unfold heap_rest_rep. rewrite SPACE_NONEMPTY. simpl. Intros. 
   unfold space_rest_rep at 1.
   if_tac. 
   { rewrite H1 in isptr_g0. simpl in *. contradiction. }

   rewrite <- Heqalloc. 

   assert (0 <= space) by lia. 
   replace int_or_ptr_type with tulong by admit. (* TODO: CHANGE THE SPECIFICATION. *)
   (* OTHERWISE I CAN'T STEP FORWARD. *) 

   (** Continuing. *) 
   do 5 forward. 

   assert (t_size : 0 <= 2 <= total_space (nth_space t_info 0) - used_space (nth_space t_info 0)). 
    { unfold nth_space. rewrite SPACE_NONEMPTY. simpl. rep_lia. }                      

   pose (v := new_copied_v g 0). 
   Exists (repNode v). 
   assert (R1 : 0 <= 0 < 256) by lia. 
   assert (R2 : 0 < Zlength [rep_field p] < two_power_nat 22) by (unfold two_power_nat; cbn; lia). 
   assert (R3 : NO_SCAN_TAG <= 0 -> ~ In None [rep_field p]). rewrite NO_SCAN_TAG_eq. lia. 
   pose (es := match p with 
               | repNode v' => [((v, Z.to_nat 0), (v, v'))]
               | _ => []
                end). 
    
    Exists (add_node g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es).  

    pose (t_info' := graph_add.add_node_ti 0 t_info _ t_size).
    Exists t_info'. 

    assert (add_node_compatible g (new_copied_v g 0) es).
    { unfold add_node_compatible. intros. subst es. destruct p; inversion H9. 
    - injection H10. intros. subst. simpl.  intuition eauto. 
      + eauto using nat_in_graph_has.
      + rep_lia. 
      + repeat constructor. eauto. 
       - inversion H10. }

    entailer!.
  - split3. 
    + (** In this new graph, we have (S n) at position v with our predicate. *) 
      exists p. intuition (try congruence).  
      * apply add_node_monotone; eauto.  
      * unfold graph_cRep, tag_nat. intuition. 
        -- split.
           ++ rewrite add_node_graph_has_gen; eauto.  
           ++ apply add_node_has_index_new; eauto. 
        -- rewrite add_node_vlabel.  
           simpl. intuition eauto. repeat constructor. 
           destruct p as [| |p_v]; try reflexivity. 
           simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (v, 0%nat)); congruence. 
    + destruct gc_cond. unfold gc_correct.sound_gc_graph, roots_compatible in *. intuition eauto. apply add_node_iso; eauto. 
    + destruct comp_g0 as (C1&C2&C3). 
      simpl. unfold vertex_address, vertex_offset.  
      simpl. f_equal. 
      * rewrite <- C3.
        assert (previous_vertices_size g 0 (number_of_vertices (nth_gen g 0)) = previous_vertices_size (add_node g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es) 0
     (number_of_vertices (nth_gen g 0))) as ->. 
        { unfold previous_vertices_size, vertex_size_accum. unfold vertex_size. 
          apply fold_left_ext. intros. rewrite add_node_vlabel_old. reflexivity. 
          unfold nat_inc_list in H13. unfold new_copied_v. 
          rewrite nat_seq_In_iff in H13. intros A. injection A. rep_lia. }
        assert (WORD_SIZE = 8) as -> by admit; rep_lia. 
      * rewrite add_node_gen_start; eauto. 
        unfold gen_start. if_tac; try contradiction. eauto.
  - unfold full_gc. 
    Intros. entailer!.
    { eapply add_node_gc_condition_prop. eauto. destruct p; intuition (eauto using nat_in_graph_has). eauto. }

    (** Names *) 
    remember (ti_heap t_info) as heap. 
    remember (heap_head heap) as g0.
    remember (offset_val (WORD_SIZE * total_space g0) (space_start g0)) as limit.
    
    unfold before_gc_thread_info_rep. Intros. 
    cancel. 
    unfold heap_rest_rep. simpl. cancel. 
    rewrite !sepcon_assoc. 
    apply sepcon_derives. 
    { apply derives_refl'. f_equal.
      - f_equal. 
        + simpl. f_equal. 
          * rewrite add_node_heap_used_space0. 
            replace WORD_SIZE with 8 by admit. rewrite <- Heqheap. rewrite <- Heqg0. rep_lia. 
          * rewrite add_node_heap_start0. congruence.  
        + f_equal. 
          rewrite add_node_heap_start0. rewrite Heqlimit. 
          rewrite add_node_heap_total0. 
          congruence. 
          }
    { apply sepcon_derives.
      - entailer!. apply derives_refl'. 
        rewrite add_node_heap_start0. rewrite add_node_heap_total0. f_equal. f_equal. 
        f_equal. clear - SPACE_NONEMPTY. 
       destruct t_info. simpl in *. destruct ti_heap; simpl in *. 
       destruct spaces; try congruence. 
       simpl in *. rewrite upd_Znth0. simpl. congruence. 
       (* Should be able to simplify this. *)
    - unfold t_info'. erewrite  add_node_heap_ti_token_rep. 
      2 : { rewrite <- Heqheap, SPACE_NONEMPTY. rewrite Zlength_cons.
            assert (B := Zlength_nonneg space_rest). rep_lia. } 
      cancel. 

    unfold force_val. 
    unfold default_val. simpl.
    
    assert (exists al, Z.to_nat (total_space g0 - used_space g0) = S (S al)) as (al&alloc_succ).  
    {  apply Z_to_nat_monotone in H0. 
       simpl in H0. destruct (Z.to_nat (total_space g0 - used_space g0)) as [|[]]; try lia; eauto. }

    rewrite alloc_succ.
    simpl. 
    rewrite upd_Znth0.  
    rewrite (upd_Znth_app2 [Vlong (Int64.repr 1024)] (Vundef :: list_repeat al Vundef)). 
    2 : { pose (Zlength_nonneg (Vundef :: list_repeat al Vundef)). 
          unfold Zlength in *.  simpl. simpl in l. lia. }
    simpl. rewrite upd_Znth0.
    erewrite add_node_spatial; auto.
    unfold sem_add_ptr_long, tulong, complete_type.
    unfold thread_info_rep. 

    unfold sem_cast_l2l.
    assert (exists p_long, rep_type_val g p = Vlong p_long) as (p_long&PLONG) by admit. (* Just because of the sem_cast_l. Will disappear if we have the right type. *)
    rewrite PLONG in *. 
    cancel.
    assert (total_space g0 - used_space g0 = Zlength (Vlong (Int64.repr 1024) :: Vlong p_long :: list_repeat al Vundef)) as AL. 
    { rewrite !Zlength_cons. rewrite Zlength_list_repeat'. rewrite <- !Nat2Z.inj_succ.  rewrite <- alloc_succ. rewrite Z2Nat.id; rep_lia. }
    rewrite AL. 
    assert (Zlength (Vlong (Int64.repr 1024) :: Vlong p_long :: list_repeat al Vundef) = Zlength (Vlong p_long :: list_repeat al Vundef) + 1) as ->. 
    { rewrite !Zlength_cons. rep_lia. }

    rewrite (@data_at_tarray_split_1 (space_sh g0) _ (Tlong Unsigned noattr) _ (Vlong p_long :: list_repeat al Vundef)); eauto.
    rewrite Zlength_cons. unfold Z.succ.
    rewrite data_at_tarray_split_1; eauto.
   rewrite <- sepcon_assoc. rewrite sepcon_comm.
     subst. 
     destruct t_info; simpl in *. destruct ti_heap; simpl in *. destruct spaces; try congruence.
     rewrite upd_Znth0. simpl. cancel. 
     assert (spaces = space_rest) as -> by congruence. 
     cancel. unfold space_rest_rep. if_tac. 
     { simpl in *. exfalso. eauto. } 
     autorewrite with norm. 
     rewrite !Zlength_list_repeat'. simpl. 
     remember (heap_head {| spaces := s :: space_rest; spaces_size := spaces_size |}) as g0. 
     assert (s = g0)  as -> by congruence.  
     assert (total_space g0 - (used_space g0 + 2) = Z.of_nat al).
     { rewrite !Zlength_cons in AL. rewrite Zlength_list_repeat' in AL. rep_lia. }
     rewrite H14. rewrite sepcon_comm.  
     apply sepcon_derives. 
     + assert (int_or_ptr_type = Tlong Unsigned noattr) as -> by admit. 
       assert (WORD_SIZE * used_space g0 + 8 + 8 = WORD_SIZE * (used_space g0 + 2)) as ->. 
       { assert (WORD_SIZE = 8) as -> by admit. rep_lia. }
       entailer!. 
      +  unfold vertex_at. rewrite sepcon_comm. apply cancel1_last. 
           --  (* Address *)
             rewrite WORD_SIZE_eq. 
             rewrite add_node_vertex_address_new; eauto. simpl. 
             eapply derives_refl'.
             assert (offset_val (4 * used_space g0) (space_start g0) = offset_val (-4) (vertex_address g (new_copied_v g 0))) as ->.
             {  unfold vertex_address. destruct comp_g0 as (C1&C2&C3). unfold gen_start.   simpl. if_tac; try contradiction. 
                rewrite <- C1. rewrite offset_offset_val. f_equal. 
                unfold vertex_offset. simpl. rep_lia.  }
             unfold header_new. simpl. destruct comp_g0 as (comp_start&comp_sh&comp_prev).
             rewrite <- comp_sh. simpl. 
             (* TODO: Problem of different types *) admit. 
           -- unfold es. destruct p eqn: Hp; simpl in *; try congruence. 
              ++ subst. entailer!. admit. (*  entailer!.  *) 
              ++ entailer!. 
                 simpl. unfold fields_new. simpl. rewrite  add_node_vertex_address_new; eauto. 
                 unfold make_fields. simpl. unfold raw_fields. simpl.  
                 unfold update_vlabel. if_tac; try congruence. simpl. 
                 rewrite Zlength_cons. 
                 assert (Z.succ (Zlength (@nil val)) = Zlength (@nil val) + 1) as -> by rep_lia. 
                 replace (env_graph_gc.CompSpecs) with CompSpecs by admit. (* CompSpecs problem *) 
                 rewrite (data_at_tarray_split_1 (nth_sh g 0)).
                 rewrite data_at_zero_array_eq. entailer!.
                 all: eauto. 
                 ** destruct comp_g0 as (comp_start&comp_sh&comp_prev).
             rewrite <- comp_sh. rewrite PLONG. 
             (* Again a type problem. *) 
             admit. 
             ** admit. 
             ++ (* TODO: SAME AS ABOVE *) admit. 
     + unfold gc_condition_prop in *. intuition eauto.
     + unfold copied_vertex_existence. unfold gc_condition_prop in *. 
       intuition eauto. unfold gc_correct.sound_gc_graph in *.
       unfold src_edge in *.
Admitted. 
