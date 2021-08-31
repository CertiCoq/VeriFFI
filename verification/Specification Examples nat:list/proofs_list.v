(** * Proofs for list

Contains 
- a proof that make_nat_nil satisfies its specification 
- a proof that add_node preserves the list_in_graph predicate. TODO: Shouldn't this be a consequence of isomorphism?

*) 

From VC Require Export specs proofs_library.

(** ** Lists *)
  
Lemma list_in_graph_has (X : Type) (X_in_graph : graph -> X -> rep_type -> Prop) g xs v: 
  list_in_graph X_in_graph g xs (repNode v) -> graph_has_v g v. 
Proof. 
  destruct xs; intros H; simpl in *.
  - contradiction.  
  - destruct H as (?&?&?). intuition. 
Qed.
       
(* TODO: In p roots is too strong, it should be reachable. *) 
(* Lemma iso_nat_in_graph g g' roots roots' p n :
  vertex_valid g -> vertex_valid g' -> nat_in_graph g n p -> In p roots -> gc_graph_iso g (map roots_rep_type roots) g' roots' -> exists p', nat_in_graph g' n p'.  *)
  (* TODO: CHANGE WHEN THE OTHER PROOF IS READY. *) 


(* TODO: I could have lemmas for each constructor. *) 

Lemma add_node_monotone_list  (X_rep : representable_X) g to lb e n p: 
 add_node_compatible g (new_copied_v g to) e -> graph_has_gen g to -> list_in_graph (X_in_graph X_rep) g n p -> list_in_graph (X_in_graph X_rep) (add_node g to lb e) n p. 
Proof. 
  intros C G. revert p. induction n; eauto. (* Number of cases depends. *)
  - intros p (p1&p2&H1&H2&H3). (* TODO: MORE TO SEPARATE, exists. *) 
    exists p1. exists p2. 
    repeat split; eauto using X_monotone, graph_cRep_add_node.
Qed.

Lemma in_valid_RepNode_list (X : representable_X) g xs p_xs: 
  list_in_graph (specs.X_in_graph X) g xs p_xs -> valid_repNode g p_xs.
Proof. 
  intros H. 
  destruct p_xs; try reflexivity. intros ->.
   apply list_in_graph_has in H. 
    eapply graph_has_v_not_eq; eauto. 
Qed.

(* TODO: GENERALIZE *) 
Lemma list_in_graph_cons:
  forall (g : graph) (p_x : rep_type) (X : representable_X) (x : X_type X) (p_xs : rep_type) (xs : list (X_type X)),
    graph_has_gen g 0 ->
    forall (R1 : 0 <= 0 < 256)
      (R2 : 0 < Zlength [rep_field p_x; rep_field p_xs] < two_power_nat 22)
      (R3 : NO_SCAN_TAG <= 0 -> ~ In None [rep_field p_x; rep_field p_xs]),
      list_in_graph (X_in_graph X)
                    (add_node g 0 (newRaw (new_copied_v g 0) 0 [rep_field p_x; rep_field p_xs] R1 R2 R3)
                              (get_fields g 0 [p_x; p_xs] 0)) (x :: xs) (repNode (new_copied_v g 0)).
Proof.
  intros g p_x X x p_xs xs graph_has_gen_0 R1 R2 R3.
  exists p_x, p_xs. (* CHANGED *) intuition (try congruence).
  * (* TODO: REQUIRE MONOTONICITY RESULT IN THE ASSUMPTIONS *) admit.
  * eauto using add_node_monotone_list. admit. (* CHANGED: One for each. Generate respective hints. *)   
  * unfold graph_cRep, tag_list. (* CHANGED to tag_list *) intuition eauto. 
    -- split.
       ++ rewrite add_node_graph_has_gen; eauto.  
       ++ apply add_node_has_index_new; eauto. 
    -- rewrite add_node_vlabel. 
       simpl. intuition eauto. repeat constructor. 
       ++ (* CHANGED: Now two things *) (* subst es. *) 
         destruct p_xs as [| |v_xs]; try reflexivity. simpl. 
         destruct p_x as [| |v_x]; try reflexivity. (* TODO: CHANGED *) 
         ** simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (new_copied_v g 0, 1%nat)); congruence. 
         ** simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (new_copied_v g 0, 1%nat)); congruence. 
         ** simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (new_copied_v g 0, 1%nat)); congruence. 
       ++ (* CHANGED: Now two things *)  
         destruct p_x as [| |v_x]; try reflexivity. 
         destruct p_xs as [| |v_xs]; try reflexivity. 
         ** simpl. unfold updateEdgeFunc. destruct EquivDec.equiv_dec; try congruence. 
         ** simpl. unfold updateEdgeFunc. destruct EquivDec.equiv_dec; congruence. 
         ** simpl. unfold updateEdgeFunc. destruct EquivDec.equiv_dec; try congruence.  
            destruct EquivDec.equiv_dec; congruence. 
Admitted.
   

(** ** 3. Proof of alloc_make_list_cons *)


(* Ltac start_function :=
 leaf_function;
 match goal with |- semax_body _ _ ?F ?spec =>
   let D := constr:(type_of_function F) in 
   let S := constr:(type_of_funspec (snd spec)) in
   let D := eval hnf in D in let D := eval simpl in D in 
   let S := eval hnf in S in let S := eval simpl in S in 
   tryif (unify D S) then idtac else
   tryif function_types_compatible D S 
   then idtac "Warning: the function-body parameter/return types are not identical to the funspec types, although they are compatible:
Function body:" D "
Function spec:" S
   else
   (fail "Function signature (param types, return type) from function-body does not match function signature from funspec
Function body: " D "
Function spec: " S);
   check_normalized F
 end;
 match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH _: globals
               PRE  [] main_pre _ nil _
               POST [ tint ] _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (NDmk_funspec _ _ _ ?Pre _)) =>
   match Pre with
   | (fun x => match _ with (a,b) => _ end) => intros Espec DependedTypeList [a b]
   | (fun i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 clear DependedTypeList;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of;
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP;
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH
                 | Share.t => intros ?SH
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax;
 lazymatch goal with 
 | |- semax ?Delta (PROPx _ (LOCALx ?L _)) _ _ => check_parameter_vals Delta L
 | _ => idtac
 end;
 try match goal with DS := @abbreviate (PTree.t funspec) PTree.Leaf |- _ =>
     clearbody DS
 end;
 start_function_hint. *) 


Lemma alloc_make_list_cons_proof : semax_body Vprog Gprog f_alloc_make_Coq_Init_Datatypes_list_cons alloc_make_list_cons_spec.
Proof.
  start_function.
  unfold thread_info_rep, full_gc, before_gc_thread_info_rep. Intros. 
  destruct args as (graph_X_var&(x&xs)).

  rename H into in_x. rename H0 into in_xs. rename H1 into gc_cond. (* CHANGED: names *) 
  pose (fds := [rep_field p_x; rep_field p_xs]). 
   assert (R1 : 0 <= 0 < 256) by lia. 
  assert (R3 : NO_SCAN_TAG <= 0 -> ~ In None fds). rewrite NO_SCAN_TAG_eq. lia. 
  assert (R2 : 0 < Zlength fds < two_power_pos 54) by (unfold two_power_pos; cbn; lia). 
  assert (H_uneq_x := in_valid_RepNode_X graph_X_var g x p_x in_x). 
  assert (H_uneq_xs := in_valid_RepNode_list _ g xs p_xs in_xs). 
  
  (** General properties *) 
  assert (graph_has_gen_0 := graph_has_gen_O g).
  assert (~ In (inr (new_copied_v g 0)) roots) as ROOTS_IN by (eapply new_node_roots; eapply gc_cond). 
  destruct (heap_head_cons (ti_heap t_info)) as (g0&space_rest&SPACE_NONEMPTY&g0_eq). rewrite !g0_eq in *.
  assert (isptr (space_start g0) /\  writable_share (space_sh g0) /\ generation_space_compatible g (0%nat, nth_gen g 0, g0)) as (isptr_g0&wsh_g0&comp_g0) by (subst; eapply spaces_g0; eauto).  
   assert ( 0 <= used_space g0 <= total_space g0) as SP1 by apply space_order. 
   
   assert (total_space g0 < MAX_SPACE_SIZE) as SP2 by apply space_upper_bound.
   remember ( space_start g0) as s0. destruct s0; try contradiction. 

   (** Start of the proof *)  do 3 forward. 
   forward_if  (1 + Zlength fds <= total_space g0 - used_space g0).
   { (** First condition if, denote_tc_samebase. *) 
     unfold denote_tc_samebase. cbn. entailer!. }
   { (* forward_call (1). entailer!. *) admit. }
   { forward. entailer!. 
     Check Zlength_space.
     eapply Zlength_space; subst fds; eauto. simpl. rep_lia. }

   (** After the if. *) 
   Intros. rename H into space_cond. unfold fds in space_cond. cbn in space_cond. 
   rewrite !Heqs0 in *.   

   unfold heap_rest_rep. rewrite SPACE_NONEMPTY. simpl. Intros. unfold space_rest_rep at 1.
   if_tac. 
   { eauto.  rewrite H in isptr_g0. simpl in *. contradiction. }

   assert (0 <= total_space g0 - used_space g0) by lia.
   replace int_or_ptr_type with tulong by admit.  (* TODO: Typing problem int_or_ptr_type/tulong. *)  
  
   repeat forward. 

   assert (t_size : 0 <= 1 + Zlength fds <= total_space (nth_space t_info 0) - used_space (nth_space t_info 0)).  
   { unfold nth_space. rewrite SPACE_NONEMPTY. simpl in *. rep_lia. }                      

   pose (v := new_copied_v g 0). Exists (repNode v). 
   pose (es := get_fields g 0 [p_x; p_xs] 0).
   Exists (add_node g 0 (newRaw v 0 fds R1 R2 R3) es).

   Exists (graph_add.add_node_ti 0 t_info _ t_size). 
   assert (add_node_compatible g (new_copied_v g 0) es) by (apply get_fields_add_node_compatible).                   

   entailer!.
  - split3. 
    + Print list_in_graph_cons. apply list_in_graph_cons; eauto. 
    + destruct gc_cond. unfold gc_correct.sound_gc_graph, roots_compatible in *. intuition eauto. apply add_node_iso; eauto. 
    + eapply offset_val_rep_type_val; eauto. 
  - unfold full_gc. 
    Intros. entailer!.
    { unfold fds. Check add_node_gc_condition_prop. (* TODO : NEEDS TO BE EXTENDED TO SEVERAL fields. *)

      (* eapply add_node_gc_condition_prop. eauto. destruct p; eauto using nat_in_graph_has. eauto. *) (* CHANGE *)
    admit. }

    (** Names *) 
    remember (ti_heap t_info) as heap. 
    remember (heap_head heap) as g0.
    remember (offset_val (WORD_SIZE * total_space g0) (space_start g0)) as limit.
    
    unfold before_gc_thread_info_rep. Intros. 
    cancel. autorewrite with graph_add. 
    unfold heap_rest_rep. simpl. cancel. 
    cancel_left. 
    { autorewrite with graph_add. apply derives_refl'. unfold WORD_SIZE.
      rewrite <- Heqheap, <-Heqg0. 
      repeat (try eauto; try congruence; try rep_lia; try f_equal). }
    autorewrite with graph_add. cancel_left. 
    + entailer!. rewrite SPACE_NONEMPTY at 1. updater. entailer!. 
    + cancel. unfold force_val, default_val. simpl. 
    
    assert (exists al, Z.to_nat (total_space g0 - used_space g0) = (1 + length fds + al)%nat) as (al&alloc_succ).  (* TODO: CHANGE *) 
    {  apply Z_to_nat_monotone in space_cond. 
       simpl in space_cond. unfold fds. simpl. destruct (Z.to_nat (total_space g0 - used_space g0)) as [|[|[]]]; try lia; eauto. (* CHANGEDpattern *) }
    rewrite alloc_succ. simpl. 

    updater. 
    erewrite add_node_spatial; auto.

    cancel. 
    rewrite <- Heqheap at 1.  rewrite SPACE_NONEMPTY at 1. updater. cancel. 

    rewrite !data_at_tarray_split_1'; eauto. 
    2, 3, 4 :  try rewrite !Zlength_cons; try rewrite !Zlength_list_repeat'; unfold fds in alloc_succ; simpl in alloc_succ; try rep_lia.
 
    rewrite !offset_offset_val. simpl.  
    unfold space_rest_rep. if_tac. 
    { simpl in *. exfalso. rewrite <- Heqheap in H14. rewrite SPACE_NONEMPTY in H14. eauto. } 

    simpl. rewrite <- !Heqheap. rewrite !SPACE_NONEMPTY. simpl. 
     rewrite (sepcon_comm _ (vertex_at _ _ _ _)). cancel_right. 
    2 : {  assert (int_or_ptr_type = tulong) as -> by admit. (* TODO: Typing problem int_or_ptr_type/tulong. But this direction should be possible. *) 
          unfold WORD_SIZE.
          assert (total_space g0 - used_space g0 - 1 - 1 - 1 = total_space g0 - (used_space g0 + 3)) as -> by rep_lia. 
          (* assert (8 * used_space g0 + 8 + 8 + 8 = 8 * (used_space g0 + 3)) as ->; try entailer!. *) 
          (* rep_lia. *) admit. 
    }

    unfold vertex_at. cancel_left. 
      --  simpl. 
        eapply derives_refl'. 
        erewrite space_start_vertex_address_header; eauto.
        unfold header_new. simpl.
        destruct comp_g0 as (comp_start&comp_sh&comp_prev). rewrite <- comp_sh.  
        change_compspecs CompSpecs.
        autorewrite with graph_add; eauto.
      -- autorewrite with graph_add; eauto. 
         change_compspecs CompSpecs.
                                                    
          unfold fields_new. simpl. unfold make_fields.
          rewrite add_node_vlabel, make_fields'_eq. simpl.
          rewrite !Zlength_cons. simpl. 
          rewrite !data_at_tarray_split_1'; eauto. 
          autorewrite with norm. simpl. 
          cancel_left. 
          ++ erewrite comp_space_sh_rew; eauto.
             assert (rep_type_val g p_x = field2val (add_node g 0 (newRaw v 0 fds R1 R2 R3) es)
           (adapt (rep_field p_x) (new_copied_v g 0) 0)) as <-. 
             { destruct p_x; try reflexivity. 
               simpl. erewrite add_node_dst_new; eauto. 
               3 : { unfold es. simpl. eauto. }
               2: { apply NoDup_get_fields. }
               autorewrite with graph_add; eauto. (* TODO *) admit. } 
             erewrite space_start_data; eauto.
             eapply data_at_int_or_ptr_ptr. eauto.

          ++ auto. (* TODO: All missing is the wrong type of data_at. *)
             rewrite data_at_zero_array_eq; eauto.
             autorewrite with norm.
             unfold generation_space_compatible in *.
             eapply data_at_int_or_ptr_ptr'; eauto with graph_add.
             ** erewrite comp_space_sh_rew; eauto.
             ** unfold adapt. destruct p_xs; try reflexivity.
                simpl. erewrite add_node_dst_new; eauto.
                     3 : { unfold es.  simpl. destruct p_x; eauto. admit. (* THERE IS SOMETHING WRONG eauto. *) admit. admit. }
               2: { apply NoDup_get_fields. }
               autorewrite with graph_add; eauto. (* TODO *) admit.
            ** erewrite <- space_start_data; eauto. 
               now rewrite !offset_offset_val.
            ** erewrite <- space_start_data; eauto. 
    -- unfold gc_condition_prop in *. intuition eauto.
    -- unfold gc_condition_prop in *. intuition eauto.
       unfold copy_compatible in H32. unfold copied_vertex_existence.
       admit. (* TODO: Does it suffice if I have this condition? *)
    +  rewrite <- Heqheap. rewrite SPACE_NONEMPTY.
       assert (HHH := Zlength_nonneg space_rest).
       updater. rewrite Zlength_cons. rep_lia.
       Unshelve.
       {  econstructor. admit. admit. }

Admitted. 
