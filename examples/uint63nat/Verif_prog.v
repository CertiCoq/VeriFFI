Require Import VeriFFI.examples.uint63nat.prog.

Require Import ZArith.
Require Import Psatz.

Require Import VeriFFI.verification.specs_general.
Require Import VeriFFI.examples.uint63nat.glue.
Require Import VeriFFI.library.meta.


Require Import VST.floyd.proofauto.
Require Import CertiGraph.CertiGC.GCGraph.

From VeriFFI Require Import library.base_representation.
From VeriFFI Require Import library.meta.
From VeriFFI Require Import verification.graph_add.
From VeriFFI Require Import verification.specs_library.

Definition alloc_make_Coq_Init_Datatypes_nat_S_spec : ident * funspec :=
  DECLARE _alloc_make_Coq_Init_Datatypes_nat_S
          (alloc_make_spec_general (@desc _ S _) 1).

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := [alloc_make_Coq_Init_Datatypes_nat_S_spec].

Lemma intro_prop_through_close_precondition :
  forall {Espec : OracleKind} Delta (p1 : Prop) f ps LS sf c post,
  (p1 -> semax Delta (sepcon (close_precondition f ((PROPx ps LS))) sf) c post) ->
  semax Delta (sepcon (close_precondition f (PROPx (p1 :: ps) LS)) sf) c post.
Proof.
  intros.
  unfold close_precondition in *.
  simpl in *.
  eapply semax_pre with (andp (prop p1)
  (fun rho : environ =>
        ((EX vals : list val,
          !! (map (Map.get (te_of rho)) f = map Some vals /\
              Forall (fun v : val => v <> Vundef) vals) &&
          PROPx ps LS (ge_of rho, vals))
            * sf rho)%logic)).
  2: apply semax_extract_prop; auto.
  clear H.
  intro rho.
  simpl.
  apply andp_left2.
  Intro vals.
  Exists vals.
  unfold PROPx.
  simpl.
  normalize.
  apply andp_right; auto.
  apply prop_right; auto.
Qed.

(* Trying to rewrite with something like: *)
(* Lemma aux : forall P ps, (A' xs' ps' -> P ps') -> (A xs ps -> P ps) *)
Lemma combined_sigT_in_arg :
  forall (A : Type) (P : A -> Type) (T : forall (p : {x : A & P x}), Type),
     (forall (a1 : A) (a2: P a1), T (a1; a2)) -> (forall (p : {x : A & P x}), T p).
Proof. intros A P T f p. destruct p. apply f. Qed.

Lemma separate_sigT_in_arg :
  forall (A : Type) (P : A -> Type) (T : forall (p : {x : A & P x}), Type),
      (forall (p : {x : A & P x}), T p) -> (forall (a1 : A) (a2: P a1), T (a1; a2)).
Proof. auto. Qed.

#[export] Instance CCE1: change_composite_env env_graph_gc.CompSpecs CompSpecs.
make_cs_preserve env_graph_gc.CompSpecs CompSpecs.
Defined.

Ltac concretize_PARAMS :=
lazymatch goal with
| xs: args (ctor_reific _), H0: in_graphs _ (ctor_reific _) ?xs' ?ps  |- _ =>
   constr_eq xs xs';
   repeat (simpl in xs;
   lazymatch type of xs with
   | unit => destruct xs;
        match goal with H: ?a = get_size ?u ?v |- _ =>
             unify a (get_size u v); clear H
        end
   | @sigT _ _ => let x := fresh "x" in destruct xs as [x xs];
                let p := fresh "p" in destruct ps as [ | p ps];
                [solve [contradiction] | ]
   end);
   repeat lazymatch goal with
   |  H: in_graphs _ _ _ (_ :: _) |- _ => destruct H
   |  H: in_graphs _ _ _ ps |- _ => hnf in H; subst ps
   end
   | _ => idtac
end.

Ltac start_function2 ::=
  repeat (simple apply intro_prop_through_close_precondition; intro);
  concretize_PARAMS;
  first
  [ erewrite compute_close_precondition_eq; [  | reflexivity | reflexivity ]
  | rewrite close_precondition_main ].

(** ** Consequences of a Well-Defined Graph *)

Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
(** If outliers/roots are compatible, the roots never contain the next new node.  *)
Lemma new_node_roots g outlier roots:
  roots_compatible g outlier roots -> ~ In (inr (new_copied_v g 0)) roots.
Proof.
  intros (RC1&RC2) A.
  rewrite filter_sum_right_In_iff in A.
  apply (computable_theorems.Forall_forall1 _ _ RC2) in A. -
  apply graph_has_v_not_eq with (to := 0%nat) in A. congruence.
Qed.

(** Properties of the nursery generation according to the heap:
 space_start is a pointer, its share is writable, and it is compatible with the first generation of the graph. *)
Lemma spaces_g0 g t_info roots outlier :
    gc_condition_prop g t_info roots outlier
    -> isptr (space_start (heap_head (ti_heap t_info)))
      /\  writable_share (space_sh (heap_head (ti_heap t_info)))
      /\ generation_space_compatible g (0%nat, nth_gen g 0, heap_head (ti_heap t_info)).
Proof.
   destruct (heap_head_cons (ti_heap t_info)) as (g0&space_rest&SPACE_NONEMPTY&g0_eq). rewrite !g0_eq in *.
  intros gc_cond.
  unfold nth_gen.
  Locate glabel.
    destruct (glabel g) eqn: glabel_g.
    destruct g_gen; try congruence.
    unfold gc_condition_prop in *. destruct gc_cond as (gc1&gc2&gc3&gc4&gc5&gc6&gc7).
    unfold graph_thread_info_compatible in gc6.
    destruct gc6 as (gc61&gc62&gc63).
    simpl in *. rewrite !glabel_g in gc61. simpl in *.
    rewrite !SPACE_NONEMPTY in *.
    apply Forall_inv in gc61. destruct gc61 as (?&?&?).
    destruct g1; simpl in *.
    split3; eauto; congruence.
Qed.


Require Import VST.floyd.functional_base.

Lemma body_alloc_make_Coq_Init_Datatypes_nat_S :
  semax_body Vprog Gprog
             f_alloc_make_Coq_Init_Datatypes_nat_S
             alloc_make_Coq_Init_Datatypes_nat_S_spec.
Proof.
  unfold alloc_make_Coq_Init_Datatypes_nat_S_spec.
  unfold alloc_make_spec_general.
  start_function.
  assert (2 <= headroom t_info) by lia.
  rename H0 into HEADROOM.
  unfold headroom in HEADROOM.
  unfold full_gc, before_gc_thread_info_rep. Intros.
  rename H0 into gc_cond.

  (* change_compspecs CompSpecs. *)

  (** General properties *)
  assert (graph_has_gen_0 := graph_has_gen_O g).
  assert (~ In (inr (new_copied_v g 0)) roots)
    as ROOTS_IN
    by (eapply new_node_roots; eapply gc_cond).

  destruct (heap_head_cons (ti_heap t_info))
    as (g0&space_rest&SPACE_NONEMPTY&g0_eq).
  rewrite !g0_eq in *.
  assert (isptr (space_start g0) /\  writable_share (space_sh g0) /\ generation_space_compatible g (0%nat, nth_gen g 0, g0)) as (isptr_g0&wsh_g0&comp_g0) by (subst; eapply spaces_g0; eauto).
   assert ( 0 <= used_space g0 <= total_space g0) as SP1 by apply space_order.
   assert (match p with | repNode v => v <> new_copied_v g 0 | _ => True end) as H_uneq.
   { destruct p; try reflexivity. intros ->. apply (@has_v nat _) in H.
        eapply graph_has_v_not_eq; eauto. }

   assert (total_space g0 < MAX_SPACE_SIZE) as SP2 by apply space_upper_bound.
   (* rewrite MAX_SPACE_SIZE_eq in SP2. simpl in SP2. *)
   remember ( space_start g0) as s0. destruct s0; try contradiction.


   (*
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
  *)

(** After the if. *)
   Intros.
   rewrite !Heqs0 in *.
   remember (offset_val (WORD_SIZE * used_space g0) (space_start g0)) as alloc.
   remember (offset_val (WORD_SIZE * total_space g0) (space_start g0)) as limit.
   remember (total_space g0 - used_space g0) as space.

   unfold heap_rest_rep. rewrite SPACE_NONEMPTY. simpl. Intros.
   unfold space_rest_rep at 1.
   if_tac.
   { rewrite H0 in isptr_g0. simpl in *. contradiction. }
   rewrite <- Heqalloc.
   assert (0 <= space) by lia.
   change_compspecs CompSpecs.
   do 1 forward.
   assert_PROP (force_val (sem_add_ptr_long tulong alloc (Vlong (Int64.repr 0))) = 
                 field_address (tarray int_or_ptr_type (total_space g0 - used_space g0)) [ArraySubsc 0] alloc). { 
     entailer!.
     rewrite arr_field_address by (auto with field_compatible; rep_lia).
     normalize.
   }
   forward.  (* fails here: 
Tactic failure: unexpected failure in load/store_tac_with_hint. The expression
((tptr tulong) __argv[(0)LL])%expr has type (Tlong Unsigned noattr)
but is expected to have type
(Tpointer Tvoid {| attr_volatile := false; attr_alignas := Some log2_sizeof_pointer |}) (level 996).
*)

   (* originally: do 5 forward. *)
Tactic failure: 
It is not obvious how to move forward here.  One way:
Find a SEP clause of the form [data_at _ _ _ 
?p
] (or field_at, data_at_, field_at_),
then use assert_PROP to prove an equality of the form
(force_val (sem_add_ptr_long tulong alloc (Vlong (Int64.repr 0))) = field_address ?t ?gfs ?p)
or if this does not hold, prove an equality of the form (alloc = field_address ?t ?gfs ?p)
, then try [forward] again. (level 992).



(* stuff copied from https://github.com/CertiCoq/VeriFFI/blob/9f04765f42a5f2f8637503187ff9e3fb9f48782b/verification/demo/proofs_nat_general.v *)
   assert (t_size : 0 <= 2 <= total_space (nth_space t_info 0) - used_space (nth_space t_info 0)).
    { unfold nth_space. rewrite SPACE_NONEMPTY. simpl. admit. }
replace (nth_space t_info 0) with g0 in * by admit.
   Search data_at_ data_at.
   rewrite data_at__eq.


   assert (readable_share (space_sh g0)) by admit.
   forward.

(* in Kathrin's proof, by now we were already at the end of the function body *)
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
      + eauto using has_v.
      + rep_lia.
      + repeat constructor. eauto.
       - inversion H10. }

    entailer!.
  - split3.
    + (** In this new graph, we have (S n) at position v with our predicate. *)
      exists p. intuition (try congruence).
      * apply is_monotone; eauto.
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
    { eapply add_node_gc_condition_prop. eauto. destruct p; intuition (eauto using has_v). eauto. }

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
*)

Admitted.
