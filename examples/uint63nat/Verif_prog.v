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

Set Nested Proofs Allowed. (* from proofs_library_general.v *)
Lemma add_node_gc_condition_prop g p t_info roots outlier R1 R2 R3 t_size (H: graph_has_gen g 0) :
  let v := new_copied_v g 0 in
  let es :=  match p with
             | repNode v' => [(v, Z.to_nat 0, (v, v'))]
             | _ => []
             end : list (VType * nat * (VType * VType)) in
  let g' := add_node g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es in
  let t_info' := add_node_ti 0 t_info 2 t_size in
  match p with
  | repNode v' => graph_has_v g v' /\ v <> v'
  | _ => True
  end
->
gc_condition_prop g t_info roots outlier -> gc_condition_prop g' t_info' roots outlier.
Proof.
  intros. unfold gc_condition_prop in *. unfold g'.
  assert ( add_node_compatible g (new_copied_v g 0) es).
  { unfold add_node_compatible. intros. subst es. destruct p; inversion H2.
    - injection H3. intros. subst. simpl. intuition.
      repeat constructor. simpl. eauto.
    - inversion H3. }
  assert (  edge_compatible g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es).
  { unfold edge_compatible. intros. simpl. destruct p; simpl; intuition eauto. }
    intuition.
  all: eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_thread_compatible, add_node_ti_size_spec, add_node_roots_compatible.
  + eapply add_node_ti_size_spec; eauto.  rewrite spaces_size.   rep_lia.
  + eapply add_node_outlier_compatible; eauto. (* Print rep_field. *)  simpl.
    destruct p eqn:Hp; hnf; simpl; intros; try contradiction; eauto.
    destruct H12; try contradiction; subst.
    (* TODO: Not sure what to do with this outlier. *)
    unfold outlier_compatible in H9.
    admit. (* THIS IS WEIRD. Should probably not be right. Or is it a problem that I allow things which are not nodes? *)
Admitted.

Lemma body_alloc_make_Coq_Init_Datatypes_nat_S :
  semax_body Vprog Gprog
             f_alloc_make_Coq_Init_Datatypes_nat_S
             alloc_make_Coq_Init_Datatypes_nat_S_spec.
Proof.
  unfold alloc_make_Coq_Init_Datatypes_nat_S_spec.
  unfold alloc_make_spec_general.
  start_function.
  assert (2 <= headroom t_info) by lia.
  clear H1.
  rename H0 into HEADROOM.
  unfold headroom in HEADROOM.
  assert (t_size: 0 <= 2 <= total_space (nth_space t_info 0) - used_space (nth_space t_info 0)). {
    pose proof heap_head_cons.
    destruct (heap_head_cons (ti_heap t_info)) as [s [l [H8 H9 ] ] ].
    unfold nth_space.
       rewrite H8 in *; subst s; simpl; lia.
  }
  unfold full_gc, before_gc_thread_info_rep. Intros.
  rename H0 into gc_cond.

  progress change_compspecs CompSpecs.

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
   forward.
   forward.
   forward.
   forward.
   forward.
   
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
    { unfold add_node_compatible. intros. subst es. destruct p; inversion H10.
    - injection H11. intros. subst. simpl.  intuition eauto.
      + eauto using has_v.
      + rep_lia.
      + repeat constructor. eauto.
       - inversion H11. }

    entailer!.
  - split3.
    + (** In this new graph, we have (S n) at position v with our predicate. *)
      exists p. 
      change (is_in_graph (add_node g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es) x p /\
       graph_cRep (add_node g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es) (repNode v) (boxed 0 1) [p]).

       intuition (try congruence).
      * apply (@is_monotone _ Rep_nat); eauto.
      * unfold graph_cRep. intuition.
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
          unfold GCGraph.nat_inc_list in H12. unfold new_copied_v.
          rewrite nat_seq_In_iff in H12. intros A. injection A. rep_lia. }
        assert (WORD_SIZE = 8) as -> by reflexivity; rep_lia.
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

    change_compspecs CompSpecs.
    unfold heap_rest_rep.
    simpl. cancel.
    rewrite !sepcon_assoc.
    apply sepcon_derives.
    { apply derives_refl'. f_equal.
      - f_equal.
        + simpl. f_equal.
          * rewrite add_node_heap_used_space0.
            replace WORD_SIZE with 8 by reflexivity.
            rewrite <- Heqheap. rewrite <- Heqg0. rep_lia.
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
    replace (upd_Znth _ _ _) with
       (Vlong (Int64.repr 1024) :: rep_type_val g p :: Zrepeat Vundef (total_space g0 - used_space g0 - 2))
       by list_solve.
    erewrite add_node_spatial; auto.
     2: admit.
     2: admit.
    replace (upd_Znth 0 _ _)
    with (add_node_space 0 (nth 0 (spaces (ti_heap t_info)) null_space) 2 t_size
            :: space_rest).
    2:{ subst heap. rewrite upd_Znth0_old by list_solve. f_equal. 
          rewrite SPACE_NONEMPTY. list_solve.
     }
     simpl. cancel.
     change (field_at ?x ?y nil) with (data_at x y).
     change (?a :: ?b :: ?c) with ([a;b]++c).
     rewrite (split2_data_at_Tarray_app 2) by list_solve.
     unfold space_rest_rep. if_tac.
     { simpl in H12. contradiction H0. rewrite <- H12.
       rewrite Heqg0. rewrite Heqheap.
        admit. (* easy *)
     }
   simpl space_sh.
   change_compspecs CompSpecs.
   replace (nth 0 (spaces (ti_heap t_info)) null_space) with g0 by admit.
   replace (total_space (add_node_space 0 (nth 0 (spaces (ti_heap t_info)) null_space) 2 t_size))
       with (total_space g0) by admit.
   replace (used_space (add_node_space 0 (nth 0 (spaces (ti_heap t_info)) null_space) 2 t_size))
     with (used_space g0 + 2) by admit.
   replace (space_sh (nth 0 (spaces (ti_heap t_info)) null_space)) with (space_sh g0) by admit.
   rewrite Z.sub_add_distr.
   replace (space_start (add_node_space 0 (nth 0 (spaces (ti_heap t_info)) null_space) 2 t_size))
       with (space_start g0) by admit.
   replace (field_address0 (tarray int_or_ptr_type (total_space g0 - used_space g0)) 
     (SUB 2) (offset_val (WORD_SIZE * used_space g0) (space_start g0)))
     with (offset_val (WORD_SIZE * (used_space g0 + 2)) (space_start g0)).

2:{ unfold field_address0. simpl. rewrite if_true by auto with field_compatible.
    rewrite offset_offset_val.
      f_equal. change WORD_SIZE with 8. lia.
   }
   cancel.

(* DONE TO HERE, SORT OF *)
   unfold spatial_gcgraph.vertex_at.

   Search data_at data_at_.
   rewrite <- data_at__tarray.
   rewrite sepcon_comm. apply sepcon_derives.
clear.
{
Set Printing Implicit.
 apply derives_refl.
   cancel.
   
Search 
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
