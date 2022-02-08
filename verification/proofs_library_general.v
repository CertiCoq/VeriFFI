(** * Proof Library *)

From VeriFFI Require Export verification.specs_general.


(** ** VST Lemmas *)

(** Shows that the composites of glue code and the CertiGraph library are compatible.
    Enables the change_compspecs tactic. *)
Lemma change_composite_env_CertiGraph :
  change_composite_env env_graph_gc.CompSpecs CompSpecs.
Proof.
   make_cs_preserve env_graph_gc.CompSpecs CompSpecs.
Qed.

Lemma change_composite_env_CertiGraph_inv :
  change_composite_env CompSpecs env_graph_gc.CompSpecs .
Proof.
   make_cs_preserve CompSpecs  env_graph_gc.CompSpecs.
Qed.

Lemma field_compatible_tarray_join:
  forall (n n1 : Z) (p : val) (t: type),
    0 <= n1 <= n -> complete_legal_cosu_type t = true ->
    field_compatible (tarray t n1) [] p ->
    field_compatible (tarray t (n - n1)) []
                     (offset_val (sizeof t * n1) p) ->
    field_compatible (tarray t n) [] p.
Proof.
  intros. unfold field_compatible. simpl. (*
  destruct H1 as [? [_ [? [? _ ]]]]?
  destruct H2 as [_ [_ [? [? _]]]]. destruct p; try contradiction. clear H1.
  simpl isptr. inv_int i. unfold size_compatible in *. simpl in H2.
  simpl sizeof in *. rewrite Z.max_r in * by lia. pose proof (Ctypes.sizeof_pos t).
  unfold sizeof in H2. remember (Ctypes.sizeof t) as S. rewrite ptrofs_add_repr in H2.
  rewrite Ptrofs.unsigned_repr in * by rep_lia.
  assert (0 <= ofs + S * n1 <= Ptrofs.max_unsigned). {
    destruct H, H6. split. 2: rep_lia. apply Z.add_nonneg_nonneg. 1: lia.
    apply Z.mul_nonneg_nonneg; lia. }
  rewrite Ptrofs.unsigned_repr in * by assumption.
  assert (forall i, ofs + S * n1 + S * (i - n1) = ofs + S * i). {
    intros. rewrite <- Z.add_assoc. rewrite <- Z.mul_add_distr_l.
    do 2 f_equal. lia. } rewrite H8 in H2. do 4 (split; auto). constructor. intros.
  unfold tarray in *. inversion H4; subst. 1: simpl in H10; inversion H10.
  inversion H5; subst. 1: simpl in H10; inversion H10. unfold sizeof in *.
  remember (Ctypes.sizeof t) as S. rewrite ptrofs_add_repr in H15.
  rewrite Ptrofs.unsigned_repr in * by rep_lia.
  assert (0 <= i < n1 \/ n1 <= i < n) by lia. destruct H10.
  1: apply H14; assumption. assert (0 <= i - n1 < n - n1) by lia.
  specialize (H15 _ H11). rewrite H8 in H15. assumption.
Qed. *)
Admitted.

Lemma data_at_tarray_fold: forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    complete_legal_cosu_type t = true ->
    data_at sh (tarray t n1) v1 p *
    data_at sh (tarray t (n - n1)) v2 (offset_val (sizeof t * n1) p) |--
            data_at sh (tarray t n) v p.
Proof.
  intros. rewrite (split2_data_at_Tarray sh t n n1 v v' v1 v2);
            [|assumption..]. entailer!. unfold field_address0. rewrite if_true.
  - simpl nested_field_offset. entailer!.
  - pose proof (field_compatible_tarray_join n _ p _ H H4 H5 H7). clear -H1 H.
    red in H1. red. simpl in *. intuition.
Qed.

Lemma data_at_tarray_unfold: forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    data_at sh (tarray t n) v p |--
            data_at sh (tarray t n1) v1 p *
    data_at sh (tarray t (n - n1)) v2 (offset_val (sizeof t * n1) p).
Proof.
  intros. sep_apply (data_at_local_facts sh (tarray t n) v p).
  Intros. rewrite (split2_data_at_Tarray sh t n n1 v v' v1 v2);
            [|assumption..]. cancel. unfold field_address0. rewrite if_true.
  - simpl nested_field_offset. entailer!.
  - clear -H H4. red. red in H4. simpl in *. intuition.
Qed.

Lemma data_at_tarray_split: forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    complete_legal_cosu_type t = true ->
    data_at sh (tarray t n) v p =
    (data_at sh (tarray t n1) v1 p *
    data_at sh (tarray t (n - n1)) v2 (offset_val (sizeof t * n1) p))%logic.
Proof.
  intros. apply pred_ext.
  - apply data_at_tarray_unfold with v'; assumption.
  - apply data_at_tarray_fold with v'; assumption.
Qed.

(** Splitting up of arrays.

Probably can use:
split2_data_at_Tarray_app
 *)
Lemma data_at_tarray_split_1:
  forall sh p (tt: type) (v: reptype tt) (l: list (reptype tt)),
    complete_legal_cosu_type tt = true ->
    (data_at sh (tarray tt (Zlength l + 1)) (v :: l) p =
    data_at sh tt v p *
    data_at sh (tarray tt (Zlength l)) l (offset_val (sizeof tt) p))%logic.
Proof.
    intros.
  rewrite (data_at_tarray_split sh (Zlength l + 1) 1 p tt (v :: l) (v :: l) [v] l).
  - replace (sizeof tt * 1)%Z with (sizeof tt) by lia.
    replace (Zlength l + 1 - 1) with (Zlength l) by lia. f_equal.
    rewrite (data_at_singleton_array_eq _ tt v); reflexivity.
  - rep_lia.
  - rewrite Zlength_cons. lia.
  - autorewrite with sublist; reflexivity.
  - simpl. vm_compute. reflexivity.
  - simpl. rewrite sublist_1_cons.
    replace (Zlength l + 1 - 1) with (Zlength l) by lia.
    autorewrite with sublist. reflexivity.
  - assumption.
Qed.



Lemma data_at_tarray_split_1':
  forall sh p (tt: type) (v: reptype tt) (l: list (reptype tt)) n,
    complete_legal_cosu_type tt = true ->
    n = Zlength l + 1 ->
    (data_at sh (tarray tt n) (v :: l) p =
    data_at sh tt v p *
    data_at sh (tarray tt (n-1)) l (offset_val (sizeof tt) p))%logic.
Proof.
  intros. subst.
  rewrite data_at_tarray_split_1; eauto.
  now rewrite Z.add_simpl_r.
Qed.


(** ** Conversions *)

(** Conversion of the representation type to roots. *)
Definition roots_rep_type (p : rep_type) : root_t :=
match p with
  | repZ z => inl (inl z)
  | repOut p => inl (inr p)
  | repNode v => (inr v)
end.

(** Number of arguments of a cRep *)
Definition cRep_args (ts : cRep) : N :=
  match ts with
  | enum _ => 0
  | boxed t n => n
end.


(** ** Consequences of a Well-Defined Graph *)

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

(** Equation for the header *)
Lemma space_start_vertex_address_header (g : graph) (graph_has_gen_0 : graph_has_gen g 0) (g0 : space):
  generation_space_compatible g (0%nat, nth_gen g 0, g0) ->
  offset_val (8 * used_space g0) (space_start g0) = offset_val (-8) (vertex_address g (new_copied_v g 0)).
Proof.
  intros (C1&C2&C3).
  unfold vertex_address, gen_start.
  simpl. if_tac; try contradiction.
  rewrite <- C1, offset_offset_val. f_equal.
  unfold vertex_offset. simpl. rewrite C3.
  unfold WORD_SIZE. rep_lia.
Qed.

Lemma space_start_data (g : graph) (graph_has_gen_0 : graph_has_gen g 0) (g0 : space) :
  generation_space_compatible g (0%nat, nth_gen g 0, g0) ->
  (offset_val (WORD_SIZE * used_space g0 + 8) (space_start g0)) = (vertex_address g (new_copied_v g 0)).
Proof.
  intros(C1&C2&C3).
  unfold vertex_address, gen_start.
  simpl. if_tac; try contradiction.
  rewrite <- C1.
  unfold vertex_offset. simpl. rewrite C3.
  unfold WORD_SIZE. f_equal. rep_lia.
Qed.

Lemma comp_space_sh_rew g g0 :
  generation_space_compatible g (0%nat, nth_gen g 0, g0) -> space_sh g0 = nth_sh g 0.
Proof.
  intros (H1&H2&H3). eauto.
Qed.

(** ** Stability with add_node *)

(** graph_cRep is stable with add_node,
    as long as to is a valid generation and the new edges are well-defined.  *)
Lemma graph_cRep_add_node g to lb e p ts ps :
  add_node_compatible g (new_copied_v g to) e
   -> graph_has_gen g to
   -> graph_cRep g p ts ps
   -> graph_cRep (add_node g to lb e) p ts ps.
Proof.
  intros C G H3.
  unfold graph_cRep in *. simpl in *.
  destruct p; eauto. destruct ts; eauto.
  destruct H3 as (H11&(H211&H212)&H22).
  repeat split; eauto.
  * rewrite add_node_graph_has_gen; eauto.
  * unfold graph_has_v in *.
    pose (number_of_vertices_increases g (fst v) to lb e G).
    unfold gen_has_index, vgeneration in *. lia.
  * unfold update_vlabel.
    if_tac.
    -- exfalso.
       unfold gen_has_index in H212.
       unfold new_copied_v, Equivalence.equiv in H.
       subst. simpl in H212. lia.
    -- destruct (vlabel g v). simple_if_tac; eauto.
       destruct raw_color; eauto. intuition.
Qed.


(** ** Lemmas Specific to the Proof *)

Hint Rewrite add_node_heap_used_space0 : add.

Lemma Zlength_space (fds : list raw_field) (L : 2 + Zlength fds <= Int.max_signed) (t_info : GCGraph.thread_info)  (b : block) (i : ptrofs):
    total_space (heap_head (ti_heap t_info)) < MAX_SPACE_SIZE ->
  0 <= used_space (heap_head (ti_heap t_info)) <= total_space (heap_head (ti_heap t_info)) ->
  typed_false tint
              (force_val
                 (both_long (fun n1 n2 : int64 => Some (Val.of_bool (Int64.lt n1 n2))) sem_cast_pointer
                            (sem_cast_i2l Signed)
                            (force_val
                               (sem_sub_pp tulong
                                           (Vptr b (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * total_space (heap_head (ti_heap t_info))))))
                                           (Vptr b (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * used_space (heap_head (ti_heap t_info))))))))
                            (vint (2 + Zlength fds)))) ->

  1 + Zlength fds <=
  total_space (heap_head (ti_heap t_info)) - used_space (heap_head (ti_heap t_info)).
Proof.
  intros SP2 SP1 H_tf.
  (** Show the condition. *)
  unfold typed_false, strict_bool_val, tint, force_val, both_int, sem_sub_pp, eq_block, peq in H_tf. simpl in H_tf.
  destruct (Pos.eq_dec b b) eqn:?; try congruence; simpl in *.
  unfold Val.of_bool in H_tf.  inversion H_tf. destruct (Int64.lt _ _) eqn:HHH; simpl in *; try congruence.
  remember (heap_head (ti_heap t_info)) as g0. unfold WORD_SIZE in *.
  revert HHH. autorewrite with norm.
  unfold Ptrofs.divs, Ptrofs.sub, Ptrofs.add. autorewrite with norm.
    rewrite (Ptrofs.signed_repr 8); try rep_lia.
    rewrite !(Ptrofs.unsigned_repr (8 * _)); try rep_lia.
    rewrite !Ptrofs.unsigned_repr; try rep_lia.
    (* assert (Ptrofs.unsigned i + 8 * total_space g0 - (Ptrofs.unsigned i + 8 * used_space g0) = (total_space g0 -  used_space g0) * 8) as -> by lia.
   rewrite Ptrofs.signed_repr.
   rewrite  Z.quot_mul; try rep_lia.
   intros HH. apply lt64_repr_false in HH. rep_lia.
   all: admit. (* TODO *) *)
Admitted.



(* TODO *)

(** ** Fields *)

(** Function to create fields *)
Fixpoint get_fields g to (xs : list rep_type) (n: nat) :=
  let v := new_copied_v g to in
  match xs with
  | nil => nil
  | cons x xs => match x with
                | repNode v_x => ((v, n), (v, v_x) ) :: get_fields g to xs (1 + n)
                | _ => get_fields g to xs (1 + n)
                end
  end.


(** TODO: How to ensure anything? *)
Lemma get_fields_add_node_compatible :
  forall xs (g : graph) n,
    add_node_compatible g (new_copied_v g 0) (get_fields g 0 xs n).
Proof.
  intros xs g. (* unfold add_node_compatible. TODO: No_dup is already provable here. *)
  induction xs; unfold add_node_compatible in *; intros; simpl in *; try contradiction.
  destruct a eqn:H_a.
  - specialize (IHxs _ _ _ _ H). intuition eauto.
  - specialize (IHxs _ _ _ _ H). intuition eauto.
  - simpl in H. destruct H as [H|H].
    + injection H. intros. subst. clear H. simpl. split3; try eauto.
      split3; try eauto.
      * (* TODO : HOW *) admit.
      * rep_lia.
      *


      admit.
    + specialize (IHxs _ _ _ _ H). intuition eauto.
      admit. (* NO DUP ARGUMENT *)
Admitted.

Lemma add_node_previous_vertice_size g r es :
  previous_vertices_size g 0 (number_of_vertices (nth_gen g 0)) = previous_vertices_size (add_node g 0 r es) 0
                                                                                                   (number_of_vertices (nth_gen g 0)).
Proof.
  unfold previous_vertices_size, vertex_size_accum. unfold vertex_size.
      apply fold_left_ext. intros. rewrite add_node_vlabel_old. reflexivity.
      unfold nat_inc_list in *. unfold new_copied_v.
      rewrite nat_seq_In_iff in *. intros A. injection A. rep_lia.
Qed.

Lemma offset_val_rep_type_val (g: graph) (t_info : GCGraph.thread_info) (graph_has_gen_0 : graph_has_gen g 0):
    generation_space_compatible g (0%nat, nth_gen g 0, heap_head (ti_heap t_info)) ->
    forall (es : list (VType * nat * (VType * VType))) (r : raw_vertex_block),
      offset_val (WORD_SIZE * used_space (heap_head (ti_heap t_info)) + sizeof tulong) (space_start (heap_head (ti_heap t_info)))
      = rep_type_val (add_node g 0 r es) (repNode (new_copied_v g 0)).
Proof.
  intros (C1&C2&C3) es r.
  simpl. unfold vertex_address, vertex_offset.
  simpl. f_equal.
  * unfold WORD_SIZE. rewrite <- C3.
    rewrite <- add_node_previous_vertice_size.
    rep_lia.
  * rewrite add_node_gen_start; eauto.
    unfold gen_start. if_tac; try contradiction. eauto.
Qed.


(** Tactics *)
Ltac cancel_left := try rewrite !sepcon_assoc; apply sepcon_derives.
Ltac cancel_right := try rewrite <- !sepcon_assoc; apply sepcon_derives.
Ltac updater := repeat (try rewrite !upd_Znth0; try (rewrite upd_Znth_cons; [|rep_lia]); simpl).

Hint Rewrite @upd_Znth0 : lists.
Hint Rewrite comp_space_sh_rew : graph_add.

(** Reducible variant of make_fields'. *)
Definition adapt (l_raw : raw_field) (v : VType) (n : nat) :=
  match l_raw with
  | Some (inl z) => inl (inl z)
  | Some (inr ptr) => inl (inr ptr)
  | None  => inr (v, n)
  end.

Fixpoint make_fields_red (l_raw : list raw_field) v n :=
  match l_raw with
  | [] => []
  | raw :: l => adapt raw v n :: make_fields_red l v (n +1)%nat
  end.

Lemma make_fields'_eq :
  forall l_raw v n, make_fields' l_raw v n = make_fields_red l_raw v n.
Proof.
  intros l_raw. induction l_raw; intros; eauto.
  simpl. unfold adapt. rewrite IHl_raw. destruct a; try reflexivity.
  destruct s; try reflexivity.
Qed.

(** get_fields alweay selivers something without duplicates. *)
Lemma NoDup_get_fields (g : graph) (xs : list rep_type) (n : nat):
  NoDup (map fst (get_fields g 0 xs n)).
Proof.
  revert n. induction xs; intros; eauto.
  - simpl. constructor.
  - simpl. destruct a; eauto.
    simpl.  constructor; eauto.
    clear.
    enough (forall m, (n < m)%nat -> ~In (new_copied_v g 0, n) (map fst (get_fields g 0 xs m))) by eauto.
    { revert n. induction xs; intros; eauto.
      simpl. destruct a; eauto. simpl. intros [|].
      - injection H0. rep_lia.
      - eapply IHxs; try eapply H0. eauto.
    }
Qed.


Definition valid_repNode (g : graph) p_x:=
match p_x with | repNode v => v <> new_copied_v g 0 | _ => True end.

(* Lemma in_valid_RepNode_X (X : representable_X) g x p_x: *)
(*   X_in_graph X g x p_x -> valid_repNode g p_x. *)
(* Proof. *)
(*   intros H. *)
(*   destruct p_x; try reflexivity. intros ->. *)
(* Admitted. *)

(* TOOD: WHAT ARE THE PRECONDITIONS
   TODO: GENERALIZE TO OTHER VERSION WITH NOT ONLY ONE REP_FIELD
 *)

Lemma add_node_gc_condition_prop_general g ps t t_info roots outlier R1 R2 R3 t_size (H: graph_has_gen g 0) :
  let v := new_copied_v g 0 in
  let es :=  get_fields g 0 ps 0 : list (VType * nat * (VType * VType)) in
  let g' := add_node g 0 (newRaw v (Z.of_nat t) (map rep_field ps) R1 R2 R3) es in
  let t_info' := add_node_ti 0 t_info (1 + Zlength (map rep_field ps)) t_size in
  Forall (fun p => match p with
  | repNode v' => graph_has_v g v' /\ v <> v'
  | _ => True
  end) ps
  ->
gc_condition_prop g t_info roots outlier -> gc_condition_prop g' t_info' roots outlier.
Proof.
  intros. unfold gc_condition_prop in *. unfold g'.
  assert ( add_node_compatible g (new_copied_v g 0) es).
  { unfold add_node_compatible. intros. subst es.
    revert H2. generalize (0)%nat at 2 5.
    clear - H0 H1.
    induction ps; intros; eauto.
    - simpl in *. inversion H2.
    - simpl in H2. inversion H0.  subst.
      specialize (IHps H5 (S n)).
      destruct a.
      + specialize (IHps H2). intuition eauto.
      + specialize (IHps H2). intuition eauto.
      + simpl in H2. destruct H2.
        * injection H. intros. subst. simpl. intuition eauto. rep_lia. repeat constructor; eauto.
          admit. admit. (* Not sure yet. *)
       * specialize (IHps H). intuition eauto. admit.
}
  assert (  edge_compatible g 0 (newRaw v (Z.of_nat t) (map rep_field ps) R1 R2 R3) es).
  { unfold edge_compatible. intros. simpl. clear.  unfold es. generalize (0)%nat at 2 4.  induction ps; intros n; simpl; eauto.
    - reflexivity.
    - destruct a; simpl.
      + rewrite Nat.add_1_r.  apply IHps.
      + rewrite Nat.add_1_r.  apply IHps.
      + rewrite Nat.add_1_r. intuition eauto. right.  apply IHps; eauto.
        rewrite IHps. eauto. } (* FIXME joomy: Coq goes into infinite loop here *)
    intuition.
  all: eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_thread_compatible, add_node_ti_size_spec, add_node_roots_compatible.
  + eapply add_node_ti_size_spec; eauto.  rewrite spaces_size.   rep_lia.
  + apply add_node_graph_thread_compatible; eauto.
    simpl. rewrite Zlength_map. lia.
  + eapply add_node_outlier_compatible; eauto. simpl. (* destruct p eqn:Hp; simpl; eauto. *)
    admit.
    (* TODO: Not sure what to do with this outlier. *)
    (* unfold outlier_compatible in H9. *)
    (* THIS IS WEIRD. Should probably not be right. Or is it a problem that I allow things which are not nodes? *)
  + admit.
Admitted.

(* TOOD: WHAT ARE THE PRECONDITIONS
   TODO: GENERALIZE TO OTHER VERSION WITH NOT ONLY ONE REP_FIELD
 *)
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
  + eapply add_node_outlier_compatible; eauto. (* Print rep_field. *)  simpl. destruct p eqn:Hp; simpl; eauto.
    (* TODO: Not sure what to do with this outlier. *)
    unfold outlier_compatible in H9.
    admit. (* THIS IS WEIRD. Should probably not be right. Or is it a problem that I allow things which are not nodes? *)
Admitted.



(** ** Compatibility of tulong and int_or_ptr_type *)

Lemma data_at_int_or_ptr_ptr:
 forall {CS: compspecs}  v p Tsh,
Archi.ptr64 = true -> data_at Tsh tulong v p |--
  data_at Tsh int_or_ptr_type v p.
Proof.
  intros CS v p Tsh A.

   unfold data_at, field_at.
   simpl. f_equal.
   f_equal.
   unfold field_compatible.
   f_equal.
   f_equal.
   f_equal.
   f_equal.
   unfold align_compatible. entailer!.
   - destruct p; auto.
     eapply align_compatible_rec_by_value_inv in H1;
     try reflexivity;
     try (eapply align_compatible_rec_by_value; eauto).
     reflexivity.
   -  unfold at_offset.
   unfold nested_field_type;  simpl.
   unfold data_at_rec; simpl.
   unfold mapsto.
   simpl.
   destruct p; simpl; auto. entailer!.
   if_tac; auto.
   + hint. unfold is_long, is_pointer_or_integer.
     eapply orp_derives.
     *
         entailer.
         destruct v; try ( exfalso; eauto; congruence).
         rewrite A. (* Search "&&". *)
         rewrite prop_true_andp; eauto.
         (* Search "|--". *)
         apply derives_refl.
     * entailer. Exists x.
       rewrite TT_andp.
       unfold res_predicates.address_mapsto.
       simpl. unfold decode_val. simpl. unfold size_chunk_nat. simpl.
       eauto.
   + unfold tc_val'.
   unfold tc_val; simpl. entailer.
   unfold is_long in *.

   destruct v; try (exfalso; apply H3; eauto; congruence).
   * unfold is_pointer_or_integer.
     apply prop_and_same_derives'.
     eauto.
   * apply prop_and_same_derives'.
     eauto.
Qed.

Lemma data_at_int_or_ptr_ptr':
 forall {CS: compspecs}  v v' p p' sh sh',
   sh = sh' -> v = v' -> p =p' ->
Archi.ptr64 = true -> data_at sh tulong v p |--
  data_at sh' int_or_ptr_type v' p'.
Proof.
  intros. subst. eauto using data_at_int_or_ptr_ptr.
Qed.

Lemma data_at_tulong_int_or_ptr_array:
 forall {CS: compspecs} v p sh n,
Archi.ptr64 = true -> data_at sh (tarray int_or_ptr_type n) v p |--
                        data_at sh (tarray tulong n) v p
  .
  simpl.

  intros CS v p Tsh n A.

   unfold data_at, field_at.
   simpl. f_equal.
   f_equal.
   unfold field_compatible.
   f_equal.
   f_equal.
   f_equal.
   f_equal.
   unfold align_compatible. entailer!.
   - destruct p; auto.
     simpl in *.
     apply align_compatible_rec_Tarray. intros.
     eapply align_compatible_rec_Tarray_inv in H1; eauto.
     simpl in *. eauto.


     eapply align_compatible_rec_by_value_inv in H1;
     try reflexivity;
     try (eapply align_compatible_rec_by_value; eauto).
     reflexivity.
   -  unfold at_offset.
   unfold nested_field_type;  simpl.
   unfold data_at_rec; simpl.
   unfold mapsto.
   simpl.
   unfold array_pred. unfold aggregate_pred.array_pred.
   simpl.
   entailer!.
   apply aggregate_pred.rangespec_ext_derives.
   entailer!. (* Search at_offset. *)
   apply at_offset_derives. entailer!.
   destruct p0; entailer!.
   if_tac; eauto.
   + unfold is_long. unfold is_pointer_or_integer.
     destruct (@Znth (@reptype CS tulong) (@Inhabitant_reptype CS tulong) i v) eqn: HH; try entailer!.
     * entailer!. admit.
Admitted.

Goal forall  Tsh b i0,  EX v, (!! is_long v &&
  res_predicates.address_mapsto Mint64 v Tsh (b, Ptrofs.unsigned i0))
  = EX v, (!! is_pointer_or_integer v &&
      res_predicates.address_mapsto Mptr v Tsh (b, Ptrofs.unsigned i0)).
Proof.
  intros.  eapply pred_ext.
  - apply exp_left; intro v.
    pose (v' := match v with Vint j => Vint (Int.repr (Byte.unsigned (Byte.repr (Int.unsigned j))))
  | _ => Vundef
end).
    apply exp_right with v'.
    (* Print res_predicates.address_mapsto. *)
    unfold res_predicates.address_mapsto.


Admitted.



Lemma data_at_int_or_ptr_ptr_array:
 forall {CS: compspecs} v p sh n,
Archi.ptr64 = true -> data_at sh (tarray tulong n) v p |--
  data_at sh (tarray int_or_ptr_type n) v p .
Proof.
  intros CS v p Tsh n A. simpl in *.
   unfold data_at, field_at, field_compatible. simpl.
   entailer!.
   - unfold align_compatible.
     destruct p; auto. simpl in *.
     apply align_compatible_rec_Tarray. intros.
     eapply align_compatible_rec_Tarray_inv in H0; eauto.
     simpl in *. eauto.
     eapply align_compatible_rec_by_value_inv in H0;
     try reflexivity;
     try (eapply align_compatible_rec_by_value; eauto).
     reflexivity.
   - unfold at_offset, nested_field_type, data_at_rec, mapsto, array_pred, aggregate_pred.array_pred;  simpl.
      entailer!.
      apply aggregate_pred.rangespec_ext_derives. entailer!.
      apply at_offset_derives. entailer!.
      destruct p0; entailer!.
      assert (@Znth (@reptype CS tulong) (@Inhabitant_reptype CS tulong) i v = @Znth (@reptype CS int_or_ptr_type) (@Inhabitant_reptype CS int_or_ptr_type) i v) as <-.
       { unfold Znth. if_tac; eauto. }
      if_tac; eauto.
      +  apply orp_left.
         * apply orp_right1.
           entailer. rewrite prop_true_andp.
           -- unfold res_predicates.address_mapsto, size_chunk_nat, decode_val.
              simpl. now apply derives_refl'.
           -- unfold is_long, is_pointer_or_integer in *.
              destruct ((@Znth (@reptype CS tulong) (@Inhabitant_reptype CS tulong) i v)); simpl in *; eauto.
         * Intros x. apply orp_right2. Exists x. entailer.
      + entailer. rewrite prop_true_andp.
        apply derives_refl.
        split; eauto. unfold tc_val' in *. simpl in *. intros HH. specialize (H4 HH).
        unfold is_long, is_pointer_or_integer in *.
        destruct ((@Znth (@reptype CS tulong) (@Inhabitant_reptype CS tulong) i v)); simpl in *; eauto.
Qed.

Lemma data_at_int_or_ptr_ptr_array_extended:
 forall {CS: compspecs} v p sh n,
Archi.ptr64 = true -> data_at sh (tarray tulong n) v p |--
  data_at sh (tarray int_or_ptr_type n) v p && (!! (forall i, 0 <= i < 0 + Z.of_nat (Z.to_nat (Z.max 0 n)) -> is_long (Znth i v)) ).
Proof.
  intros. simpl in *.
  sep_apply data_at_int_or_ptr_ptr_array.
  entailer.
  unfold data_at, field_at, field_compatible. entailer.
  unfold at_offset. unfold nested_field_type. unfold data_at_rec. unfold mapsto, array_pred, aggregate_pred.array_pred;  simpl.
  entailer. clear.
  assert (0 = Z.of_nat O) as -> by reflexivity.
generalize O as low. intros low. generalize ((Z.to_nat (Z.max (Z.of_nat low) n))). clear n. intros n. revert low.
  induction n; intros; eauto.
  - simpl. entailer!.
  - simpl. assert (Z.succ (Z.of_nat low) = Z.of_nat (S low)) as -> by rep_lia.
    admit.
Admitted.
(*     assert (
    sep_apply (IHn (S low)).

sep_apply IHn.

 generalize 0.
  induction (Z.to_nat (Z.max 0 n)); eauto.
  - simpl. entailer!.
  - simpl.

  sep_apply (@aggregate_pred.rangespec_ext_derives 0 ((Z.to_nat (Z.max 0 n))) _  ( fun i => !!(is_long (Znth i v))) _).
  Check aggregate_pred.rangespec_elim.
  sep_apply aggregate_pred.rangespec_elim.
  sep_apply aggregate_pred.rangespec_elim.
      apply aggregate_pred.rangespec_ext_derives. entailer!.
      apply at_offset_derives. entailer!.
      destruct p0; entailer!. *)


Lemma data_at_int_or_ptr_ptr_array2:
 forall {CS: compspecs} v p sh n,
Archi.ptr64 = true -> (forall i, 0 <= i < 0 + Z.of_nat (Z.to_nat (Z.max 0 n)) -> is_long (Znth i v))  -> data_at sh (tarray int_or_ptr_type n) v p  |-- data_at sh (tarray tulong n) v p.
Proof.
  intros CS v p Tsh n A B. simpl in *.
   unfold data_at, field_at, field_compatible. simpl.
   entailer!.
   - unfold align_compatible.
     destruct p; auto. simpl in *.
     apply align_compatible_rec_Tarray. intros.
     eapply align_compatible_rec_Tarray_inv in H0; eauto.
     simpl in *. eauto.
     eapply align_compatible_rec_by_value_inv in H0;
     try reflexivity;
     try (eapply align_compatible_rec_by_value; eauto).
     reflexivity.
   - unfold at_offset, nested_field_type, data_at_rec, mapsto, array_pred, aggregate_pred.array_pred;  simpl.
      entailer!.
      apply aggregate_pred.rangespec_ext_derives. entailer!.
      apply at_offset_derives. entailer!.
      destruct p0; entailer!.
      assert (@Znth (@reptype CS tulong) (@Inhabitant_reptype CS tulong) i v = @Znth (@reptype CS int_or_ptr_type) (@Inhabitant_reptype CS int_or_ptr_type) i v) as <-.
       { unfold Znth. if_tac; eauto. }
      if_tac; eauto.
      +  apply orp_left.
         * apply orp_right1.
           entailer. rewrite prop_true_andp.
           -- unfold res_predicates.address_mapsto, size_chunk_nat, decode_val.
              simpl. now apply derives_refl'.
           -- unfold is_long, is_pointer_or_integer in *.
              specialize (B _ H2).
              enough ((@Znth (@reptype CS tulong) (@Inhabitant_reptype CS tulong) i v) = Znth i v) as ->.
              destruct (Znth i v ); simpl in *; eauto.
              unfold Znth; if_tac; eauto.
         * Intros x. apply orp_right2. Exists x. entailer.
      + entailer. rewrite prop_true_andp.
        apply derives_refl.
        split; eauto. unfold tc_val' in *. simpl in *. intros HH. specialize (H4 HH).
        unfold is_long, is_pointer_or_integer in *.
        specialize (B _ H2).
                      enough ((@Znth (@reptype CS tulong) (@Inhabitant_reptype CS tulong) i v) = Znth i v) as ->.
              destruct (Znth i v ); simpl in *; eauto.
              unfold Znth; if_tac; eauto.
Qed.
