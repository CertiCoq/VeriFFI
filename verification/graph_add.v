(** * Adding Nodes to CertiCoq Graph

Kathrin Stark, 2020. 

This file contains a function for adding a node to the CertiCoq Graph with a given label at the end of a generation. 
In the second part, we prove several compatibility properties for this augmented graph. 
 *)

Require Export CertiGraph.CertiGC.gc_correct.
From VeriFFI.library Require Export base_representation. 
Import GCGraph graph_model gc_spec.

(** ** 1. Definition of the function for adding a node to CertiCoq Graph with a given label. 

This vertex will be added automatically at the end of a generation to.. *)


(** Function for adapting the pregraph.
   Just have to add the new vertex new_v via pregraph_add_vertex 
   and the given edges with pregraph_add_edge. *)

Definition pregraph_add_my_edge g (x : (EType * (VType * VType))) := pregraph_add_edge g (fst x) (fst (snd x)) (snd (snd x)). 

Definition pregraph_add_v (g: LGraph) (new_v: VType) (xs : list (EType * (VType * VType))): PreGraph VType EType :=
  List.fold_left pregraph_add_my_edge xs (pregraph_add_vertex g new_v). 

(** Function for actually adding a node in generation to to graph g with the node label lb. *) 
Definition add_node (g : graph) (to : nat) (lb : raw_vertex_block) es : graph :=
  let new_v := new_copied_v g to in (** Address of the new node *) 
  Build_LabeledGraph _ _ _ (pregraph_add_v g new_v es) 
                     (update_vlabel (vlabel g) new_v lb)
                     (elabel g) (copy_v_update_glabel (glabel g) to).

Hint Unfold pregraph_add_my_edge pregraph_add_v add_node : graph_add. 

(** ** 2. Compatibility Proofs *) 

(** Condition for edges to later preserve the corresponding lemmas: 
    - Source of all edges should be v.
    - All targets are contained in the graph. 
    - The generation of the source node is earlier than the generation of the target node.
    - No edge shows up twice.
 *)
Definition add_node_compatible (g: graph) (v: VType) (es: list (EType * (VType * VType))) :=
  forall e src trg, In (e, (src, trg)) es -> fst e = v /\ fst e = src /\ graph_has_v g trg /\ (fst src <= fst trg)%nat /\  NoDup (map fst es) /\ trg <> v. 

Hint Unfold add_node_compatible : graph_add.

(** Creates a raw_vertex_block in the initial state for garbage collection. *)
Definition newRaw (v : VType) (raw_tag: Z) (raw_fields: list raw_field) (raw_tag_range : 0 <= raw_tag < 256)
    (raw_fields_range : 0 < Zlength raw_fields < two_power_pos 54)
    (tag_no_scan : NO_SCAN_TAG <= raw_tag -> ~ In None raw_fields): raw_vertex_block. 
refine (Build_raw_vertex_block false v  raw_fields 0 raw_tag _ _ _ _). 
all: cbn; try lia. eauto.
Defined.
 
(** *** dst *)
Lemma flcvae_dst_old: forall g  l e,
    ~ In e (map fst l) -> dst (fold_left pregraph_add_my_edge l g) e = dst g e.
Proof.
  intros. revert g H. induction l; intros; simpl. 1: reflexivity.
  rewrite IHl. 2: intro; apply H; simpl; right; assumption. simpl.
  unfold updateEdgeFunc. rewrite if_false. 1: reflexivity. unfold equiv. intro.
  apply H. simpl. left; assumption.
Qed.

Lemma add_node_dst (g: graph) to es e : 
 ~ In e (map fst es) -> dst g e = dst (pregraph_add_v g (new_copied_v g to) es) e. 
Proof.
  intros. unfold add_node_compatible in H.
  unfold pregraph_add_v. 
  assert (dst g e = dst (pregraph_add_vertex g (new_copied_v g to)) e) as -> by reflexivity. 
   remember (pregraph_add_vertex g (new_copied_v g to)) as g'. clear to g Heqg'. 
  revert g'.
  induction es. 
  - reflexivity. 
  - simpl. intros g. rewrite <- IHes; simpl in *; eauto. 
    unfold updateEdgeFunc. 
    destruct (EquivDec.equiv_dec (fst a) e); eauto. exfalso. eauto. 
Qed.

Lemma add_node_dst_new (g: graph) to es e src trg: 
  NoDup (map fst es) -> In (e, (src, trg)) es -> dst (pregraph_add_v g (new_copied_v g to) es) e = trg. 
Proof.
  intros ND H. unfold pregraph_add_v. remember (pregraph_add_vertex g (new_copied_v g to)) as g'. clear Heqg' g to. 
  rename g' into g.
  revert g. unfold pregraph_add_v. induction es; intros. 
  - simpl in *. contradiction.
  - simpl. 
    destruct H. 
    + subst. rewrite flcvae_dst_old. 
      * simpl. unfold updateEdgeFunc. rewrite if_true; reflexivity. 
      * simpl in ND. apply NoDup_cons_2 in ND. assumption. 
    + apply IHes; [apply NoDup_cons_1 in ND |]; assumption. 
Qed.

Hint Rewrite flcvae_dst_old add_node_dst add_node_dst_new : graph_add. 

(** *** src *)
Lemma flcvae_src_old: forall g  l e,
    ~ In e (map fst l) -> src (fold_left pregraph_add_my_edge l g) e = src g e.
Proof.
  intros. revert g H. induction l; intros; simpl. 1: reflexivity.
  rewrite IHl. 2: intro; apply H; simpl; right; assumption. simpl.
  unfold updateEdgeFunc. rewrite if_false. 1: reflexivity. unfold equiv. intro.
  apply H. simpl. left; assumption.
Qed.

Lemma add_node_src (g: graph) to es e : 
 ~ In e (map fst es) -> src g e = src (pregraph_add_v g (new_copied_v g to) es) e. 
Proof.
  intros. unfold add_node_compatible in H.
  unfold pregraph_add_v. 
  assert (src g e = src (pregraph_add_vertex g (new_copied_v g to)) e) as -> by reflexivity. 
   remember (pregraph_add_vertex g (new_copied_v g to)) as g'. clear to g Heqg'. 
  revert g'.
  induction es. 
  - reflexivity. 
  - simpl. intros g. rewrite <- IHes; simpl in *; eauto. 
    unfold updateEdgeFunc. 
    destruct (EquivDec.equiv_dec (fst a) e); eauto. exfalso. eauto. 
Qed.

Lemma add_node_src_new (g: graph) to es e srcn trg: 
  NoDup (map fst es) -> In (e, (srcn, trg)) es -> src (pregraph_add_v g (new_copied_v g to) es) e = srcn. 
Proof.
  intros ND H. unfold pregraph_add_v. remember (pregraph_add_vertex g (new_copied_v g to)) as g'. clear Heqg' g to. 
  rename g' into g.
  revert g. unfold pregraph_add_v. induction es; intros. 
  - simpl in *. contradiction.
  - simpl. 
    destruct H. 
    + subst. rewrite flcvae_src_old. 
      * simpl. unfold updateEdgeFunc. rewrite if_true; reflexivity. 
      * simpl in ND. apply NoDup_cons_2 in ND. assumption. 
    + apply IHes; [apply NoDup_cons_1 in ND |]; assumption. 
Qed.

Hint Rewrite flcvae_src_old add_node_src add_node_src_new : graph_add. 

(** The new node is contained in the graph. *)
Lemma add_node_has_index_new g to r es: 
graph_has_gen g to -> 
let v := new_copied_v g to in
gen_has_index (add_node g to r es) (fst v) (snd v).
Proof. 
  intros. unfold graph_has_gen in H. 
  destruct g; simpl in *. 
  unfold gen_has_index, add_node, nth_gen.
  simpl. 
  destruct glabel. simpl.
  rewrite cvmgil_eq; eauto.
  destruct (nth to g_gen null_info). simpl. rep_lia. 
Qed.

Hint Resolve add_node_has_index_new : graph_add. 

(** Looking up the new node, we actually get to the updated label. *) 
Lemma add_node_vlabel g to r es :
let v := new_copied_v g to in
vlabel (add_node g to r es) v = r. 
Proof. 
  simpl.
  unfold update_vlabel, EquivDec.equiv_dec. 
  if_tac; eauto. 
  unfold complement in H. exfalso. apply H. reflexivity.  
Qed.

(** If the generation exists, then pre-existing generations stay the same. *) 
Lemma add_node_nth_gen: forall g to n lb e,
    n <> to -> graph_has_gen g to ->
    nth_gen (add_node g to lb e) n = nth_gen g n.
Proof.
  intros. unfold lgraph_add_copied_v, nth_gen. simpl. remember (g_gen (glabel g)).
  apply cvmgil_not_eq; [|subst l]; assumption.
Qed.

Hint Rewrite add_node_vlabel add_node_nth_gen : graph_add. 

(** graph-has_gen stays unchanged *) 
Lemma add_node_graph_has_gen: forall g to n lb e,
    graph_has_gen g to ->
    graph_has_gen (add_node g to lb e) n <-> graph_has_gen g n.
Proof.
  intros. unfold graph_has_gen. simpl.
  rewrite cvmgil_length by assumption. reflexivity.
Qed.

Hint Resolve add_node_graph_has_gen: graph_add. 

(** The start of the generation stays unchanged. *) 
Lemma add_node_gen_start: forall g to n lb e,
    graph_has_gen g to -> gen_start (add_node g to lb e) n = gen_start g n.
Proof.
  intros. unfold gen_start. do 2 if_tac.
  - destruct (Nat.eq_dec n to).
    + subst n. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption.
      simpl. reflexivity.
    + rewrite add_node_nth_gen by assumption. reflexivity.
  - rewrite add_node_graph_has_gen in H0 by assumption. contradiction.
  - exfalso. apply H0. rewrite add_node_graph_has_gen; assumption.
  - reflexivity.
Qed.

(** The vlabel of all old vertices stays unchanged. *) 
Lemma add_node_vlabel_old: forall (g : LGraph) (to: nat) lb e x,
    x <> new_copied_v g to -> vlabel (add_node g to lb e) x = vlabel g x.
Proof.
  intros. simpl.
  unfold update_copied_new_vlabel, graph_gen.update_vlabel.
  rewrite if_false. 1: reflexivity. unfold Equivalence.equiv; intro S; apply H.
  inversion S; reflexivity.
Qed.

Hint Rewrite add_node_gen_start add_node_vlabel_old : graph_add. 

(** The vertex address stays unchanged, as long as the generation of the vertex is contained in g, and the vertex is contained in the graph. 

closure_has_index seems to also contain the next node, i.e. <= number_of_vertices.
*) 
Lemma add_node_vertex_address: forall (g : LGraph) (to: nat) lb e x,
    closure_has_v g x -> graph_has_gen g to ->
    vertex_address (add_node g to lb e) x = vertex_address g x.
Proof.
  intros. destruct x as [n m]. destruct H. simpl in *. unfold vertex_address. f_equal.
  - f_equal. unfold vertex_offset. f_equal. unfold previous_vertices_size.
    simpl. apply fold_left_ext. intros. unfold vertex_size_accum. f_equal.
    unfold vertex_size. f_equal. rewrite add_node_vlabel_old. 1: reflexivity.
    intro. unfold new_copied_v in H3. inversion H3.
    rewrite nat_inc_list_In_iff in H2. subst n. red in H1. lia.
  - simpl. apply add_node_gen_start. assumption.
Qed.

Lemma add_node_vertex_address_old: forall (g : LGraph) (to: nat) lb e x,
    graph_has_v g x -> graph_has_gen g to ->
    vertex_address (add_node g to lb e) x = vertex_address g x.
Proof.
  intros. apply add_node_vertex_address; [apply graph_has_v_in_closure |]; assumption.
Qed.

Lemma add_node_make_header_old: forall (g : LGraph) (to : nat) lb e x,
    x <> new_copied_v g to ->
    make_header (add_node g to lb e) x = make_header g x.
Proof.
  intros. unfold make_header. rewrite add_node_vlabel_old by assumption. reflexivity.
Qed.

Hint Rewrite add_node_vertex_address add_node_vertex_address_old add_node_make_header_old : graph_add. 


Lemma add_node_field2val_make_fields_old:  forall (g : LGraph) (to : nat) lb es x,
    add_node_compatible g (new_copied_v g to) es -> graph_has_v g x -> graph_has_gen g to -> no_dangling_dst g -> 
    map (field2val (add_node g to lb es))
        (make_fields (add_node g to lb es) x) =
    map (field2val g) (make_fields g x).
Proof.
  intros g to lb es x E H H0 D. unfold make_fields. pose proof (graph_has_v_not_eq _ to _ H) as H1.
  rewrite add_node_vlabel_old by assumption. apply map_ext_in.
  intros [[? | ?] | ?] ?; simpl; try reflexivity. 
  rewrite <- add_node_dst; eauto. 
  rewrite add_node_vertex_address_old; eauto.
  - eapply D. eassumption. 
  unfold get_edges. rewrite <- filter_sum_right_In_iff. assumption. 
  - unfold no_dangling_dst in D. 
    unfold get_edges in D.
 
    assert (HH := get_edges_fst g x e). 
    assert (In e (get_edges g x)). 
    { unfold get_edges. unfold make_fields.
      remember (make_fields' (raw_fields (vlabel g x)) x 0) as xs. 
      clear - H2. induction xs; simpl in *; eauto. destruct H2; eauto.  
      - subst. now left. 
      - destruct a; eauto. right. eauto. }
    specialize (HH H3). intros A. rewrite In_map_fst_iff in A.   destruct A as ((src&trg)&A).
    unfold add_node_compatible in E. destruct (E _ _ _ A) as (E1&E2&E3). congruence. 
Qed.


(* Subpart of copy_compatible *) 
Definition copied_vertex_existence g := 
  forall x, graph_has_v g x -> graph_has_v g (copied_vertex (vlabel g x)).  

Hint Unfold copied_vertex_existence : graph_add. 

Lemma add_node_make_fields_vals_old: forall (g : LGraph) (to: nat) lb e x,
    add_node_compatible g (new_copied_v g to) e -> graph_has_v g x -> graph_has_gen g to ->  no_dangling_dst g ->  copied_vertex_existence g ->
    make_fields_vals (add_node g to lb e) x = make_fields_vals g x.
Proof.
  intros g to lb e x E H H0 D C. pose proof (add_node_field2val_make_fields_old g to lb e x E H H0 (* H0 H1 *)).
  unfold make_fields_vals. pose proof (graph_has_v_not_eq g to x H).
  rewrite add_node_vlabel_old by assumption. rewrite H1; eauto.
  destruct (raw_mark (vlabel g x)) eqn:? ; [f_equal | reflexivity].
  apply add_node_vertex_address_old; try assumption. 
  unfold no_dangling_dst in D. 
  apply C. eauto. 
Qed.

Lemma add_node_generation_rep_not_eq: forall g to n lb e,
    n <> to -> graph_has_gen g to -> no_dangling_dst g -> copied_vertex_existence g -> add_node_compatible g (new_copied_v g to) e ->
    generation_rep (add_node g to lb e) n = generation_rep g n.
Proof.
  intros g to n lb e H H0 D C E. unfold generation_rep. rewrite add_node_nth_gen by assumption.
  apply iter_sepcon.iter_sepcon_func_strong. intros. apply list_in_map_inv in H1.
  destruct H1 as [m [? ?]]. unfold nth_sh. rewrite add_node_nth_gen by assumption.
  remember (generation_sh (nth_gen g n)) as sh. unfold vertex_rep. subst x.
  assert (graph_has_v g (n, m)). {
    rewrite nat_inc_list_In_iff in H2.
    destruct (Nat.lt_ge_cases n (length (g_gen (glabel g)))).
    - split; simpl; assumption.
    - exfalso. unfold nth_gen in H2. rewrite nth_overflow in H2 by assumption.
      simpl in H2. lia. } f_equal.
  - apply add_node_vertex_address_old; assumption.
  - apply add_node_make_header_old. intro S; inversion S. contradiction.
  - apply add_node_make_fields_vals_old; try assumption.
Qed.

Lemma add_node_icgr_not_eq: forall l g to lb e,
    ~ In to l -> graph_has_gen g to ->  no_dangling_dst g -> copied_vertex_existence g -> add_node_compatible g (new_copied_v g to) e ->
    iter_sepcon.iter_sepcon l (generation_rep (add_node g to lb e)) =
    iter_sepcon.iter_sepcon l (generation_rep g).
Proof.
  intros. induction l; simpl. 1: reflexivity. rewrite IHl.
  - f_equal. apply add_node_generation_rep_not_eq; [|assumption..].
    intro. apply H. left. assumption.
  - intro. apply H. right. assumption.
Qed. 

Lemma add_node_nth_sh: forall (g : LGraph)  (to : nat) lb e n,
    graph_has_gen g to -> nth_sh (add_node g to lb e) n = nth_sh g n.
Proof.
  intros. unfold nth_sh, nth_gen. simpl. destruct (Nat.eq_dec n to).
  - subst n. rewrite cvmgil_eq by assumption. simpl. reflexivity.
  - rewrite cvmgil_not_eq by assumption. reflexivity.
Qed.

Lemma add_node_vertex_address_new: forall (g : LGraph) (to: nat) lb e,
    graph_has_gen g to ->
    vertex_address (add_node g to lb e) (new_copied_v g to) =
    vertex_address g (new_copied_v g to).
Proof.
  intros. unfold new_copied_v. apply add_node_vertex_address. 2: assumption.
  red. simpl.  split; [assumption | apply Nat.le_refl].
Qed. 

Hint Rewrite add_node_nth_sh add_node_vertex_address_new : graph_add. 

Lemma add_node_generation_rep_eq: forall g to lb e,
    let v := new_copied_v g to in
    let h := if raw_mark lb then 0 else raw_tag lb + Z.shiftl (raw_color lb) 8 + Z.shiftl (Zlength (raw_fields lb)) 10 in
    let g' := add_node g to lb e in
    let fds := 
        let original_fields_val := map (field2val g') (make_fields g' v) in
        if raw_mark lb
        then vertex_address g' (copied_vertex lb) :: tl original_fields_val
        else original_fields_val in
    (* graph_has_v g v -> *) graph_has_gen g to -> (* no_dangling_dst g -> copy_compatible g -> *)
 no_dangling_dst g -> copied_vertex_existence g -> add_node_compatible g (new_copied_v g to) e ->
    generation_rep (add_node g to lb e) to =
    (vertex_at (nth_sh g to) (vertex_address (add_node g to lb e) v) h (* make_fields_vals g v *) fds * generation_rep g to)%logic. (* TODO: Simplify the address. *)
Proof.
  intros. unfold generation_rep. rewrite add_node_nth_sh by assumption.
  remember (number_of_vertices (nth_gen g to)).
  unfold add_node at 1. unfold nth_gen. simpl.
  rewrite cvmgil_eq by assumption. simpl. unfold nth_gen in Heqn. rewrite <- Heqn.
  rewrite nat_inc_list_app, map_app, iter_sepcon_app_sepcon, sepcon_comm.
  simpl nat_seq. change (nth to (g_gen (glabel g)) null_info) with
                     (nth_gen g to) in Heqn. f_equal.
  - simpl. normalize. subst v.
    unfold vertex_rep.
    assert ((to, n) = new_copied_v g to) as COPY. 
    { unfold new_copied_v. congruence. }
    assert (vlabel (add_node g to lb e) (to, n) = lb) as LB. 
    { rewrite COPY. 
      now rewrite add_node_vlabel. }
    f_equal. 
    + rewrite COPY. reflexivity. 
    + subst h. 
      unfold make_header. 
      rewrite LB. reflexivity. 
    + subst fds. unfold make_fields_vals. 
      rewrite LB. subst g'. rewrite COPY.  f_equal. 
      congruence. 
  - apply iter_sepcon.iter_sepcon_func_strong. intros x IN. destruct x as [m x].
    apply list_in_map_inv in IN as [? [? ?]]. inversion H3. subst x0.
    subst m. clear H3. remember (nth_sh g to) as sh. subst n.
    rewrite nat_inc_list_In_iff in H4. unfold vertex_rep.
    assert (graph_has_v g (to, x)) by (split; simpl; assumption).
    rewrite add_node_vertex_address_old, add_node_make_header_old, add_node_make_fields_vals_old;
      [reflexivity | try assumption..].
    unfold new_copied_v. intro. inversion H5. lia.
Qed.

Definition header_new lb := 
if raw_mark lb then 0 else raw_tag lb + Z.shiftl (raw_color lb) 8 + Z.shiftl (Zlength (raw_fields lb)) 10. 

Definition fields_new g' lb v :=
  let original_fields_val := map (field2val g') (make_fields g' v) in
    if raw_mark lb
    then vertex_address g' (copied_vertex lb) :: tl original_fields_val
    else original_fields_val. 

Lemma add_node_spatial g to lb e: 
let v := new_copied_v g to in
let g' := add_node g to lb e in
graph_has_gen g to ->
 no_dangling_dst g -> copied_vertex_existence g -> add_node_compatible g (new_copied_v g to) e ->
graph_rep g' = 
(graph_rep g *
vertex_at (nth_sh g to)  (vertex_address g' v) (header_new lb) (fields_new g' lb v) 
)%logic. 
Proof.
  intros v g' H D E C.  unfold g', graph_rep. unfold add_node at 1. simpl. red in H. 
  rewrite cvmgil_length by assumption. remember (length (g_gen (glabel g))). 
  assert (n = to + (n - to))%nat by lia. assert (0 < n - to)%nat by lia. 
  remember (n-to)%nat as m. rewrite H0, nat_inc_list_app, !iter_sepcon_app_sepcon. 
  assert (iter_sepcon.iter_sepcon (nat_inc_list to) (generation_rep (add_node g to lb e)) = iter_sepcon.iter_sepcon (nat_inc_list to) (generation_rep g) ). 
  { apply add_node_icgr_not_eq; eauto. 
    intros H_In; rewrite nat_inc_list_In_iff in H_In; lia.
    unfold graph_has_gen. congruence. }
  rewrite H2. clear H2. rewrite !sepcon_assoc. f_equal. 
  assert (m = 1 + (m - 1))%nat by lia.
  rewrite H2, nat_seq_app, !iter_sepcon_app_sepcon.
  assert (nat_seq to 1 = [to]) by reflexivity. rewrite H3. clear H3.
  rewrite (add_node_icgr_not_eq (nat_seq (to + 1) (m - 1)) g to lb e); try assumption.
  3: subst n; apply H. 2: intros H_In; rewrite nat_seq_In_iff in H_In; lia.
  setoid_rewrite sepcon_comm at 3. rewrite <- sepcon_assoc.  f_equal. 
  simpl iter_sepcon.iter_sepcon. normalize. clear m Heqm H0 H1 H2. subst n.
  rewrite <- add_node_generation_rep_eq with (lb := lb); eauto. 
Qed.

Lemma compatible_add_node g v n raw_fields ps to lb e: 
add_node_compatible g (new_copied_v g to) e -> v <> new_copied_v g to -> compatible g v n raw_fields ps -> compatible (add_node g to lb e) v n raw_fields ps. 
Proof. 
  intros C B.
  induction 1; constructor; eauto.  
  rewrite <- H0. 
  unfold field_rep. 
  destruct x; eauto. simpl. 
  rewrite <- add_node_dst; eauto. 
  intros A. rewrite In_map_fst_iff in A. destruct A as ((src&trg)&A).
  unfold add_node_compatible in C. destruct (C _ _ _ A). simpl in *. congruence. 
 Qed. 

Hint Resolve compatible_add_node : graph_add. 

Require Import Nat. 

Lemma number_of_vertices_new g to lb es: 
  graph_has_gen g to -> number_of_vertices (nth_gen (add_node g to lb es) to) = S (number_of_vertices (nth_gen g to)). 
Proof. 
  intros H. 
      unfold nth_gen. simpl.
  unfold copy_v_mod_gen_info_list. unfold graph_has_gen in H.
    remember (g_gen (glabel g)) as xs. 
unfold copy_v_mod_gen_info.  clear Heqxs. 
    assert (Datatypes.length (firstn to xs) = to). 
    { apply firstn_length_le. lia. }
    rewrite app_nth2; try lia. rewrite H0 in *.
    rewrite Nat.sub_diag. simpl. lia. 
Qed.

Hint Rewrite number_of_vertices_new : graph_add. 

Lemma number_of_vertices_increases g gen to lb e: 
  graph_has_gen g to -> (number_of_vertices (nth_gen g gen) <= number_of_vertices (nth_gen (add_node g to lb e) gen))%nat. 
Proof.
  intros H.
  destruct (EqDec_nat gen to). 
  - subst. rewrite number_of_vertices_new; eauto. 
  - rewrite add_node_nth_gen; eauto. 
Qed.


Lemma add_node_gen_has_index_impl g gen i to lb es: 
  graph_has_gen g to -> gen_has_index g gen i -> gen_has_index (add_node g to lb es) gen i. 
Proof.
  intros H I.
  unfold gen_has_index in *.
  assert (H' := number_of_vertices_increases g gen to lb es H). lia. 
Qed.


Lemma add_node_gen_has_index_old g gen i to lb es: 
  graph_has_gen g to  -> gen <> to -> gen_has_index g gen i <-> gen_has_index (add_node g to lb es) gen i. 
Proof.
  intros H I.
  unfold gen_has_index in *.
  assert (H' := number_of_vertices_increases g gen to lb es H). 
  rewrite add_node_nth_gen; eauto. 
  reflexivity. 
Qed.

Lemma add_node_gen_has_index g i to lb es: 
  graph_has_gen g to  -> gen_has_index g to i \/ i = snd (new_copied_v g to) <-> gen_has_index (add_node g to lb es) to i. 
Proof.
  intros H. unfold gen_has_index. simpl. 
  simpl. rewrite number_of_vertices_new; eauto. rep_lia. 
Qed.


Lemma add_node_graph_has_v_impl g v to lb es : 
  graph_has_gen g to -> graph_has_v g v -> graph_has_v (add_node g to lb es) v.
Proof.
  intros H (H1&H2). unfold graph_has_v.
  split. 
  - rewrite add_node_graph_has_gen; eauto. 
  - apply add_node_gen_has_index_impl; eauto. 
Qed.

Lemma add_node_graph_has_v g v to lb es : 
  graph_has_gen g to -> graph_has_v g v \/ v = new_copied_v g to <-> graph_has_v (add_node g to lb es) v.
Proof.
  intros H.
  unfold graph_has_v. rewrite add_node_graph_has_gen; eauto. destruct (EqDec_nat (vgeneration v) to). 
  - subst. rewrite <- add_node_gen_has_index; eauto.  intuition eauto. 
   + simpl. right. rewrite H1 at 1.                                                                                
     reflexivity. 
  + unfold new_copied_v. simpl in H0. rewrite <- H0. right. destruct v; reflexivity.
  - rewrite <- add_node_gen_has_index_old; eauto. intuition eauto.
    + subst. simpl in *. contradiction. 
    + subst. simpl in *. contradiction.
Qed.


Lemma add_node_graph_has_v_old g v to lb es : 
  graph_has_gen g to -> v <> new_copied_v g to ->  graph_has_v g v <-> graph_has_v (add_node g to lb es) v.
Proof. 
  intros. rewrite <- add_node_graph_has_v; eauto. intuition.
Qed.

Hint Resolve add_node_gen_has_index_impl add_node_gen_has_index_old add_node_gen_has_index add_node_graph_has_v_impl add_node_graph_has_v add_node_graph_has_v_old : graph_add. 


Definition edge_compatible g to lb (es: list (EType * (VType * VType))) :=
forall e, In e (filter_sum_right (make_fields' (raw_fields lb) (new_copied_v g to) 0)) <-> 
  In e (map fst es). 

Lemma add_node_get_edges_or e g to lb es: 
  graph_has_gen g to ->
  graph_has_v (add_node g to lb es) (fst e) ->
  edge_compatible g to lb es ->
  add_node_compatible g (new_copied_v g to) es -> 
  In e (get_edges (add_node g to lb es) (fst e)) -> 
  In e (map fst es) \/ ~ In e (map fst es) /\ graph_has_v g (fst e) /\ In e (get_edges g (fst e)).
Proof.
  intros G He EC C.
  unfold get_edges. 
  unfold make_fields. (* intros H.
  unfold add_node_compatible in H. *) 
  destruct (V_EqDec (fst e) (new_copied_v g to)).
  - rewrite e0. rewrite add_node_vlabel. intros H. 
    left. now eapply EC in H.
  - intros A. rewrite add_node_vlabel_old in A.
    + right.  split3; eauto.
      * intros B. unfold edge_compatible in EC.
        unfold add_node_compatible in C.
        assert (B' := B).
        rewrite In_map_fst_iff in B. destruct B as ((src&trg)&B).
        destruct (C _ _ _ B) as (C1&C2&C3&C4&C5). subst. congruence. 
      * apply add_node_graph_has_v in He; eauto. destruct He; eauto. congruence.
    + eauto.
Qed.
    

Lemma add_node_graph_has_e g to lb es e : 
    graph_has_gen g to ->
   edge_compatible g to lb es ->
  add_node_compatible g (new_copied_v g to) es -> 
  graph_has_e (add_node g to lb es) e -> In e (map fst es) \/ (~ In e (map fst es) /\ graph_has_e g e).
Proof.
  intros G EC C.
  unfold graph_has_e.  
  - intros (A1&A2). apply add_node_get_edges_or in A2; eauto. 
Qed.  


Lemma add_node_no_dangling_dst g to lb es: 
    edge_compatible g to lb es ->
  add_node_compatible g (new_copied_v g to) es -> 
  graph_has_gen g to -> add_node_compatible g (new_copied_v g to) es -> no_dangling_dst g -> no_dangling_dst (add_node g to lb es). 
Proof. 
  intros EC CO C H D v A e B. unfold add_node_compatible in C.
  destruct e as (v'&p). 
  assert (v = v') as <-. 
  { apply get_edges_fst in B. simpl in *. eauto. }
  simpl in *.

  apply add_node_get_edges_or in B; eauto. destruct B as [B|(B1&B2&B3)].
  -  
    rewrite In_map_fst_iff in B. destruct B as ((src&trg)&B). simpl. 
    erewrite (add_node_dst_new g to es _ src trg _ B).
    unfold add_node_compatible in H. apply add_node_graph_has_v_impl; eauto. eapply H; eauto. 
    Unshelve. unfold add_node_compatible in H. eapply H; eauto. 
  - unfold no_dangling_dst in D.
    simpl in *. 
    rewrite <- add_node_dst; eauto. 
    specialize (D _ B2 _ B3). apply add_node_graph_has_v_impl; eauto.
Qed.

Lemma add_node_graph_unmarked g to lb es : 
  graph_has_gen g to -> raw_mark lb = false -> graph_unmarked g -> graph_unmarked (add_node g to lb es). 
Proof.
  intros G H A. 
  unfold graph_unmarked in *. 
  intros v. destruct (V_EqDec v (new_copied_v g to)).
  - intros _. simpl. unfold update_vlabel. if_tac; congruence. 
  - rewrite <- add_node_graph_has_v_old; eauto.
    intros. rewrite add_node_vlabel_old; eauto. 
Qed.

Lemma add_node_no_backward_edge g to lb es: 
  graph_has_gen g to ->  edge_compatible g to lb es ->
  add_node_compatible g (new_copied_v g to) es -> 
 add_node_compatible g (new_copied_v g to) es  ->  no_backward_edge g -> no_backward_edge (add_node g to lb es). 
Proof.
  intros G EC C A B. 
  unfold no_backward_edge. intros g1 g2 H. 
  unfold gen2gen_no_edge. intros v e E. 
  simpl. 
  destruct (add_node_graph_has_e _ to lb es _ G EC C E) as [E'|(E1'&E2')]. 
  - rewrite In_map_fst_iff in E'. destruct E' as ((src&trg)&E'). 
    erewrite (add_node_dst_new _ _ _ _ _ _ _ E'). 
    unfold add_node_compatible in A. destruct (A _ _ _ E') as (A1&A2&A3&A4).
    simpl in *. unfold new_copied_v in A1. injection A1. intros. subst. 
    simpl in A4. unfold vgeneration. rep_lia. 
    Unshelve. eapply A. eauto.
  - unfold no_backward_edge in B. specialize (B _ _ H _ _ E2' ). 
    rewrite <- add_node_dst; eauto.   
Qed.

Definition add_node_space (to : nat) (sp : space) (off : Z) (H: 0 <= off <= total_space sp - used_space sp): space. 
  assert (0 <= used_space sp + off <= total_space sp).
  { assert (H' := space_order sp).  rep_lia. }
  pose (sp' := Build_space (space_start sp) (used_space sp + off) (total_space sp) (space_sh sp) H0 (space_upper_bound sp)).
  exact sp'. 
Defined.

Definition add_node_heap (to : nat) (hp : heap) (off : Z) : 
  let sp :=  nth to (spaces hp) null_space 
in  0 <= off <= total_space sp - used_space sp -> heap. 
  intros sp H.
  refine (Build_heap (upd_Znth (Z.of_nat to) (spaces hp) (add_node_space to sp off H) ) _).
    rewrite Zlength_upd_Znth. apply spaces_size.
Defined. 

Definition add_node_ti (to : nat) (ti : GCGraph.thread_info) (off : Z) (H: 0 <= off <= total_space (nth_space ti to) - used_space (nth_space ti to)): GCGraph.thread_info := 
Build_thread_info (ti_heap_p ti) (add_node_heap to (ti_heap ti) off H) (ti_args ti) (arg_size ti). 
 
Lemma add_node_heap_start to hp off H (sz : Z.of_nat to < Zlength (spaces hp)): 
   space_start (nth to (spaces (add_node_heap to hp off H)) null_space) = space_start (nth to (spaces hp) null_space). 
Proof.
  unfold add_node_heap. simpl. 
  rewrite <- nat_of_Z_eq at 1. rewrite nth_Znth. 
  rewrite upd_Znth_same; try rep_lia. reflexivity. 
  rewrite Zlength_upd_Znth. 
  rep_lia. 
Qed.

Lemma add_node_heap_start0 hp off H: 
  space_start (heap_head (add_node_heap 0 hp off H)) = space_start (heap_head hp). 
Proof.
  destruct (heap_head_cons hp) as (sp1&sp2&HP1&HP2). 
  destruct (heap_head_cons (add_node_heap 0 hp off H)) as (sp1'&sp2'&HP1'&HP2'). 
  rewrite HP2'.  
  simpl in HP1'. setoid_rewrite HP1 at 1 in HP1'.
  rewrite upd_Znth0 in HP1'. 
  injection HP1'. intros. rewrite <- H1. simpl. 
  rewrite HP1. simpl. congruence. 
Qed.

Lemma add_node_heap_total0 hp off H: 
total_space (heap_head (add_node_heap 0 hp off H)) = total_space (heap_head hp). 
Proof. 
  destruct (heap_head_cons hp) as (sp1&sp2&HP1&HP2). 
  destruct (heap_head_cons (add_node_heap 0 hp off H)) as (sp1'&sp2'&HP1'&HP2'). 
  rewrite HP2'.  
  simpl in HP1'. setoid_rewrite HP1 at 1 in HP1'.
  rewrite upd_Znth0 in HP1'. 
  injection HP1'. intros. rewrite <- H1. simpl. 
  rewrite HP1. simpl. congruence. 
Qed.


Lemma add_node_heap_sh0 hp off H: 
space_sh (heap_head (add_node_heap 0 hp off H)) = space_sh (heap_head hp). 
Proof. 
    destruct (heap_head_cons hp) as (sp1&sp2&HP1&HP2). 
  destruct (heap_head_cons (add_node_heap 0 hp off H)) as (sp1'&sp2'&HP1'&HP2'). 
  rewrite HP2'.  
  simpl in HP1'. setoid_rewrite HP1 at 1 in HP1'.
  rewrite upd_Znth0 in HP1'. 
  injection HP1'. intros. rewrite <- H1. simpl. 
  rewrite HP1. simpl. congruence. 
Qed.

Lemma add_node_heap_used_space0 hp off H : 
  used_space (heap_head (add_node_heap 0 hp off H)) = used_space (heap_head hp) + off. 
Proof.
    destruct (heap_head_cons hp) as (sp1&sp2&HP1&HP2). 
  destruct (heap_head_cons (add_node_heap 0 hp off H)) as (sp1'&sp2'&HP1'&HP2'). 
  rewrite HP2'.  
  simpl in HP1'. setoid_rewrite HP1 at 1 in HP1'.
  rewrite upd_Znth0 in HP1'. 
  injection HP1'. intros. rewrite <- H1. simpl. 
  rewrite HP1. simpl. congruence. 
Qed.

Arguments add_node_heap: simpl never.

Lemma add_node_heap_start_real n to hp off H (sz : Z.of_nat n < Zlength (spaces hp)) (sz2 : Z.of_nat to < Zlength (spaces hp)): 
   space_start (nth n (spaces (add_node_heap to hp off H)) null_space) = space_start (nth n (spaces hp) null_space). 
Proof.
  unfold add_node_heap. simpl. 
  rewrite <- nat_of_Z_eq at 1.
  rewrite nth_Znth.

  destruct (EqDec_nat n to). 
  - rewrite e.
    rewrite upd_Znth_same; try rep_lia. reflexivity. 
  - rewrite upd_Znth_diff'; try rep_lia.
    rewrite <- nth_Znth; try rep_lia. 
    repeat f_equal. rep_lia. 
  - rewrite Zlength_upd_Znth. 
  rep_lia. 
Qed. 

Lemma add_node_heap_total_real n to hp off H (sz : Z.of_nat n < Zlength (spaces hp)) (sz2 : Z.of_nat to < Zlength (spaces hp)): 
   total_space (nth n (spaces (add_node_heap to hp off H)) null_space) = total_space (nth n (spaces hp) null_space). 
Proof.
  unfold add_node_heap. simpl. 
  rewrite <- nat_of_Z_eq at 1.
  rewrite nth_Znth.

  destruct (EqDec_nat n to). 
  - rewrite e.
    rewrite upd_Znth_same; try rep_lia. reflexivity. 
  - rewrite upd_Znth_diff'; try rep_lia.
    rewrite <- nth_Znth; try rep_lia. 
    repeat f_equal. rep_lia. 
  - rewrite Zlength_upd_Znth. 
  rep_lia. 
Qed.



Lemma add_node_heap_ti_token_rep (to : nat) (ti : GCGraph.thread_info) (off : Z) H (size : 0 <= Z.of_nat to < Zlength (spaces (ti_heap ti))): 
ti_token_rep (add_node_ti to ti off H) = ti_token_rep ti.
Proof.
  unfold ti_token_rep. simpl. f_equal.
  setoid_rewrite <- upd_Znth_unchanged with (i := Z.of_nat to) (l := spaces (ti_heap ti)) at 3; eauto. 
  rewrite !upd_Znth_unfold; eauto.
  rewrite !iter_sepcon_app_sepcon. 
  f_equal. f_equal. 
  simpl. unfold space_token_rep. f_equal. unfold add_node_space. simpl.
  rewrite <- (nat_of_Z_eq to). 
  rewrite nth_Znth. 
  rewrite nat_of_Z_eq. unfold space_inhabitant. 
  if_tac; eauto. 
  rep_lia. 
Qed.

Lemma add_node_previous_vertices_size g to lb e gen x : 
  closure_has_index g gen x -> previous_vertices_size (add_node g to lb e) gen x = previous_vertices_size g gen x. 
Proof.
  intros A. 
  unfold previous_vertices_size.
    simpl. apply fold_left_ext. intros. unfold vertex_size_accum. f_equal.
    unfold vertex_size. f_equal. rewrite add_node_vlabel_old. 1: reflexivity.
    intro. unfold new_copied_v in *. inversion H0. subst.  clear H0.
    rewrite nat_inc_list_In_iff in H. red in A. lia.
Qed.

Hint Rewrite add_node_heap_start add_node_heap_start0 add_node_heap_total0 add_node_heap_sh0 add_node_heap_used_space0 add_node_heap_start_real add_node_heap_total_real add_node_heap_ti_token_rep add_node_previous_vertices_size: graph_add. 


Lemma add_node_safe_to_copy0 g lb es : 
  graph_has_gen g 0 -> safe_to_copy g -> safe_to_copy (add_node g 0 lb es). 
Proof.
  unfold safe_to_copy. intros H A. intros.
  assert (A' := A n).
  rewrite add_node_graph_has_gen in H0; eauto. specialize (A' H0).
  unfold safe_to_copy_gen in *.
  unfold graph_gen_size. rewrite add_node_nth_gen; eauto.  
Qed.

Lemma add_node_roots_graph_compatible g roots to lb es : 
  graph_has_gen g to -> roots_graph_compatible roots g -> roots_graph_compatible roots (add_node g to lb es).
Proof.
  intros G.
  unfold roots_graph_compatible. rewrite !Forall_forall. 
  intros A v B. apply add_node_graph_has_v_impl; eauto.
Qed.

Lemma add_node_roots_compatible g outlier roots to lb es : 
  graph_has_gen g to -> roots_compatible g outlier roots -> roots_compatible (add_node g to lb es) outlier roots. 
Proof.
  unfold roots_compatible. intuition. 
  eauto using add_node_roots_graph_compatible.
Qed.


Lemma add_node_outlier_compatible g outlier to lb es : 
   graph_has_gen g to ->  incl (filter_sum_right (filter_option (raw_fields lb))) outlier -> outlier_compatible g outlier -> outlier_compatible (add_node g to lb es) outlier. 
Proof.
    unfold outlier_compatible.
    intros G I A v B%add_node_graph_has_v; eauto. 
    destruct B. 
    - rewrite add_node_vlabel_old. 
      eauto. now eapply graph_has_v_not_eq.   
    - subst. rewrite add_node_vlabel. eauto.
Qed.

Lemma add_node_graph_thread_compatible g t_info to lb es (off : Z) (H: 0 <= off <= total_space (nth_space t_info to) - used_space (nth_space t_info to)): 
   Zlength (raw_fields lb) + 1 = off -> graph_has_gen g to -> no_dangling_dst g -> graph_thread_info_compatible g t_info -> graph_thread_info_compatible (add_node g to lb es) (add_node_ti to t_info off H). 
Proof.
  unfold graph_thread_info_compatible. intros L HH ND (A1&A2&A3). 
  assert (Datatypes.length (copy_v_mod_gen_info_list (g_gen (glabel g)) to) = Datatypes.length (g_gen (glabel g))) as LU.
  { simpl. unfold copy_v_mod_gen_info_list.
     rewrite !app_length. simpl. rewrite List.skipn_length. unfold graph_has_gen in HH.
     rewrite firstn_length_le; rep_lia. }   
    split3. 
  - rewrite !Forall_forall in *.
    intros ((n&g_n)&s_n) B.
    unfold no_dangling_dst in ND.
    apply In_nth with (d := (n, g_n, s_n)) in B. destruct B as (l&B1&B2).
    rewrite !combine_length in *. rewrite !nat_inc_list_length in *.
    
    erewrite !combine_nth_lt in B2; try rep_lia.   
    specialize (A1 (nth l (combine
            (combine (nat_inc_list (Datatypes.length (g_gen (glabel g)))) (g_gen (glabel g)))
            (spaces (ti_heap t_info))) (n, g_n, s_n)) ).
    assert (In
         (nth l
            (combine
               (combine (nat_inc_list (Datatypes.length (g_gen (glabel g))))
                  (g_gen (glabel g))) (spaces (ti_heap t_info))) 
            (n, g_n, s_n))
         (combine
            (combine (nat_inc_list (Datatypes.length (g_gen (glabel g)))) (g_gen (glabel g)))
            (spaces (ti_heap t_info)))) as C. 
    { eapply nth_In.  rewrite !combine_length in *. rewrite !nat_inc_list_length in *.  simpl in *. rep_lia. }
    specialize (A1 C). clear C.
    rewrite !combine_nth_lt in A1; try rep_lia.
    all: simpl in *; try rewrite !nat_inc_list_length; try rewrite !combine_length; try rewrite !nat_inc_list_length; try rep_lia. 
    injection B2. clear B2. intros. 
      rewrite !nat_inc_list_nth in *; try rep_lia. subst. 
      destruct A1 as (C1&C2&C3).
      destruct (Nat.eq_dec n to).
      + subst. rewrite <- H0, <- H1. split3. 
        *  rewrite !nth_indep with (d' := null_info) in *; try rep_lia. rewrite !nth_indep with (d' := null_space) in *; try rep_lia. 
           assert (A := add_node_heap_start). simpl in A. erewrite A. clear A. 
           rewrite <- C1. unfold copy_v_mod_gen_info_list.
           rewrite app_nth2. rewrite firstn_length_le.
           assert ((to - to = 0)%nat) as -> by rep_lia. 
           reflexivity.  
           all: try rep_lia. 
           rewrite firstn_length_le; try rep_lia.
           rewrite !LU in *.
          rewrite <- !ZtoNat_Zlength in B1. 
          rewrite !Zlength_upd_Znth in *. rep_lia. 
        * rewrite <- (Nat2Z.id to) at 3. 
          rewrite nth_Znth.
          rewrite upd_Znth_same. simpl. 
          rewrite !nth_indep with (d' := null_info). 
          rewrite nth_indep with (d' := null_space) in C2. rewrite <- C2. 
          rewrite cvmgil_eq. simpl. rewrite nth_indep with (d' := g_n). reflexivity. 
          all: try rep_lia. 
          --   rewrite !LU in *.
          rewrite <- !ZtoNat_Zlength in B1. 
          rewrite !Zlength_upd_Znth in *. rep_lia.
          --   rewrite !LU in *.
          rewrite <- !ZtoNat_Zlength in B1. 
          rewrite !Zlength_upd_Znth in *. rep_lia.
        * rewrite <- (Nat2Z.id to) at 5. 
          rewrite nth_Znth.
          rewrite upd_Znth_same. simpl.
          rewrite nth_indep with (d' := null_space) in C3. 
          rewrite <- C3. 
          assert (D := number_of_vertices_new). unfold nth_gen in D. 
          rewrite nth_indep with (d' := null_info). 
          simpl in D. rewrite D.
          rewrite pvs_S. rewrite add_node_previous_vertices_size.
          rewrite nth_indep with (d := g_n) (d' := null_info).
          f_equal. unfold vertex_size. simpl. unfold update_vlabel. if_tac; try congruence. 
          exfalso. apply H2. reflexivity.  
          all: try rep_lia; try eauto. 
          -- unfold closure_has_index. unfold nth_gen. rep_lia.
          -- rewrite !LU in *.
          rewrite <- !ZtoNat_Zlength in B1. 
          rewrite !Zlength_upd_Znth in *. rep_lia.
          -- rewrite !LU in *.
          rewrite <- !ZtoNat_Zlength in B1. 
          rewrite !Zlength_upd_Znth in *. rep_lia.
      + rewrite <- (Nat2Z.id n) in H0. 
        rewrite nth_Znth in H0.
        rewrite Znth_upd_Znth_diff in H0.
        rewrite <- nth_Znth in H0. rewrite Nat2Z.id in H0.
        assert (D := add_node_nth_gen). unfold nth_gen in D. simpl in D.
        rewrite nth_indep with (d' := null_info) in H1.
        rewrite D in H1. clear D. 
        rewrite nth_indep with (d' := g_n) in H1. 
        split3; try congruence. 
        rewrite <- H0, <- H1. rewrite <- C3. 
        rewrite add_node_previous_vertices_size. reflexivity. 
        all : eauto; try rep_lia. 
        * unfold closure_has_index. rewrite nth_indep with (d' := null_info).
         unfold nth_gen. rep_lia. rep_lia. 
        * rewrite !LU in *.
          rewrite <- !ZtoNat_Zlength in B1. 
          rewrite !Zlength_upd_Znth in *. rep_lia. 
        *  rewrite !LU in *.
          rewrite <- !ZtoNat_Zlength in B1. 
          rewrite !Zlength_upd_Znth in *. rep_lia. 
  - rewrite !Forall_forall in *.
    intros v B. eapply A2. rewrite <- !map_skipn in *. 
    rewrite !in_map_iff in *. destruct B as (sp&B1&B2). exists sp. split; eauto.
    destruct t_info; simpl in *. destruct ti_heap; simpl in *.
    rewrite !In_Znth_iff in *.
    destruct B2 as (i&B2&B3).
    exists i. split. 
    + rewrite !Zlength_solver.Zlength_skipn in *.
      rewrite Zlength_upd_Znth in *. rewrite LU in *. rep_lia. 
    + rewrite <- B3.
      rewrite <- (Nat2Z.id (Datatypes.length _)). 
      rewrite <- (Nat2Z.id (Datatypes.length (copy_v_mod_gen_info_list _ _))). 
      rewrite !Znth_skipn; try rep_lia. 
      unfold graph_has_gen in HH. 
      rewrite !upd_Znth_diff'; try rep_lia.
      * 
        do 3 f_equal. unfold copy_v_mod_gen_info_list.
       rewrite <- firstn_skipn with (l := g_gen (glabel g)) (n := to) at 1. 
       rewrite !app_length, !List.skipn_length. simpl. 
       rewrite List.skipn_length. rep_lia.
      * rewrite Zlength_correct. rep_lia. 
    - rewrite <- (ZtoNat_Zlength (spaces _)) . 
     rewrite <- (ZtoNat_Zlength (spaces _)) in A3. 
     rewrite !spaces_size in *. 
     simpl. rep_lia.  
Qed.


Lemma vvalid_pregraph_add_my_edge es g v:
  vvalid (fold_left pregraph_add_my_edge es g) v <-> vvalid g v. 
Proof.
  revert g.
  induction es; cbn; try reflexivity.
  intros g. rewrite IHes. reflexivity. 
Qed.

Lemma add_node_vvalid g to es v : 
  vvalid (pregraph_add_v g (new_copied_v g to) es) v <-> vvalid g v \/ v = new_copied_v g to. 
Proof.
  simpl. unfold pregraph_add_v. now rewrite vvalid_pregraph_add_my_edge.
Qed.

Lemma add_node_vertex_valid g to lb es : 
  graph_has_gen g to -> vertex_valid g -> vertex_valid (add_node g to lb es).
Proof.  
  unfold vertex_valid. intros T H v. simpl.
  rewrite add_node_vvalid. 
  simpl. rewrite <- add_node_graph_has_v; eauto. 
  rewrite H. reflexivity. 
Qed.

Lemma add_node_evalid g to es e: 
evalid (pregraph_add_v g (new_copied_v g to) es) e <-> ( evalid g e) \/ In e (map fst es). 
Proof.
  unfold pregraph_add_v.
  assert ( evalid g e <-> evalid  (pregraph_add_vertex g (new_copied_v g to)) e) as -> by (simpl; intuition).
  remember (pregraph_add_vertex g (new_copied_v g to)) as g'. clear Heqg'. revert g'. 
  induction es. 
  - simpl. intuition.
  - intros g'. simpl. rewrite IHes. simpl. unfold addValidFunc. intuition eauto.
Qed.

Lemma add_node_graph_has_e_full g to lb es e : 
  graph_has_gen g to ->
   edge_compatible g to lb es ->
  add_node_compatible g (new_copied_v g to) es -> 
  graph_has_e (add_node g to lb es) e <-> In e (map fst es) \/ ( graph_has_e g e).
Proof.
  intros G EC C. 
  split. 
  - intros H. eapply add_node_graph_has_e in H; eauto. intuition eauto.
  - unfold graph_has_e. unfold get_edges. unfold make_fields. intros [H|(H1&H2)].
    + assert (H' := H).
      rewrite In_map_fst_iff in H.
      destruct H as ((src&trg)&H).
      destruct (C _ _ _ H) as (C1&C2&C3&C4&C5). subst. rewrite !C1.  
      split. 
      * eapply add_node_graph_has_v; eauto. 
      * rewrite add_node_vlabel. eapply EC. eauto. 
    + split. eapply add_node_graph_has_v_impl; eauto. 
      rewrite add_node_vlabel_old. 
      eauto. 
      eapply graph_has_v_not_eq; eauto.
Qed.


Lemma add_node_edge_valid g to lb es : 
    graph_has_gen g to ->
   edge_compatible g to lb es ->
  add_node_compatible g (new_copied_v g to) es -> 
  edge_valid g -> edge_valid (add_node g to lb es). 
Proof. 
  unfold edge_valid. intros G EC C H e.
  simpl. rewrite add_node_evalid. 
  rewrite add_node_graph_has_e_full; eauto. rewrite H.
  intuition eauto.
Qed.

Lemma add_node_src_edge (g : graph) to lb es : 
  forall v, add_node_compatible g v es -> src_edge g -> src_edge (add_node g to lb es). 
Proof.
  unfold src_edge. intros v C A e.
  unfold add_node_compatible in C.
  destruct (ListDec.In_dec) with (l := map fst es) (a := e). 
  - eauto using E_EqDec.  
  - rewrite In_map_fst_iff in i. destruct i as ((src_e&trg)&H). 
    destruct (C _ _ _ H) as (C1&C2&C3&C4&C5&C6). simpl.
    erewrite add_node_src_new. 3: apply H. all: eauto.
  - simpl. rewrite <- add_node_src; eauto. 
Qed.

Lemma sound_gc_graph g to lb es: 
  graph_has_gen g to ->  edge_compatible g to lb es -> add_node_compatible g (new_copied_v g to) es -> sound_gc_graph g -> sound_gc_graph (add_node g to lb es).
Proof.
  unfold sound_gc_graph. intros A EC C (H1&H2&H3).
  split3.
  all: eauto using add_node_vertex_valid, add_node_edge_valid, add_node_src_edge. 
Qed.

Lemma add_node_copied_vertex_existence g to lb es: 
  copied_vertex lb = new_copied_v g to -> graph_has_gen g to -> copied_vertex_existence g -> copied_vertex_existence (add_node g to lb es). 
Proof.
  intros C G E v A.
  destruct (V_EqDec v (new_copied_v g to)).
  - rewrite e. simpl. 
    unfold update_vlabel. if_tac; try congruence.
  - unfold copied_vertex_existence in E.
    eapply add_node_graph_has_v in A; eauto. 
    destruct A; try congruence.  
    specialize (E _ H).  
    rewrite add_node_vlabel_old; eauto. 
    destruct E as (E1&E2). 
    split. 
    + rewrite add_node_graph_has_gen; eauto.
    + unfold gen_has_index. unfold gen_has_index in E2.
      assert (H' := number_of_vertices_increases g (vgeneration (copied_vertex (vlabel g v))) to lb es G). rep_lia.
Qed.

Lemma add_node_ti_size_spec (to : nat) (ti : GCGraph.thread_info) (off : Z) (H: 0 <= off <= total_space (nth_space ti to) - used_space (nth_space ti to)): 
  Z.of_nat to < Zlength (spaces (ti_heap ti)) -> ti_size_spec ti -> ti_size_spec (add_node_ti to ti off H) . 
Proof.
  intros ? A. unfold ti_size_spec in *. rewrite Forall_forall in *. 
  intros n B. specialize (A _ B). rewrite nat_inc_list_In_iff in B. unfold nth_gen_size_spec, nth_space in *. 
  rewrite <- add_node_heap_start_real with (H := H) in A; eauto. 
  simpl in *. if_tac; eauto.
  rewrite <- A.
  unfold gen_size, nth_space. rewrite <- add_node_heap_total_real with (H := H); eauto.
  all: rewrite spaces_size. all: rep_lia. 
Qed.


Lemma reachable_new (g : graph) v to (roots: roots_t): 
vertex_valid g -> path_lemmas.reachable_through_set g (filter_sum_right roots) v -> v <> new_copied_v g to. 
Proof.
  intros VV A. unfold path_lemmas.reachable_through_set in A.
  destruct A as (rt&A1&A2).
  eapply path_lemmas.reachable_foot_valid in A2.
  apply VV in A2.
  eauto using graph_has_v_not_eq.
Qed.

Definition disjoint_path (es : list (EType * (VType * VType)))  (p : VType * list EType) : Prop :=
  forall e, In e (snd p) -> ~ In e (map fst es). 

Lemma disjoint_path_cons v a p es : 
  disjoint_path es (v, a :: p) <-> ~ In a (map fst es) /\ disjoint_path es (v, p).
Proof.
  unfold disjoint_path. simpl. intuition eauto. 
  subst. eauto.
Qed.

Lemma add_node_path_pfoot g to es p: 
  disjoint_path es p ->  path_lemmas.pfoot (pregraph_add_v g (new_copied_v g to) es) p = path_lemmas.pfoot g p. 
Proof.
  intros D.
  destruct p as (v&p).
  simpl. 
  induction p; eauto. 
   rewrite disjoint_path_cons in D. destruct D as (D1&D2). 
  simpl in *. 
  destruct p; eauto. 
  rewrite <- add_node_dst; eauto. 
Qed.




Lemma add_node_valid_path (g : graph) to es p: 
  src_edge g -> vertex_valid g -> edge_valid g -> no_dangling_dst g -> disjoint_path es p -> fst p <> new_copied_v g to -> path_lemmas.valid_path (pregraph_add_v g (new_copied_v g to) es) p <-> path_lemmas.valid_path g p. 
Proof.
  intros SE VV EV ND A B. 
  destruct p as (v&p). simpl. destruct p; eauto. 
  - rewrite add_node_vvalid. intuition. 
  - (* rewrite disjoint_path_cons in A. destruct A as (A1&A2). *) rewrite <- add_node_src.
    + enough (v = src g e -> path_lemmas.valid_path' (pregraph_add_v g (new_copied_v g to) es) (e :: p) <->  path_lemmas.valid_path' g (e :: p)) by intuition.
      intros. subst. simpl in B.
      assert (e = hd e (e ::p)) by reflexivity.
      remember (e :: p) as p'.
      rewrite H in A, B. clear Heqp' H p.
      induction p'. 
      * reflexivity.  
      * simpl in *.
         rewrite disjoint_path_cons in A. destruct A as (A1&A2).
        assert (strong_evalid (pregraph_add_v g (new_copied_v g to) es) a <-> strong_evalid g a).
        { unfold strong_evalid. rewrite add_node_evalid, !add_node_vvalid, <- !add_node_src, <- !add_node_dst; eauto.
          intuition eauto.  subst. eauto. 
          unfold no_dangling_dst in ND. unfold vertex_valid in VV. rewrite VV. eapply ND.
          rewrite <- VV. eapply H0.
          unfold edge_valid in EV.
          rewrite EV in H1. unfold graph_has_e in H1. destruct H1.
          specialize (SE a). congruence. 
 }
        destruct p'; eauto. 
        rewrite H.    apply disjoint_path_cons in A2. 
        rewrite <- add_node_src, <- add_node_dst; eauto. 
        2 : intuition.         
        split. 
        -- intros (B1&B2&B3). rewrite IHp' in *; eauto.  
           ++ simpl. rewrite <- B2. unfold no_dangling_dst in ND. 
              unfold strong_evalid in B1. destruct B1 as (_&_&B1).
              unfold vertex_valid in *. rewrite VV in B1.
              intros C. eapply graph_has_v_not_eq; eauto.
           ++ simpl. eapply disjoint_path_cons; eauto. 
         -- intros (C1&C2&C3). rewrite IHp' in *; eauto. 
            ++ unfold strong_evalid in C1.  
               simpl. rewrite <- C2. 
               intros C. eapply graph_has_v_not_eq; eauto.
               unfold vertex_valid in *. rewrite <- VV. intuition.
            ++ simpl. apply disjoint_path_cons; eauto.
    + simpl in *. eapply A; eauto. 
      now left.
Qed.

Lemma add_node_path_prop g to es p : 
path_lemmas.path_prop (pregraph_add_v g (new_copied_v g to) es) (fun _ : VType => True) p  <-> path_lemmas.path_prop g (fun _ : VType => True) p. 
Proof.
  unfold path_lemmas.path_prop.
  reflexivity. 
Qed.

Lemma add_node_good_path (g : graph) to es p: 
   src_edge g -> vertex_valid g -> edge_valid g -> no_dangling_dst g -> fst p <> new_copied_v g to -> disjoint_path es p -> path_lemmas.good_path (pregraph_add_v g (new_copied_v g to) es)
         (fun _ : VType => True) p <->  path_lemmas.good_path g (fun _ : VType => True) p.
Proof.
  intros.
  simpl. unfold path_lemmas.good_path.
  rewrite add_node_path_prop, add_node_valid_path; eauto.
  reflexivity. 
Qed.

Lemma add_node_path_ends g to es p s v : 
   disjoint_path es p -> path_lemmas.path_ends (pregraph_add_v g (new_copied_v g to) es) p s v <-> path_lemmas.path_ends g p s v.
Proof.
  intros.
  unfold path_lemmas.path_ends.
  simpl. rewrite add_node_path_pfoot; eauto. reflexivity.  
Qed.

Lemma add_node_reachable (g : graph) to es s v (roots: roots_t): 
  s <> new_copied_v g to -> add_node_compatible g (new_copied_v g to) es -> (forall e, In e es -> snd (snd e) <> new_copied_v g to) ->  src_edge g -> vertex_valid g -> edge_valid g -> no_dangling_dst g ->  path_lemmas.reachable (pregraph_add_v g (new_copied_v g to) es) s v <-> path_lemmas.reachable g s v. 
Proof.
  unfold path_lemmas.reachable, path_lemmas.reachable_by. unfold path_lemmas.reachable_by_path. 
  intros NC EE SE VV EV ND.
  split; intros (p&H1&H2); exists p.
  - destruct p as (vp&p). 
     assert (vp <> new_copied_v g to).
    { destruct H1. simpl in *. subst.  eauto. } 
    assert (  disjoint_path es (vp, p)). 
    { unfold disjoint_path. simpl. 
      intros e P A.
      rewrite In_map_fst_iff in A. destruct A as ((src&trg)&A).
      destruct (EE _ _ _ A) as (E1&E2&E3&E4&E5&E6). subst.
      destruct H1. simpl in *. subst. destruct H2. clear NC H2.
      revert s H0 H1. induction p; intros. 
      - inversion P.  
      - simpl in P. destruct P. 
           (*
         I know that this doesn't start with the new node (NC).
         I know that no edge - neither in the orignal graph, nor in es, leads to the new node.
         But all edges in es start with the new node.
         So for the new node to be in the path, the path has to be start with it.
     *)     
        + subst. simpl in H1.
          destruct H1. subst. 
          enough (strong_evalid (pregraph_add_v g (new_copied_v g to) es) e).
          2 : { destruct p; intuition. } 
          clear H2. destruct H1 as (H1&H2&H3). rewrite <- VV in E1.
          erewrite add_node_src_new in H0; try eapply A; eauto.
          congruence. 
        + eapply path_lemmas.valid_path_cons_iff in H1.   
          destruct H1 as (D1&D2&D3).
          eapply IHp; try eapply D3; eauto.
          destruct ListDec.In_dec with (l := map fst es) (a := a). eauto using E_EqDec.
          * rewrite In_map_fst_iff in i. destruct i as ((src_a&trg_a)&i).
            erewrite add_node_dst_new; try apply i; eauto.
            destruct (EE _ _ _ i). intuition. 
          * rewrite <- add_node_dst in *; eauto.  
            intros C. unfold no_dangling_dst in H. unfold strong_evalid in D2. 
            eapply graph_has_v_not_eq. 2: apply C.  
            eapply H with (v := src g a). 
            -- unfold vertex_valid in EV. rewrite <- EV. 
               destruct D2 as (D21&D22&D23). rewrite add_node_vvalid in D22. 
               destruct D22. 
               ++ rewrite <- add_node_src in H1; eauto. 
               ++ congruence.
            -- unfold edge_valid in *. unfold graph_has_e in ND.
               destruct D2 as (D21&D22&D23). 
               rewrite add_node_evalid in D21. destruct D21; try contradiction.
               eapply ND in H1. rewrite VV. intuition. }
    rewrite add_node_path_ends in *; rewrite add_node_good_path in *; eauto.
    - destruct p as (vp&p). 
     assert (vp <> new_copied_v g to).
    { destruct H1. simpl in *. subst.  eauto. } 

    assert (  disjoint_path es (vp, p)). 
    {  unfold disjoint_path. simpl. 
      intros e P A.
      rewrite In_map_fst_iff in A. destruct A as ((src&trg)&A).
      destruct (EE _ _ _ A) as (E1&E2&E3&E4&E5). subst.
      destruct H1. simpl in *. subst.
      destruct H2. 
      assert (B := path_lemmas.valid_path_strong_evalid _ _ _ _ H1 P) .
      destruct B as (B1&B2&B3). rewrite <- VV in E1. rewrite E1 in B2. 
      eapply graph_has_v_not_eq. 2 : reflexivity. 
      unfold vertex_valid in *. rewrite <- EV. eauto. 
 }    
   rewrite add_node_path_ends; eauto. rewrite add_node_good_path in *; eauto.
Qed.

Lemma add_node_reachable_through_set (g : graph) to es (roots : roots_t) v: 
   roots_graph_compatible roots g -> src_edge g -> vertex_valid g -> edge_valid g -> no_dangling_dst g ->   add_node_compatible g (new_copied_v g to) es ->  path_lemmas.reachable_through_set (pregraph_add_v g (new_copied_v g to) es) (filter_sum_right roots) v <-> path_lemmas.reachable_through_set g (filter_sum_right roots) v.   
Proof.
  unfold path_lemmas.reachable_through_set. intros R SE VV EV ND C.  simpl.
  assert (forall e, In e es -> snd (snd e) <> new_copied_v g to). 
  { intros (e&(src&trg)) H. simpl. 
    destruct (C _ _ _ H) as (C1&C2&C3&C4&C5&C6). subst. 
    intros D. subst. eapply graph_has_v_not_eq; eauto. }   
   split; intros (s&H1&H2); exists s; split; eauto.
  - assert (s <> new_copied_v g to). 
    { unfold roots_graph_compatible in R. rewrite Forall_forall in R.
      specialize (R _ H1). intros D. eapply graph_has_v_not_eq; eauto. } 
     eapply add_node_reachable; eauto.
  - assert (s <> new_copied_v g to). 
    { unfold roots_graph_compatible in R. rewrite Forall_forall in R.
      specialize (R _ H1). intros D. eapply graph_has_v_not_eq; eauto. } 
     eapply add_node_reachable; eauto. 
Qed.

Lemma add_node_subgraph_vvalid g (roots : roots_t) to lb es: 
   roots_graph_compatible roots g -> src_edge g ->  
 vertex_valid g -> edge_valid g -> no_dangling_dst g ->forall v : VType,
     add_node_compatible g (new_copied_v g to) es ->
  vvalid (subgraph2.reachable_sub_labeledgraph g (filter_sum_right roots)) v <->
  vvalid
    (subgraph2.reachable_sub_labeledgraph (add_node g to lb es) (filter_sum_right roots))
    (id v). 
Proof.
  intros R SE C VV EV ND v. simpl. unfold predicate_vvalid.
  rewrite add_node_vvalid.
  rewrite add_node_reachable_through_set; eauto. intuition.
  exfalso. eapply reachable_new; eauto. 
Qed. 

Lemma add_node_compatible_vvalid (g: graph) (roots: roots_t) to : 
  vertex_valid g ->  ~ vvalid (subgraph2.reachable_sub_labeledgraph g (filter_sum_right roots)) (new_copied_v g to). 
Proof.
  intros VV H. unfold vertex_valid in VV.
  assert (~ vvalid g (new_copied_v g to)). 
  { rewrite VV. intros C. eapply graph_has_v_not_eq; eauto. }
  eapply H0. simpl in H. 
  unfold predicate_vvalid in H. apply H.
Qed.

Lemma add_node_compatible_evalid (g: graph) (roots : roots_t) e to (es: list (EType * (VType * VType))): 
   src_edge g -> add_node_compatible g (new_copied_v g to) es -> vertex_valid g -> edge_valid g -> evalid (subgraph2.reachable_sub_labeledgraph g (filter_sum_right roots)) e ->  ~ In e (map fst es). 
Proof.
  intros SE C VV EV A1 A2. unfold vertex_valid in VV. unfold edge_valid in EV.
  rewrite In_map_fst_iff in A2. destruct A2 as ((src&trg)&A2). 
  destruct (C _ _ _ A2) as (C1&C2&C3&C4&C5).
  subst. simpl in A1. unfold predicate_evalid in A1. destruct A1 as (A11&A12&A13).
  eapply path_lemmas.reachable_through_set_foot_valid in A12.
  rewrite VV in A12. rewrite SE in A12.  rewrite C1 in A12. eapply graph_has_v_not_eq.  apply A12. eauto. 
Qed.

Lemma add_node_subgraph_evalid (g : graph) (roots: roots_t) to lb es : 
   roots_graph_compatible roots g -> src_edge g -> add_node_compatible g (new_copied_v g to) es -> vertex_valid g -> edge_valid g -> no_dangling_dst g ->
  forall e : EType,
  evalid (subgraph2.reachable_sub_labeledgraph g (filter_sum_right roots)) e <->
  evalid
    (subgraph2.reachable_sub_labeledgraph (add_node g to lb es) (filter_sum_right roots))
    (id e). 
Proof.
  intros RC SE C VV EV ND e. simpl. unfold predicate_evalid. 
  rewrite add_node_evalid. 
  rewrite !add_node_reachable_through_set; eauto.
   destruct (ListDec.In_dec) with (l := map fst es) (a := e). 
   - eauto using E_EqDec.
   - rewrite In_map_fst_iff in i. destruct i as ((srcn&trg)&i).
     destruct (C _ _ _ i) as (C1&C2&C3&C4&C5&C6).
    rewrite (add_node_dst_new _ _ _ _ _ _ C5 i).
    rewrite (add_node_src_new _ _ _ _ _ _ C5 i).
        assert (src g e = srcn) as ->. 
    { rewrite  SE. eauto. }
    split. 
    + intuition eauto.
    apply path_lemmas.reachable_through_set_foot_valid in H. 
    exfalso. eapply graph_has_v_not_eq. 2 : eapply C1. 
    subst. unfold vertex_valid in VV. rewrite <- VV. eauto. 
    + intros (?&H&?). 
       apply path_lemmas.reachable_through_set_foot_valid in H. 
    exfalso. eapply graph_has_v_not_eq. 2 : eapply C1. 
    subst. unfold vertex_valid in VV. rewrite <- VV. eauto. 
    - rewrite <- !add_node_src; eauto.
    rewrite <- add_node_dst; eauto. 
    intuition eauto. 
Qed.
     

Lemma add_node_iso roots (g : graph) to lb es: 
  roots_graph_compatible roots g ->  add_node_compatible g (new_copied_v g to) es -> src_edge g -> vertex_valid g -> edge_valid g -> no_dangling_dst g -> add_node_compatible g (new_copied_v g to) es -> ~ In (inr (new_copied_v g to)) roots -> gc_graph_iso g roots (add_node g to lb es) roots.
Proof.
  intros R AC SE VV EV ND C ROOTS.
  unfold gc_graph_iso. exists id, id, id, id. 
  split. 
  - now rewrite root_map_id, map_id. 
  - simpl. split. 
    + split. all: eauto using Coqlib.bijective_refl. 
      * intros. apply add_node_subgraph_vvalid; eauto.  
      * intros. rewrite add_node_subgraph_vvalid; eauto.  
      * intros. apply add_node_subgraph_evalid; eauto.  
      * intros. rewrite add_node_subgraph_evalid; eauto. 
      * intros. simpl. rewrite <- add_node_src; eauto.
        eauto using add_node_compatible_evalid. 
         * intros. simpl. rewrite <- add_node_dst; eauto.
           eauto using add_node_compatible_evalid.
     + intros v H. simpl. unfold update_vlabel. if_tac; try eauto. 
       exfalso. eapply add_node_compatible_vvalid; eauto. rewrite H0. eapply H. 
     + intros.  reflexivity. 
Qed.


