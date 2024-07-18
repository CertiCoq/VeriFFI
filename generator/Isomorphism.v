(* General proofs of isomorphism for graph predicates 

KS: This file contains general definitions and proofs to enable 
automatic isomorphism proofs.
*)


Require Import ZArith.
Require Import Psatz.
Require Import CertiGraph.CertiGC.spatial_gcgraph.
Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Lists.List
               Coq.Lists.ListSet.
Require Export CertiGraph.CertiGC.GCGraph.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad
               ExtLib.Data.String.

Require Import VeriFFI.generator.gen_utils.
Require Import VeriFFI.library.base_representation.
Require Import VeriFFI.library.meta.

Import ListNotations.

Lemma in_graph_reachable {X} {In_X : GraphPredicate X} {g} {outliers} {p} {x : X} {roots} : 
(forall g outliers n v, graph_predicate g outliers n (repNode v) -> graph_has_v g v)
-> vertex_valid g  -> 
graph_predicate g outliers x p
-> In p roots
-> match p with
| repNode v' => path_lemmas.reachable_through_set 
  (CertiGraph.graph.graph_model.pg_lg g)
   (CertiGraph.lib.List_ext.filter_sum_right (map roots_rep_type roots)) v'
| _ => True
end.
Proof. 
Set Printing All.
intros has_v VV. intros.
destruct p; eauto.
exists v. split. 
+ rewrite <- CertiGraph.lib.List_ext.filter_sum_right_In_iff. 
  rewrite in_map_iff.  exists (repNode v).
  split; eauto.
+ apply path_lemmas.reachable_refl. apply VV.
eapply has_v.  eapply H.
Qed.

Lemma reachable_suc (g : LGraph) v roots n m:
(n < m) %nat->
In (v, n) (get_edges g v) ->
vertex_valid g ->
no_dangling_dst g ->
src_edge ((CertiGraph.graph.graph_model.pg_lg g)) ->
edge_valid g ->
graph_has_v g v ->
path_lemmas.reachable_through_set (graph_model.pg_lg g) 
       (List_ext.filter_sum_right (map roots_rep_type roots)) v ->
path_lemmas.reachable_through_set (graph_model.pg_lg g)
  (List_ext.filter_sum_right (map roots_rep_type roots)) (graph_model.dst (graph_model.pg_lg g) 
  (v, n%nat)).
Proof.
intros lt_n_m Hl VV ND src_edge EV H H0. 
eapply path_lemmas.reachable_through_set_step. 
2 : eapply H0. 
-- (* Showing that dst is valid *) 
destruct H0 as (v_root & H01 & H02).
eapply path_lemmas.reachable_foot_valid.
eapply path_lemmas.reachable_trans. 
exact H02. 
eapply path_lemmas.reachable_path_edge_in with (p := (v, [(v, n%nat)])).
  ++ econstructor.
  ** unfold path_lemmas.path_ends. simpl. split; reflexivity.
  ** unfold path_lemmas.good_path. split. 
    --- unfold path_lemmas.valid_path. split; try reflexivity.
    simpl. rewrite src_edge. reflexivity.
    unfold path_lemmas.valid_path'. 
    unfold graph_model.strong_evalid.
    split; try split. 
    +++ apply EV. unfold graph_has_e. 
      split; eauto. 
    +++ rewrite src_edge. simpl. apply VV. assumption.
    +++ eapply VV. eapply ND; eauto.
    --- unfold path_lemmas.path_prop. intuition eauto. simpl. 
    econstructor; eauto.
  ++ simpl. intuition eauto.
  -- eapply graph_model.out_edges_step. 
      unfold graph_model.out_edges.
      rewrite src_edge. split; try reflexivity. 
      apply EV. unfold graph_has_e.
      split; eauto.
Qed.  


Lemma iso_graph_has_v (g g': LGraph) vmap12 vmap21 emap12 emap21 v (roots: list rep_type) (roots' : roots_t) : 
vertex_valid g -> vertex_valid g' ->
path_lemmas.reachable_through_set (graph_model.pg_lg g)
  (List_ext.filter_sum_right (map roots_rep_type roots)) v ->
graph_isomorphism.label_preserving_graph_isomorphism_explicit
        (subgraph2.reachable_sub_labeledgraph g (List_ext.filter_sum_right (map roots_rep_type roots)))
        (subgraph2.reachable_sub_labeledgraph g' (List_ext.filter_sum_right roots')) vmap12 vmap21 emap12
        emap21
-> graph_has_v g v ->
graph_has_v g' (vmap12 v). 
Proof. 
  intros VV VG'. intros. 
  assert (vvalid_v : graph_model.vvalid ( CertiGraph.graph.graph_model.pg_lg(subgraph2.reachable_sub_labeledgraph g 
    (CertiGraph.lib.List_ext.filter_sum_right (map roots_rep_type roots)))) v).
      { simpl. unfold predicate_vvalid. split. 
      unfold vertex_valid in VV. eapply VV. assumption.
        eauto. } 
      eapply graph_isomorphism.vvalid_bij in vvalid_v.
       2 : eapply H0.
      unfold vertex_valid in *. rewrite <- VG'. 
      simpl in vvalid_v. unfold predicate_vvalid in vvalid_v. 
      eapply vvalid_v.
Qed.

Lemma vlabel_vmap (g g' : LGraph) vmap12  vmap21 emap12 emap21 v (roots : list rep_type) (roots': roots_t ): 
vertex_valid g ->
graph_isomorphism.label_preserving_graph_isomorphism_explicit
        (subgraph2.reachable_sub_labeledgraph g (List_ext.filter_sum_right (map roots_rep_type roots)))
        (subgraph2.reachable_sub_labeledgraph g' (List_ext.filter_sum_right roots')) vmap12 vmap21 emap12
        emap21 ->
        graph_has_v g v ->
        path_lemmas.reachable_through_set (graph_model.pg_lg g)
  (List_ext.filter_sum_right (map roots_rep_type roots)) v ->
graph_model.vlabel g v =
graph_model.vlabel g' (vmap12 v).
Proof. 
intros.
assert (graph_model.vlabel g v = graph_model.vlabel ((subgraph2.reachable_sub_labeledgraph g
(CertiGraph.lib.List_ext.filter_sum_right (map roots_rep_type roots)))) v)
as -> by reflexivity.
erewrite graph_isomorphism.vlabel_iso; try apply H0.  reflexivity. 
simpl. unfold predicate_vvalid. split. 
- apply H. eauto. 
- eauto.
Qed.


Lemma reachable_id g v ps roots p' t: 
vertex_valid g ->
no_dangling_dst g ->
src_edge ((CertiGraph.graph.graph_model.pg_lg g)) ->
edge_valid g ->
graph_has_v g v ->
path_lemmas.reachable_through_set (graph_model.pg_lg g) 
       (List_ext.filter_sum_right (map roots_rep_type roots)) v ->
match graph_model.vlabel g v with
                   | {| raw_mark := raw_mark; raw_fields := raws; raw_color := raw_color; raw_tag := k |} =>
                       if raw_mark
                       then False
                       else
                        match raw_color with
                        | 0%Z => k = Z.of_N t /\ base_representation.compatible g v 0 raws ps
                        | _ => False
                        end
                   end ->

In p' ps ->
match p' with
| repNode v' =>
    path_lemmas.reachable_through_set (graph_model.pg_lg g)
      (List_ext.filter_sum_right (map roots_rep_type roots)) v'
| _ => True
end.
Proof. 
intros.
destruct (graph_model.vlabel g v) eqn: Hl.
destruct raw_mark; try contradiction. 
destruct raw_color; try contradiction.
destruct H5 as (raw_tag_eq&compatible_g).
destruct p'; try eauto.
assert (exists x n', field_rep g v n' x = repNode v0 /\ In (v, n') (get_edges g v)) as (x&n'&H'&H''). 
{ unfold get_edges. unfold make_fields. rewrite Hl. simpl.
clear - compatible_g H6. 
  induction compatible_g. 
  - inversion H6. 
  - destruct H6. 
    + exists x. exists n. 
      split; eauto. congruence.
      subst. apply List_ext.filter_sum_right_In_iff.
      simpl in *. destruct x.
      destruct s; simpl in *; try congruence.
      left. reflexivity. 
    + destruct (IHcompatible_g H0) as (x'&n'&H1&H2).
     exists x'. exists n'. split; eauto. 
     apply List_ext.filter_sum_right_In_iff. 
     apply List_ext.filter_sum_right_In_iff in H2.
     simpl. replace (n+1) with (S n) by lia. destruct x. destruct s. now right. now right. now right. 
 }
  destruct x; eauto. 
  * destruct s; simpl in *; try congruence.
  * simpl in H'. inversion H'.
  eapply reachable_suc; eauto.
Qed.

Require Import Coq.Program.Equality.

Lemma compatible_length g v n xs ys: 
  base_representation.compatible g v n xs ys -> length xs = length ys. 
Proof. 
  induction 1; eauto. 
  simpl. eauto. 
Qed.

Lemma make_fields'_In : 
forall (l : list (option (Z + GC_Pointer))) v n m , 
       nth_error l m = Some None -> In (inr (v, (m + n))) (make_fields' l v n).
Proof.
 clear. intros l. induction l; intros; eauto. 
     - destruct m; simpl in H; congruence. 
     - simpl in *. destruct m; try eauto. 
       + simpl in *. inversion H. subst. now left. 
       + simpl in H. specialize (IHl v (n + 1) m H).
       replace (m + (n + 1)) with (S m + n) in IHl  by lia.
        destruct a; eauto. 
        * destruct s; eauto. 
          -- right; eauto.
          -- right; eauto. 
        * right; eauto. 
  Qed.

Lemma compatible_lift g v ps g' vmap12 vmap21 emap12 emap21 (roots : list rep_type) : 
base_representation.compatible g v 0 (raw_fields (graph_model.vlabel g v)) ps  ->
src_edge ((CertiGraph.graph.graph_model.pg_lg g)) ->
src_edge ((CertiGraph.graph.graph_model.pg_lg g')) ->
vertex_valid g ->
edge_label_same g -> 
edge_label_same g' ->
edge_valid g ->
no_dangling_dst g ->
graph_has_v g v ->
graph_isomorphism.label_preserving_graph_isomorphism_explicit
        (subgraph2.reachable_sub_labeledgraph g (List_ext.filter_sum_right (map roots_rep_type roots)))
        (subgraph2.reachable_sub_labeledgraph g'
           (List_ext.filter_sum_right (map (root_map vmap12) (map roots_rep_type roots)))) vmap12 vmap21
        emap12 emap21 ->
path_lemmas.reachable_through_set (graph_model.pg_lg g)
  (List_ext.filter_sum_right (map roots_rep_type roots)) v ->
 base_representation.compatible g' (vmap12 v) 0 (raw_fields (graph_model.vlabel g v)) (map (meta.lift vmap12) ps).
Proof. 
intros H2 src_edge src_edge' VV ELS ELS' EV ND  has_g_v H12 R.

pose (n := length (raw_fields (graph_model.vlabel g v)) - length ps).
assert (0 = n) as H. 
{ subst n. eapply compatible_length in H2. lia. }
assert (raw_fields (graph_model.vlabel g v) = skipn n (raw_fields (graph_model.vlabel g v))) as H0.
{ rewrite <- H. reflexivity.  }
rewrite H0. rewrite H0 in H2. clear H0.
rewrite H. rewrite H in H2. clear H.

subst n.
induction ps. 

- simpl in *.
  inversion H2. simpl. constructor. 

- simpl in *. inversion H2. subst. simpl.
remember ( Datatypes.length (raw_fields (graph_model.vlabel g v)) - S (Datatypes.length ps)) as n.
assert (Datatypes.length (raw_fields (graph_model.vlabel g v)) - Datatypes.length ps = S n).
{ clear - Heqn H2 H3 H.
eapply compatible_length in H3.

  
subst n. 
rewrite <- Nat.sub_succ_l. reflexivity.
remember (raw_fields (graph_model.vlabel g v)) as ys. 
assert (Datatypes.length (x :: xs) = Datatypes.length (skipn (Datatypes.length ys - S (Datatypes.length ps)) ys)).
rewrite H. reflexivity.
simpl in H0. rewrite skipn_length in H0. lia.  
 }
rewrite H0 in IHps.
assert (xs = skipn (S n) ((raw_fields (graph_model.vlabel g v)))).
{ symmetry. eapply MCList.skipn_n_Sn; eauto. }
rewrite H1.

constructor. 
  + simpl.
  eapply IHps. rewrite <- H1. assumption. 
  +  unfold lift. 
  

 simpl.
  unfold field_rep. 
  destruct x eqn:H_x; try eauto. 
++ eauto.  destruct s; eauto.  
++ 
assert (In_edge: In (v, n) (get_edges g (fst (v, n)))). 
{ 
  simpl. unfold get_edges. unfold make_fields.
  eapply List_ext.filter_sum_right_In_iff.

  clear - H. remember ((raw_fields (graph_model.vlabel g v))) as ys.
  clear Heqys.
  assert (exists ys1, length ys1 = n /\ ys = ys1 ++ None :: xs).
 { rewrite <- (firstn_skipn n ys).
   exists (firstn n ys). split. 
   - eapply firstn_length_le.
   assert (Datatypes.length (None :: xs) = Datatypes.length (skipn n ys)).
   rewrite <- H. reflexivity.
   simpl in H0. rewrite skipn_length in H0. lia. 
  -  rewrite <- H. reflexivity.
  }

  destruct H0. destruct H0. subst. 
  replace (Datatypes.length x) with (Datatypes.length x + 0) by lia.
  eapply make_fields'_In.
  replace (Datatypes.length x) with (Datatypes.length x + 0) by lia.
  rewrite List_ext.nth_error_app.
  reflexivity. }

assert (evalid_suc: predicate_evalid (graph_model.pg_lg g)
(path_lemmas.reachable_through_set (graph_model.pg_lg g)
  (List_ext.filter_sum_right (map roots_rep_type roots))) (v, n%nat)).
  {   
  split; try split. 
     +++ apply EV. unfold graph_has_e. 
       split; eauto.      

     +++ rewrite src_edge. simpl. eauto.
     +++ eapply reachable_suc; eauto. }  

unfold edge_label_same in ELS. 
f_equal. 
destruct H12.
destruct lp_pregraph_iso. simpl in *. simpl in *.
rewrite dst_bij.
f_equal. 
assert (vmap12 v = fst (emap12 (v, n%nat))). 
{ rewrite <- src_edge'. 
 rewrite <- src_bij.
 rewrite src_edge. reflexivity.
 eauto. }
assert (n%nat = snd (emap12 (v, n%nat))).
{ rewrite <- ELS'. rewrite <- elabel_iso. rewrite ELS. reflexivity.
eauto. }
destruct (emap12 (v, n%nat)).
cbn in *. congruence.
eauto.
Qed.

Lemma graph_cRep_iso v vmap12 vmap21 emap12 emap21 g g' 
(roots : list rep_type) (roots': roots_t )  t n ps : 
vertex_valid g -> vertex_valid g' ->
src_edge ((CertiGraph.graph.graph_model.pg_lg g)) ->
src_edge ((CertiGraph.graph.graph_model.pg_lg g')) ->
roots' = map (root_map vmap12) (map roots_rep_type roots) ->
edge_label_same g -> 
edge_label_same g' ->
edge_valid g ->
no_dangling_dst g ->
path_lemmas.reachable_through_set (graph_model.pg_lg g)
  (List_ext.filter_sum_right (map roots_rep_type roots)) v -> 
graph_isomorphism.label_preserving_graph_isomorphism_explicit
(subgraph2.reachable_sub_labeledgraph g (List_ext.filter_sum_right (map roots_rep_type roots)))
(subgraph2.reachable_sub_labeledgraph g' (List_ext.filter_sum_right roots')) vmap12 vmap21 emap12
emap21 ->
Datatypes.length ps = N.to_nat n ->
graph_cRep g (repNode v) (boxed t n) ps ->
graph_cRep g' (meta.lift vmap12 (repNode v)) (boxed t n) (map (meta.lift vmap12 ) ps). 
Proof. 
intros VV VV' src_edge src_edge' Roots ELS ELS' EV ND R ISO L C. 
destruct C as (_&has_v_g&in_graph_surface).
split; eauto; try split. 
- simpl. rewrite map_length. eauto. 
- eapply iso_graph_has_v; try eapply has_v_g; eauto.
- assert (LB:  graph_model.vlabel g v = graph_model.vlabel g' (vmap12 v)) 
by (eapply vlabel_vmap; eauto).
 rewrite <- LB .
 destruct (graph_model.vlabel g v) as [raw_mark ? ? raw_color ? ? ? ? ?] eqn:Hl .
 destruct raw_mark; try contradiction .
 destruct raw_color; try contradiction. 
 intuition. 
  assert (raw_fields = GCGraph.raw_fields (graph_model.vlabel g v)).
  { rewrite Hl. reflexivity. }
  rewrite H1. 
  eapply compatible_lift; try eapply ISO; eauto.
  rewrite Hl. eauto. subst. eauto.  
Qed.

(** ** *)


(** ** Tactics *)

Ltac prove_ps_1 g roots outliers H12 vmap12 x H p := 
    let p' := fresh "p'" in 
    let in_graph_p' := fresh "in_graph_p'" in 
    let H22 := fresh "H22" in 
    destruct H as (p'&in_graph_p'&H22); 

    let z := fresh "z" in 
    let o := fresh "o" in 
    let v := fresh "v" in 
    let H_p := fresh "H_p" in 
    destruct p as [z | o | v] eqn: H_p; try contradiction ; 

    assert (reachable_p g roots p') by (
    let has_v_ := fresh "has_v_g" in 
    let in_graph_surface := fresh "in_graph_surface" in 
    destruct H22 as (_&has_v_g&in_graph_surface) ;
    eapply reachable_id; eauto; repeat constructor);
    
    exists (meta.lift vmap12 p'); split ; 
    [  (* now *) first [now (
      match goal with
      | [IH: forall (p: rep_type), meta.graph_predicate g outliers x p -> _ -> _  |- _ ] =>    
      apply IH end; eauto) | 
      now (match goal with
      | [  |- @meta.graph_predicate ?T _ _ _ _ _ ] => eapply (@meta.gc_preserved T ltac:(auto with typeclass_instances)); eauto; split; eauto
      end) | 
      match goal with
    | [ H: context [@graph_predicate ?T _ _ _ _ _] |- @graph_predicate ?T _ _ _ _ _ ] =>
      eapply H; eauto; split; eauto
    end
      ] 
      
      | eapply (graph_cRep_iso) with (n := 1%N) (ps := [p']); try eapply H12; eauto
    ].


    Ltac prove_ps_2 g roots outliers H12 vmap12 x H p := 
      let p1' := fresh "p1'" in 
      let p2' := fresh "p2'" in 
      let in_graph_p1' := fresh "in_graph_p1''" in 
      let in_graph_p2' := fresh "in_graph_p2''" in 
      let H22 := fresh "H22" in 
    
      (* specific *) destruct H as (p1'&p2'&in_graph_p1'&in_graph_p2'&H22); 
    
      let z := fresh "z" in 
      let o := fresh "o" in 
      let v := fresh "v" in 
      let H_p := fresh "H_p" in 
      destruct p as [z | o | v] eqn: H_p; try contradiction;
    
    (* specific *) assert (reachable_p g roots p1') by (
      let has_v_ := fresh "has_v_g" in 
      let in_graph_surface := fresh "in_graph_surface" in 
    destruct H22 as (_&has_v_g&in_graph_surface);
    eapply reachable_id; simpl; eauto; simpl; eauto);
    assert (reachable_p g roots p2') by (
      let has_v_ := fresh "has_v_g" in 
      let in_graph_surface := fresh "in_graph_surface" in 
    destruct H22 as (_&has_v_g&in_graph_surface);
    eapply reachable_id; simpl; eauto; simpl; eauto);
    
    exists (meta.lift vmap12 p1'); 
    (* specific *) exists (meta.lift vmap12 p2'); 
    
    repeat (split; [  (first [now (
      match goal with
      | [IH: forall (p: rep_type), meta.graph_predicate g outliers x p -> _ -> _  |- _ ] =>    
      apply IH end; eauto) 
      | 
      now (match goal with
      | [  |- @meta.graph_predicate ?T _ _ _ _ _ ] => eapply (@meta.gc_preserved T ltac:(auto with typeclass_instances)); eauto; split; eauto
      end) | 
      match goal with
        | [ H: context [@graph_predicate ?T _ _ _ _ _] |- @graph_predicate ?T _ _ _ _ _ ] =>
          eapply H; eauto; split; eauto
        end
      ] ) | ]);
    
      (* specific *)
      eapply (graph_cRep_iso) with (n := 2%N) (ps := [p1'; p2']); try eapply H12; eauto.

Ltac prove_ps_3 g roots outliers H12 vmap12 x H p := 
  let p1' := fresh "p1'" in 
  let p2' := fresh "p2'" in 
  let p3' := fresh "p3'" in 
  let in_graph_p1' := fresh "in_graph_p1''" in 
  let in_graph_p2' := fresh "in_graph_p2''" in 
  let in_graph_p3' := fresh "in_graph_p3''" in 
  let H22 := fresh "H22" in 

(* specific *) destruct H as (p1'&p2'&p3'&in_graph_p1'&in_graph_p2'&in_graph_p3'&H22); 
destruct p as [z | o | v] eqn: H_p; try contradiction;

(* specific *) assert (reachable_p g roots p1') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p2') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p3') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);

exists (meta.lift vmap12 p1'); 
(* specific *) exists (meta.lift vmap12 p2'); 
exists (meta.lift vmap12 p3'); 

repeat (split; [  (first [now (
match goal with
| [IH: forall (p: rep_type), meta.graph_predicate g outliers x p -> _ -> _  |- _ ] =>    
apply IH end; eauto) 
| 
now (match goal with
| [  |- @meta.graph_predicate ?T _ _ _ _ _ ] => eapply (@meta.gc_preserved T ltac:(auto with typeclass_instances)); eauto; split; eauto
end) | match goal with
| [ H: context [@graph_predicate ?T _ _ _ _ _] |- @graph_predicate ?T _ _ _ _ _ ] =>
  eapply H; eauto; split; eauto
end ] ) | ]);

(* specific *)
eapply (graph_cRep_iso) with (n := 3%N) (ps := [p1'; p2'; p3']); try eapply H12; eauto.

Ltac prove_ps_4 g roots outliers H12 vmap12 x H p := 
  let p1' := fresh "p1'" in 
  let p2' := fresh "p2'" in 
  let p3' := fresh "p3'" in 
  let p4' := fresh "p4'" in 
  let in_graph_p1' := fresh "in_graph_p1''" in 
  let in_graph_p2' := fresh "in_graph_p2''" in 
  let in_graph_p3' := fresh "in_graph_p3''" in 
  let in_graph_p4' := fresh "in_graph_p4''" in 
  let H22 := fresh "H22" in 

(* specific *) destruct H as (p1'&p2'&p3'&p4'&
in_graph_p1'&in_graph_p2'&in_graph_p3'&in_graph_p4'&H22); 
destruct p as [z | o | v] eqn: H_p; try contradiction;

(* specific *) assert (reachable_p g roots p1') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p2') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p3') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p4') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);

(* specific *)
exists (meta.lift vmap12 p1'); 
 exists (meta.lift vmap12 p2'); 
exists (meta.lift vmap12 p3'); 
exists (meta.lift vmap12 p4'); 

repeat (split; [  (first [now (
match goal with
| [IH: forall (p: rep_type), meta.graph_predicate g outliers x p -> _ -> _  |- _ ] =>    
apply IH end; eauto) 
| 
now (match goal with
| [  |- @meta.graph_predicate ?T _ _ _ _ _ ] => eapply (@meta.gc_preserved T ltac:(auto with typeclass_instances)); eauto; split; eauto
end) | match goal with
| [ H: context [@graph_predicate ?T _ _ _ _ _] |- @graph_predicate ?T _ _ _ _ _ ] =>
  eapply H; eauto; split; eauto
end ] ) | ]);

(* specific *)
eapply (graph_cRep_iso) with (n := 4%N) (ps := [p1'; p2'; p3'; p4']); try eapply H12; eauto.

Ltac prove_ps_5 g roots outliers H12 vmap12 x H p := 
  let p1' := fresh "p1'" in 
  let p2' := fresh "p2'" in 
  let p3' := fresh "p3'" in 
  let p4' := fresh "p4'" in 
  let p5' := fresh "p5'" in 
  let in_graph_p1' := fresh "in_graph_p1''" in 
  let in_graph_p2' := fresh "in_graph_p2''" in 
  let in_graph_p3' := fresh "in_graph_p3''" in 
  let in_graph_p4' := fresh "in_graph_p4''" in 
  let in_graph_p5' := fresh "in_graph_p5''" in 
  let H22 := fresh "H22" in 

(* specific *) destruct H as (p1'&p2'&p3'&p4'&p5'&
in_graph_p1'&in_graph_p2'&in_graph_p3'&in_graph_p4'&in_graph_p5'&H22); 
destruct p as [z | o | v] eqn: H_p; try contradiction;

(* specific *) assert (reachable_p g roots p1') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p2') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p3') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p4') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p5') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto 10; simpl; eauto 10);

(* specific *)
exists (meta.lift vmap12 p1'); 
 exists (meta.lift vmap12 p2'); 
exists (meta.lift vmap12 p3'); 
exists (meta.lift vmap12 p4'); 
 exists (meta.lift vmap12 p5'); 

repeat (split; [  (first [now (
match goal with
| [IH: forall (p: rep_type), meta.graph_predicate g outliers x p -> _ -> _  |- _ ] =>    
apply IH end; eauto) 
| 
now (match goal with
| [  |- @meta.graph_predicate ?T _ _ _ _ _ ] => eapply (@meta.gc_preserved T ltac:(auto with typeclass_instances)); eauto; split; eauto
end) | match goal with
| [ H: context [@graph_predicate ?T _ _ _ _ _] |- @graph_predicate ?T _ _ _ _ _ ] =>
  eapply H; eauto; split; eauto
end ] ) | ]);

(* specific *)
eapply (graph_cRep_iso) with (n := 5%N) (ps := [p1'; p2'; p3'; p4'; p5']); try eapply H12; eauto.

Ltac prove_ps_6 g roots outliers H12 vmap12 x H p := 
  let p1' := fresh "p1'" in 
  let p2' := fresh "p2'" in 
  let p3' := fresh "p3'" in 
  let p4' := fresh "p4'" in 
  let p5' := fresh "p5'" in 
  let p6' := fresh "p6'" in 
  let p7' := fresh "p7'" in 
  let p8' := fresh "p8'" in 
  let in_graph_p1' := fresh "in_graph_p1''" in 
  let in_graph_p2' := fresh "in_graph_p2''" in 
  let in_graph_p3' := fresh "in_graph_p3''" in 
  let in_graph_p4' := fresh "in_graph_p4''" in 
  let in_graph_p5' := fresh "in_graph_p5''" in 
  let in_graph_p6' := fresh "in_graph_p6''" in 
  let in_graph_p7' := fresh "in_graph_p7''" in 
  let in_graph_p8' := fresh "in_graph_p8''" in 
  let H22 := fresh "H22" in 

(* specific *) destruct H as (p1'&p2'&p3'&p4'&p5'&p6'&
in_graph_p1'&in_graph_p2'&in_graph_p3'&in_graph_p4'&in_graph_p5'&in_graph_p6'&H22); 
destruct p as [z | o | v] eqn: H_p; try contradiction;

(* specific *) assert (reachable_p g roots p1') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p2') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p3') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p4') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p5') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto 10; simpl; eauto 10);
assert (reachable_p g roots p6') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto 10; simpl; eauto 10);

(* specific *)
exists (meta.lift vmap12 p1'); 
 exists (meta.lift vmap12 p2'); 
exists (meta.lift vmap12 p3'); 
exists (meta.lift vmap12 p4'); 
 exists (meta.lift vmap12 p5'); 
exists (meta.lift vmap12 p6'); 

repeat (split; [  (first [now (
match goal with
| [IH: forall (p: rep_type), meta.graph_predicate g outliers x p -> _ -> _  |- _ ] =>    
apply IH end; eauto) 
| 
now (match goal with
| [  |- @meta.graph_predicate ?T _ _ _ _ _ ] => eapply (@meta.gc_preserved T ltac:(auto with typeclass_instances)); eauto; split; eauto
end) | match goal with
| [ H: context [@graph_predicate ?T _ _ _ _ _] |- @graph_predicate ?T _ _ _ _ _ ] =>
  eapply H; eauto; split; eauto
end ] ) | ]);

(* specific *)
eapply (graph_cRep_iso) with (n := 6%N) (ps := [p1'; p2'; p3'; p4'; p5'; p6']); try eapply H12; eauto.

Ltac prove_ps_7 g roots outliers H12 vmap12 x H p := 
  let p1' := fresh "p1'" in 
  let p2' := fresh "p2'" in 
  let p3' := fresh "p3'" in 
  let p4' := fresh "p4'" in 
  let p5' := fresh "p5'" in 
  let p6' := fresh "p6'" in 
  let p7' := fresh "p7'" in 
  let in_graph_p1' := fresh "in_graph_p1''" in 
  let in_graph_p2' := fresh "in_graph_p2''" in 
  let in_graph_p3' := fresh "in_graph_p3''" in 
  let in_graph_p4' := fresh "in_graph_p4''" in 
  let in_graph_p5' := fresh "in_graph_p5''" in 
  let in_graph_p6' := fresh "in_graph_p6''" in 
  let in_graph_p7' := fresh "in_graph_p7''" in 
  let H22 := fresh "H22" in 

(* specific *) destruct H as (p1'&p2'&p3'&p4'&p5'&p6'&p7'&
in_graph_p1'&in_graph_p2'&in_graph_p3'&in_graph_p4'&in_graph_p5'&in_graph_p6'&in_graph_p7'&H22); 
destruct p as [z | o | v] eqn: H_p; try contradiction;

(* specific *) assert (reachable_p g roots p1') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p2') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p3') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p4') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p5') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto 10; simpl; eauto 10);
assert (reachable_p g roots p6') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto 10; simpl; eauto 10);
assert (reachable_p g roots p7') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto 10; simpl; eauto 10);

(* specific *)
exists (meta.lift vmap12 p1'); 
 exists (meta.lift vmap12 p2'); 
exists (meta.lift vmap12 p3'); 
exists (meta.lift vmap12 p4'); 
 exists (meta.lift vmap12 p5'); 
exists (meta.lift vmap12 p6'); 
exists (meta.lift vmap12 p7'); 

repeat (split; [  (first [now (
match goal with
| [IH: forall (p: rep_type), meta.graph_predicate g outliers x p -> _ -> _  |- _ ] =>    
apply IH end; eauto) 
| 
now (match goal with
| [  |- @meta.graph_predicate ?T _ _ _ _ _ ] => eapply (@meta.gc_preserved T ltac:(auto with typeclass_instances)); eauto; split; eauto
end) | match goal with
| [ H: context [@graph_predicate ?T _ _ _ _ _] |- @graph_predicate ?T _ _ _ _ _ ] =>
  eapply H; eauto; split; eauto
end ] ) | ]);

(* specific *)
eapply (graph_cRep_iso) with (n := 7%N) (ps := [p1'; p2'; p3'; p4'; p5'; p6'; p7']); try eapply H12; eauto.

Ltac prove_ps_8 g roots outliers H12 vmap12 x H p := 
  let p1' := fresh "p1'" in 
  let p2' := fresh "p2'" in 
  let p3' := fresh "p3'" in 
  let p4' := fresh "p4'" in 
  let p5' := fresh "p5'" in 
  let p6' := fresh "p6'" in 
  let p7' := fresh "p7'" in 
  let p8' := fresh "p8'" in 
  let in_graph_p1' := fresh "in_graph_p1''" in 
  let in_graph_p2' := fresh "in_graph_p2''" in 
  let in_graph_p3' := fresh "in_graph_p3''" in 
  let in_graph_p4' := fresh "in_graph_p4''" in 
  let in_graph_p5' := fresh "in_graph_p5''" in 
  let in_graph_p6' := fresh "in_graph_p6''" in 
  let in_graph_p7' := fresh "in_graph_p7''" in 
  let in_graph_p8' := fresh "in_graph_p8''" in 
  let H22 := fresh "H22" in 

(* specific *) destruct H as (p1'&p2'&p3'&p4'&p5'&p6'&p7'&p8'&
in_graph_p1'&in_graph_p2'&in_graph_p3'&in_graph_p4'&in_graph_p5'&in_graph_p6'&in_graph_p7'&in_graph_p8'&H22); 
destruct p as [z | o | v] eqn: H_p; try contradiction;

(* specific *) assert (reachable_p g roots p1') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p2') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p3') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p4') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto; simpl; eauto);
assert (reachable_p g roots p5') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto 10; simpl; eauto 10);
assert (reachable_p g roots p6') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto 10; simpl; eauto 10);
assert (reachable_p g roots p7') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto 10; simpl; eauto 10);
assert (reachable_p g roots p8') by (
  let has_v_ := fresh "has_v_g" in 
  let in_graph_surface := fresh "in_graph_surface" in 
destruct H22 as (_&has_v_g&in_graph_surface);
eapply reachable_id; simpl; eauto 10; simpl; eauto 10);

(* specific *)
exists (meta.lift vmap12 p1'); 
 exists (meta.lift vmap12 p2'); 
exists (meta.lift vmap12 p3'); 
exists (meta.lift vmap12 p4'); 
 exists (meta.lift vmap12 p5'); 
exists (meta.lift vmap12 p6'); 
exists (meta.lift vmap12 p7'); 
 exists (meta.lift vmap12 p8'); 

repeat (split; [  (first [now (
match goal with
| [IH: forall (p: rep_type), meta.graph_predicate g outliers x p -> _ -> _  |- _ ] =>    
apply IH end; eauto) 
| 
now (match goal with
| [  |- @meta.graph_predicate ?T _ _ _ _ _ ] => eapply (@meta.gc_preserved T ltac:(auto with typeclass_instances)); eauto; split; eauto
end) | match goal with
| [ H: context [@graph_predicate ?T _ _ _ _ _] |- @graph_predicate ?T _ _ _ _ _ ] =>
  eapply H; eauto; split; eauto
end ] ) | ]);

(* specific *)
eapply (graph_cRep_iso) with (n := 8%N) (ps := [p1'; p2'; p3'; p4'; p5'; p6'; p7'; p8']); try eapply H12; eauto.



(* Tactic to solve the isomorphism goal in case there are no IHs *)
Ltac iso_no_IH p :=
  destruct p; simpl in *; try contradiction; eauto.
