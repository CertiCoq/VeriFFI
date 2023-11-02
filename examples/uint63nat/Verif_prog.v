Require Import VeriFFI.examples.uint63nat.prog.

Require Import ZArith.
Require Import Psatz.

Require Import VeriFFI.verification.specs_general.

Require Import VeriFFI.generator.Rep.

Obligation Tactic := gen.
MetaCoq Run (gen_for nat).
MetaCoq Run (gen_for bool).

MetaCoq Run (desc_gen S).

Require Import VST.floyd.proofauto.
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

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := [alloc_make_Coq_Init_Datatypes_nat_S_spec].

(* BEGIN delete this in the next VST release that has Ltac prove_cs_preserve_type *)
Ltac prove_cs_preserve_type := 
reflexivity || 
lazymatch goal with |- cs_preserve_type ?a ?b ?CCE ?t = true =>
 tryif is_evar CCE 
 then fail 2 "Before using change_compspecs, define an Instance of change_composite_env"
 else tryif unify (cs_preserve_type a b CCE t) false
 then let id := constr:(match t with Tstruct i _ => Some i | Tunion i _ => Some i | _ => None end) in 
      let id := eval hnf in id in 
      lazymatch id with 
      | None => fail 2 "change_compspecs fails because the two compspecs environments disagree on the definition of type" t "(that is," 
a "versus" b ")"
      | Some ?id' => let ca := constr:(@get_co a id') in
               let cb := constr:(@get_co b id') in
               let ca := eval hnf in ca in
               let cb := eval hnf in cb in
               fail 2 "change_compspecs fails because the two compspecs environments disagree on the definition of type" t
                 ". That is," a "claims" ca "while" b "claims" cb
       end
 else fail
end.

Ltac change_compspecs' cs cs' ::=
  lazymatch goal with
  | |- context [@data_at cs' ?sh ?t ?v1] => erewrite (@data_at_change_composite cs' cs _ sh t); [| apply JMeq_refl | prove_cs_preserve_type]
  | |- context [@field_at cs' ?sh ?t ?gfs ?v1] => erewrite (@field_at_change_composite cs' cs _ sh t gfs); [| apply JMeq_refl | prove_cs_preserve_type]
  | |- context [@data_at_ cs' ?sh ?t] => erewrite (@data_at__change_composite cs' cs _ sh t); [| prove_cs_preserve_type]
  | |- context [@field_at_ cs' ?sh ?t ?gfs] => erewrite (@field_at__change_composite cs' cs _ sh t gfs); [| prove_cs_preserve_type]
  | |- _ => 
    match goal with 
  | |- context [?A cs'] => 
     idtac "Warning: attempting change_compspecs on user-defined mpred:" A;
         change (A cs') with (A cs)
  | |- context [?A cs' ?B] => 
     idtac "Warning: attempting change_compspecs on user-defined mpred:" A;
         change (A cs' B) with (A cs B)
  | |- context [?A cs' ?B ?C] => 
     idtac "Warning: attempting change_compspecs on user-defined mpred:" A;
         change (A cs' B C) with (A cs B C)
  | |- context [?A cs' ?B ?C ?D] => 
     idtac "Warning: attempting change_compspecs on user-defined mpred:" A;
         change (A cs' B C D) with (A cs B C D)
  | |- context [?A cs' ?B ?C ?D ?E] => 
     idtac "Warning: attempting change_compspecs on user-defined mpred:" A;
         change (A cs' B C D E) with (A cs B C D E)
  | |- context [?A cs' ?B ?C ?D ?E ?F] => 
     idtac "Warning: attempting change_compspecs on user-defined mpred:" A;
         change (A cs' B C D E F) with (A cs B C D E F)
   end
 end.
(* END delete this in the next VST release that has Ltac prove_cs_preserve_type *)

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
| xs: args (ctor_reified _), H0: in_graphs _ (ctor_reified _) ?xs' ?ps  |- _ =>
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

Ltac start_function' := 
  start_function1; 
  repeat (simple apply intro_prop_through_close_precondition; intro);
  concretize_PARAMS;
  start_function2;
  start_function3.

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
    destruct (glabel g) eqn: glabel_g.
    destruct g_gen; try congruence.
    unfold gc_condition_prop in *. destruct gc_cond as (gc1&gc2&gc3&gc4&gc5&gc6&gc7).
    unfold graph_heap_compatible in gc6.
    destruct gc6 as (gc61&gc62&gc63).
    simpl in *. rewrite !glabel_g in gc61. simpl in *.
    rewrite !SPACE_NONEMPTY in *.
    apply Forall_inv in gc61. destruct gc61 as (?&?&?).
    destruct g1; simpl in *.
    split3; eauto; congruence.
Qed.

Set Nested Proofs Allowed. (* from proofs_library_general.v *)


Lemma add_node_copy_compatible:
 forall g (v := new_copied_v g 0 : VType) flds R1 R2 R3 es,
 copy_compatible g ->
 copy_compatible (add_node g 0 (newRaw v 0 flds R1 R2 R3) es).
Proof.
intros.
hnf; intros.
hnf in H.
apply add_node_graph_has_v in H0; [ | apply graph_has_gen_O].
destruct H0.
-
assert (v0 <> new_copied_v g 0). {
 apply graph_has_v_not_eq; auto.
}
rewrite add_node_vlabel_old in *; auto.
split.
apply add_node_graph_has_v;  [apply graph_has_gen_O | ].
destruct (H _ H0 H1).
auto.
apply H; auto.
-
subst.
rewrite add_node_vlabel in *; auto.
split.
apply add_node_graph_has_v;  [apply graph_has_gen_O | ].
right.
simpl.
reflexivity.
inv H1.
Qed.

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
  | repOut v' => In v' outlier
  | _ => True
  end
->
gc_condition_prop g t_info roots outlier -> gc_condition_prop g' t_info' roots outlier.
Proof.
  intros. unfold gc_condition_prop in *. unfold g'.
  assert ( add_node_compatible g (new_copied_v g 0) es).
  { unfold add_node_compatible. intros. subst es. destruct p; inversion H2.
    - injection H3. intros. subst. simpl.
      destruct H0.
      decompose [and] H1; clear H1.
      split3; auto. split3; auto. lia. split; auto. repeat constructor. intro Hx; inv Hx.
    - inversion H3. }
  assert (  edge_compatible g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es).
  { unfold edge_compatible. intros. simpl. destruct p; simpl; intuition eauto. }
    decompose [and] H1; clear H1.
      repeat simple apply conj.
  all: eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_thread_compatible, add_node_ti_size_spec, add_node_roots_compatible.
  + eapply add_node_ti_size_spec; eauto.  rewrite spaces_size.   rep_lia.
  + eapply add_node_outlier_compatible; eauto. (* Print rep_field. *)  simpl.
    destruct p eqn:Hp; hnf; simpl; intros; try contradiction; eauto.
    destruct H12; try contradiction; subst; auto.
     destruct H1; try contradiction. subst g0. auto.
  + apply add_node_copy_compatible; auto.
Qed.

Compute reptype thread_info_type.
Compute reptype env_graph_gc.space_type.


Lemma unfold_for_allocation:
 forall (g: graph) (t_info: GCGraph.thread_info) (roots: roots_t)
    (outlier: outlier_t) (ti: val) (sh: share)
 (HEADROOM: 1 < total_space (heap_head (ti_heap t_info))
                 - used_space (heap_head (ti_heap t_info))),

let heap := ti_heap t_info in
let g0 := heap_head heap in 
let space := total_space g0 - used_space g0 in
let alloc := offset_val (WORD_SIZE * used_space g0) (space_start g0) in
let limit := offset_val (WORD_SIZE * total_space g0) (space_start g0) in
full_gc g t_info roots outlier ti sh |--
!! (gc_condition_prop g t_info roots outlier /\
     ~In (inr (new_copied_v g 0)) roots /\
     spaces heap = g0 :: tl (spaces heap) /\
     isptr (space_start g0) /\
     writable_share (space_sh g0) /\
     generation_space_compatible g (0%nat, nth_gen g 0, g0)) &&
 spatial_gcgraph.frames_rep sh (ti_frames t_info) *
  (spatial_gcgraph.outlier_rep outlier *
   @data_at env_graph_gc.CompSpecs sh thread_info_type 
        (alloc, (limit, (ti_heap_p t_info, 
         (ti_args t_info, (spatial_gcgraph.ti_fp t_info, 
       (Vptrofs (ti_nalloc t_info),nullval)))))) ti *
   spatial_gcgraph.heap_struct_rep sh
     ((space_start g0, (Vundef, (limit,limit))) :: 
        map spatial_gcgraph.space_tri (tl (spaces heap)))
     (ti_heap_p t_info) *
   @data_at_ env_graph_gc.CompSpecs (space_sh g0) (tarray int_or_ptr_type (total_space g0 - used_space g0))
     (offset_val (WORD_SIZE * used_space g0) (space_start g0)) *
   iter_sepcon.iter_sepcon (tl (spaces heap)) (@space_rest_rep env_graph_gc.CompSpecs) *
   spatial_gcgraph.ti_token_rep (ti_heap t_info) (ti_heap_p t_info) *
   spatial_gcgraph.graph_rep g).
Proof.
intros.
  unfold full_gc, before_gc_thread_info_rep. Intros.
  rename H into gc_cond.

  (** General properties *)
(*  assert (graph_has_gen_0 := graph_has_gen_O g). *)
  assert (~ In (inr (new_copied_v g 0)) roots)
    as ROOTS_IN
    by (eapply new_node_roots; eapply gc_cond).
  fold heap.
  destruct (heap_head_cons heap)
    as (g0'&space_rest&SPACE_NONEMPTY&g0_eq).
  subst g0'. fold g0.
  assert (space_rest = tl (spaces heap)) by (rewrite SPACE_NONEMPTY; reflexivity).
  subst space_rest.
  assert (isptr (space_start g0) /\  writable_share (space_sh g0) /\ generation_space_compatible g (0%nat, nth_gen g 0, g0)) as (isptr_g0&wsh_g0&comp_g0) by (subst; eapply spaces_g0; eauto).
  unfold spatial_gcgraph.before_gc_thread_info_rep.
  unfold spatial_gcgraph.heap_rest_rep. rewrite SPACE_NONEMPTY. simpl.
  fold g0.
(*   unfold space_rest_rep at 1.*)
  replace spatial_gcgraph.space_rest_rep with space_rest_rep
  by (unfold space_rest_rep, spatial_gcgraph.space_rest_rep; extensionality sp;
      change_compspecs CompSpecs; reflexivity).
  entailer!!.
  fold heap.
  rewrite SPACE_NONEMPTY.
  simpl.
  replace (@space_rest_rep env_graph_gc.CompSpecs)
   with (@space_rest_rep CompSpecs)
  by (unfold space_rest_rep, spatial_gcgraph.space_rest_rep; extensionality sp;
      change_compspecs CompSpecs; reflexivity).
  fold g0. fold limit.
  cancel.
  unfold space_rest_rep.
  rewrite if_false by (intro H0; rewrite H0 in isptr_g0; simpl in *; contradiction).
  change_compspecs CompSpecs.
  cancel.
Qed.

Fixpoint upd_first_n' {A} (n: Z) (al bl: list A) :=
 match al with
 | a::al' => let n' := Z.pred n in upd_Znth n' (upd_first_n' n' al' bl) a
 | nil => bl
 end.

Definition upd_first_n {A} (al bl: list A) :=
  upd_first_n' (Zlength al) (rev al) bl.

Ltac create_upd_first_n := 
 match goal with |- context [upd_Znth 0 ?bl ?h] =>
  change (upd_Znth 0 bl h) with (upd_first_n' 1%Z [h] bl)
 end;
 repeat
   match goal with |- context [upd_Znth ?i (upd_first_n' ?j ?al ?bl) ?a]
     => constr_eq i j;
        let i1 := constr:(Z.succ i) in let i1 := eval compute in i1 in 
        change (upd_Znth i (upd_first_n' j al bl) a) with
              (upd_first_n' i1 (a::al) bl)
   end;
  change (upd_first_n' _ ?al ?bl) with (upd_first_n (rev al) bl).

Lemma delete_LOCAL_from_ENTAIL:
 forall Delta P i v Q R X,
   ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- X ->
   ENTAIL Delta, PROPx P (LOCALx (temp i v :: Q) (SEPx R)) |-- X.
Proof.
intros.
intro rho; destruct (H rho); split; auto.
clear H.
intro m; specialize (derivesI m).
intro.
apply derivesI; clear derivesI.
destruct H as [? [? [? ? ] ] ]; split3; auto.
split; auto.
simpl in H1.
destruct H1; auto.
Qed.

Lemma upd_first_n_app:
 forall {A} `{INH: Inhabitant A} (al bl: list A),
   Zlength al <= Zlength bl ->
   upd_first_n al bl = al ++ sublist (Zlength al) (Zlength bl) bl.
Proof.
intros.
unfold upd_first_n.
rewrite <- (rev_involutive al) at 3.
rewrite <- (Zlength_rev _ al) in H.
rewrite <- rev_append_rev.
rewrite <- Zlength_rev.
rewrite Zlength_correct.
set (al' := rev al) in *; clearbody al'; clear al; rename al' into al.
revert bl H; induction al; intros.
simpl.
rewrite sublist_same by lia; auto.
simpl Datatypes.length.
rewrite Zlength_cons in H.
rewrite inj_S.
simpl.
rewrite Z.pred_succ.
rewrite IHal by lia; clear IHal.
rewrite <- !Zlength_correct.
rewrite !rev_append_rev.
rewrite upd_Znth_app2.
rewrite Zlength_rev. rewrite Z.sub_diag.
f_equal.
rewrite (sublist_split (Zlength al) (Z.succ (Zlength al))) by rep_lia.
rewrite upd_Znth_app1 by list_solve.
rewrite sublist_one by list_solve.
simpl.
reflexivity.
rewrite !Zlength_rev.
Zlength_solve.
Qed.

Lemma tl_sublist: forall {A} (al: list A),
  tl al = sublist 1 (Zlength al) al.
Proof.
intros.
unfold sublist.
rewrite Zlength_correct, Nat2Z.id.
destruct al; simpl; auto.
rewrite firstn_exact_length; auto.
Qed.


Lemma data_at_int_or_ptr_long:
 forall {CS: compspecs} sh i p,
  data_at sh int_or_ptr_type (Vlong i) p
  = data_at sh tulong (Vlong i) p.
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
Compute reptype thread_info_type.

Lemma alloc_finish: forall
 (g : graph)
 (pl : list rep_type)
 (x : nat) 
 (roots : roots_t) 
 (sh : share) 
 (ti : val) 
 (outlier : outlier_t) 
 (t_info : GCGraph.thread_info)
 (H : Forall (@is_in_graph nat _ g x) pl)
 (heap := (ti_heap t_info : heap) : heap)
 (g0 := (heap_head heap : space) : space)
 (space := total_space g0 - used_space g0 : Z)
 (N := length pl : nat)
 (HEADROOM : Z.of_nat N < space)
 (RECORD_SIZE_BOUND: 0 < Z.of_nat N < Z.pow 2 54)
 (gc_cond : gc_condition_prop g t_info roots outlier)
 (ROOTS_IN : ~In (inr (new_copied_v g 0)) roots)
 (SPACE_NONEMPTY : spaces heap = g0 :: tl (spaces heap))
 (isptr_g0 : isptr (space_start g0))
 (comp_g0 : generation_space_compatible g (0%nat, nth_gen g 0, g0))
 (alloc := offset_val (WORD_SIZE * used_space g0) (space_start g0) : val)
 (FC : field_compatible (tarray int_or_ptr_type space) [] alloc)
 (vl := Vlong (Int64.repr (1024 * Z.of_nat N)) :: map (rep_type_val g) pl : list val)
 (limit := offset_val (WORD_SIZE * total_space g0) (space_start g0) : val),
spatial_gcgraph.outlier_rep outlier
  * (data_at sh thread_info_type
       (offset_val
          (WORD_SIZE * used_space g0 + sizeof int_or_ptr_type * Z.succ (Z.of_nat N))
          (space_start g0), (limit, (ti_heap_p t_info, (ti_args t_info,
             (spatial_gcgraph.ti_fp t_info, 
                   (Vptrofs (ti_nalloc t_info),nullval)))))) ti
       * (spatial_gcgraph.heap_struct_rep sh
            ((space_start g0, (Vundef, (limit, limit)))
             :: map spatial_gcgraph.space_tri (tl (spaces heap))) 
            (ti_heap_p t_info)
            * (data_at (space_sh g0) (tarray int_or_ptr_type space)
                 (upd_first_n vl (default_val (tarray int_or_ptr_type space))) alloc
                 * (msl.iter_sepcon.iter_sepcon space_rest_rep (tl (spaces heap))
                      * (spatial_gcgraph.ti_token_rep (ti_heap t_info) (ti_heap_p t_info) * spatial_gcgraph.graph_rep g)))))
|-- EX (a : rep_type) (a0 : graph) (a1 : GCGraph.thread_info),
    !! (@is_in_graph nat _ a0 (ctor_reflected desc (x; tt)) a /\
        gc_graph_iso g roots a0 roots /\
        offset_val (WORD_SIZE * used_space g0 + sizeof int_or_ptr_type * 1)
          (space_start g0) = rep_type_val a0 a) && full_gc a0 a1 roots outlier ti sh.
Proof.
intros.
rewrite upd_first_n_app
 by (subst vl N;
      unfold default_val; simpl; rewrite Zlength_Zrepeat by lia;
       simpl; rewrite Zlength_cons, Zlength_map, Zlength_correct; lia).
assert (LEN_N: Zlength vl = Z.succ (Z.of_nat N))
  by (subst vl; rewrite Zlength_cons, Zlength_map, Zlength_correct; lia).
change (default_val (tarray int_or_ptr_type space))
  with (Zrepeat Vundef space).
rewrite (split2_data_at_Tarray_app (Zlength vl)) by list_simplify.
rewrite Zlength_Zrepeat by lia.
  rewrite Z.mul_succ_r.
  change (sizeof int_or_ptr_type) with WORD_SIZE.
  assert (H_uneq: Forall (fun p => match p with | repNode v => v <> new_copied_v g 0 | _ => True end) pl). {
    clear - H. induction H; constructor; auto. destruct x0; try reflexivity.
       intros ->. pose proof (@has_v nat _ g x (new_copied_v g 0) H).
    eapply graph_has_v_not_eq; eauto. }
   pose (v := new_copied_v g 0).
   Exists (repNode v).
   assert (R1 : 0 <= 0 < 256) by lia.
   assert (R2 : 0 < Zlength (map rep_field pl) < two_power_pos 54). {
          clear - RECORD_SIZE_BOUND. subst N. 
          rewrite Zlength_map. rewrite two_power_pos_equiv. rewrite Zlength_correct. assumption.
   } 
   assert (R3 : NO_SCAN_TAG <= 0 -> ~ In None (map rep_field pl)). rewrite NO_SCAN_TAG_eq. lia.
   pose (make_es := fix make_es (i: Z) (l: list (rep_type)) := 
          match l with
          | repNode v' :: l' => ((v, Z.to_nat i), (v,v')) :: make_es (Z.succ i) l'
          | _ :: l' => make_es (Z.succ i) l'
          | nil => nil
          end).
   pose (es := make_es 0 pl).
   assert (NODUP: NoDup (map fst es)). {
     clear - es. subst es. clearbody v. set (i := 0).
     assert (0<=i) by lia. clearbody i.
     revert i H; induction pl; simpl; intros. constructor.
     destruct a; try (apply IHpl; lia).
     constructor; try (apply IHpl; lia).
     simpl. intro. set (j := Z.succ i) in H0. assert (i<j) by lia. clearbody j.
      clear - H H0 H1. revert j H0 H1; induction pl; intros; auto.
      destruct a; try (apply IHpl in H0; auto; lia).
      destruct H0. inv H0. lia.
      apply IHpl in H0; auto; lia.
    } 
    Exists (add_node g 0 (newRaw v 0 (map rep_field pl) R1 R2 R3) es).

  assert (t_size: 0 <= 2 <= total_space (nth_space (ti_heap t_info) 0) - used_space (nth_space (ti_heap t_info) 0)). {
    pose proof heap_head_cons.
    destruct (heap_head_cons (ti_heap t_info)) as [s [l [H8' H9' ] ] ].
    unfold nth_space.
      subst s. rewrite H8'. simpl. fold heap. fold g0. subst space; lia.
  }
    pose (t_info' := graph_add.add_node_ti 0 t_info _ t_size).
    Exists t_info'.

  assert (add_node_compatible g (new_copied_v g 0) es).
    { unfold add_node_compatible.
     intros * Hx. subst es v.
     clear - H_uneq H Hx NODUP.
     match goal with |- ?a /\ ?b /\ ?c /\ ?d /\ ?e /\ ?f =>
          assert (H0: a /\ b /\ c /\ d /\ f); [ clear NODUP | clear - H0 NODUP; tauto ]
     end.
     set (i := 0) in Hx. assert (0 <= i) by lia. clearbody i.
     revert i H0 Hx; induction H; intros; inv H_uneq. contradiction.
     destruct x0; try destruct Hx as [?|Hx];
     try solve [destruct (IHForall H5 (Z.succ i) ltac:(lia) Hx) as [? [? [? [? ?] ] ] ]; auto].
     inv H2. split3; auto. split3; auto.
     apply has_v with x; auto.
     unfold new_copied_v. simpl; lia.
    }
    clear NODUP.

    entailer!;     clear H7 H8 H6 H5 H4 H3 H2.
  - split3.
    + (** In this new graph, we have (S n) at position v with our predicate. *)
      evar (p: rep_type).
      exists p.
      change (is_in_graph (add_node g 0 (newRaw v 0 (map rep_field pl) R1 R2 R3) es) x p /\
       graph_cRep (add_node g 0 (newRaw v 0 (map rep_field pl) R1 R2 R3) es) (repNode v) (boxed 0 1) [p]).

      split.
      *  admit. (*  eapply is_monotone; eauto. apply graph_has_gen_O. *)
      * split3.
        -- reflexivity.
        -- split.
           ++ rewrite add_node_graph_has_gen; eauto; apply graph_has_gen_O.
           ++ apply add_node_has_index_new; eauto; apply graph_has_gen_O.
        -- rewrite add_node_vlabel.
           simpl. intuition eauto. repeat constructor.
Print compatible.
           destruct p as [| |p_v] eqn:?H; try reflexivity.
           simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (v, 0%nat)); congruence.
  red.
Search graph_predicate.
red.
unfold in_graph_pred.
simpl.

Print graph_predicate.
red.
red.

 red. simpl.
      * apply (@is_monotone _ Rep_nat); eauto; apply graph_has_gen_O.
      * unfold graph_cRep. intuition.
        -- split.
           ++ rewrite add_node_graph_has_gen; eauto; apply graph_has_gen_O.
           ++ apply add_node_has_index_new; eauto; apply graph_has_gen_O.
        -- rewrite add_node_vlabel.
           simpl. intuition eauto. repeat constructor.
           destruct p as [| |p_v]; try reflexivity.
           simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (v, 0%nat)); congruence.
    + destruct gc_cond. unfold gc_correct.sound_gc_graph, roots_compatible in *. intuition eauto. apply add_node_iso; eauto.
    + destruct comp_g0 as (C1&C2&C3).
      simpl. unfold vertex_address, vertex_offset.
      simpl. f_equal.
      * fold heap; fold g0. rewrite <- C3.
        assert (previous_vertices_size g 0 (number_of_vertices (nth_gen g 0)) = previous_vertices_size (add_node g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es) 0
     (number_of_vertices (nth_gen g 0))) as ->.
        { unfold previous_vertices_size, vertex_size_accum. unfold vertex_size.
          apply fold_left_ext. intros. rewrite add_node_vlabel_old. reflexivity.
          unfold GCGraph.nat_inc_list in H2. unfold new_copied_v.
          rewrite nat_seq_In_iff in H2. intros A. injection A. rep_lia. }
        assert (WORD_SIZE = 8) as -> by reflexivity; rep_lia.
      * rewrite add_node_gen_start; eauto; try apply graph_has_gen_O.
        unfold gen_start. if_tac. eauto. contradiction H2; apply graph_has_gen_O.
  - unfold full_gc.
    Intros. entailer!;     clear H7 H8 H6 H5 H4 H2.
    { eapply add_node_gc_condition_prop; try apply graph_has_gen_O; eauto. destruct p; 
       intuition (eauto using has_v).
        clear - H. exfalso.
       induction x; simpl. contradiction. destruct H as[p [? ? ] ]. contradiction.
     }

    (** Names *)

    unfold before_gc_thread_info_rep. Intros.
    unfold heap_rest_rep.
    simpl.
    progress fold heap.
    rewrite add_node_heap_start0.
    rewrite add_node_heap_used_space0.
    rewrite add_node_heap_total0.
    subst t_info'; rewrite add_node_heap_ti_token_rep
           by (fold heap; rewrite SPACE_NONEMPTY; Zlength_solve).
    progress fold g0.    
    rewrite Z.mul_add_distr_l.
    change 16 with (WORD_SIZE * 2).
    change (upd_Znth _ _ _) with (upd_first_n [add_node_space 0 (nth 0 (spaces heap) null_space) 2 t_size] (spaces heap)).
    rewrite upd_first_n_app by list_solve.
    simpl tl.
    fold limit.
    change (Zlength [_]) with 1.
    rewrite <- tl_sublist.
    rewrite iter_sepcon.iter_sepcon_app.
    simpl. 
    rewrite add_node_spatial; [ | apply graph_has_gen_O | apply gc_cond | | ].
    2: red; intros; apply gc_cond; auto.
    2:{ unfold new_copied_v; red.
        subst es. destruct p; intros; try contradiction.
        destruct H2; try contradiction. inv H2. simpl.
        subst v; simpl. split3; auto.
        split. eapply has_v; eauto.
        split3; auto. lia. repeat constructor; intro Hx ;inv Hx.
    }
    cancel.
    rewrite sepcon_comm.
    apply sepcon_derives.
    +
      unfold space_rest_rep, add_node_space; simpl.
      replace (nth 0 (spaces heap) null_space) with g0
       by (rewrite SPACE_NONEMPTY; reflexivity).
   rewrite if_false by (intro H0'; rewrite H0' in isptr_g0; simpl in *; contradiction).
   rewrite Z.sub_add_distr. fold space. rewrite LEN_N in *. change (Z.succ _) with 2 in *.
   unfold field_address0.
   rewrite if_true by auto with field_compatible.
   simpl.
   unfold alloc.
   rewrite offset_offset_val.
   rewrite Z.mul_add_distr_l.
   change (WORD_SIZE * 2)%Z with 16.
   cancel.
  +
    pattern vl at 2; replace vl with (sublist 0 1 vl ++ sublist 1 (Zlength vl) vl)
              by list_solve.
    rewrite (split2_data_at_Tarray_app 1) by list_solve.
    unfold spatial_gcgraph.vertex_at.
    destruct comp_g0 as [C1 [C2 C3 ] ].
    replace (nth_sh g 0) with (space_sh g0)
     by (unfold nth_sh; rewrite C2; auto).
    apply sepcon_derives.
   * unfold vertex_address, vertex_offset. rewrite offset_offset_val.
     rewrite add_node_gen_start by apply graph_has_gen_O.
     rewrite add_node_previous_vertices_size by apply Nat.le_refl.
     unfold new_copied_v; simpl.
     rewrite sublist_one by lia. 
     unfold vl. simpl. rewrite Znth_0_cons.
     unfold Z2val, header_new; simpl.
     change (tarray ?t 1) with (tarray t (Zlength (@nil val) + 1)).
     rewrite spatial_gcgraph.data_at_tarray_split_1 by reflexivity.
     rewrite data_at_zero_array_eq by (auto; repeat apply isptr_offset_val'; auto).
     rewrite C3. unfold alloc.
     rewrite sepcon_emp.
     change WORD_SIZE with 8.
     replace (8 * (used_space g0 + 1) + -8) with (8 * used_space g0) by lia.
      replace (gen_start g 0) with (space_start g0).
     rewrite data_at_int_or_ptr_long; apply derives_refl.
     rewrite <- C1.
     unfold gen_start.
     rewrite if_true by apply graph_has_gen_O; auto.
   * unfold field_address0; rewrite if_true by auto with field_compatible.
     simpl nested_field_offset.
     unfold fields_new; simpl. rewrite Zlength_map.
     rewrite add_node_vertex_address_new;  [ | apply graph_has_gen_O].
     rewrite make_fields_eq_length. simpl.
     unfold update_vlabel. rewrite if_true by reflexivity.
     unfold newRaw at 1; simpl. rewrite Zlength_cons, Zlength_nil.
     change (Z.succ 0) with 1.
     rewrite <- tl_sublist. subst vl; simpl.
     unfold new_copied_v, vertex_address, vertex_offset. simpl.
     rewrite C3.
     unfold alloc.
      rewrite offset_offset_val.
     rewrite Z.mul_add_distr_l. change (WORD_SIZE * 1) with 8.
     unfold gen_start. rewrite C1.
     rewrite if_true by apply graph_has_gen_O; auto.
     apply derives_refl'. f_equal.
     unfold make_fields, add_node at 2. simpl.
     unfold update_vlabel. rewrite if_true by reflexivity.
     subst v.
     unfold rep_type_val.
     destruct p; simpl; auto. f_equal.
     unfold vertex_address; simpl.
     unfold new_copied_v; simpl.
      unfold vgeneration; simpl. unfold updateEdgeFunc; simpl.
      rewrite if_true by reflexivity.
     rewrite add_node_gen_start by apply graph_has_gen_O.
     unfold vertex_offset.
     rewrite add_node_previous_vertices_size.
     reflexivity.
     red. 
     clear - H. apply has_v in H.
     destruct H. red in H0. lia.

*)

Local Ltac entailer_for_return ::= idtac.

Ltac alloc_start :=
  start_function';
  match goal with H1 : Z.of_nat ?a < headroom _ |- _ => 
    let HEADROOM := fresh "HEADROOM" in 
    rename H1 into HEADROOM; set (N := a) in HEADROOM;
    unfold headroom in HEADROOM
  end;
  let UFA := fresh "UFA" in assert (UFA := unfold_for_allocation);
     cbv zeta in UFA; sep_apply UFA; clear UFA; Intros;
  set(heap := ti_heap _) in *;
  set (g0 := heap_head heap) in *;
  set (space := total_space g0 - used_space g0) in *.

(*
Ltac alloc_finish N := 
  create_upd_first_n;
  repeat match goal with |- context [@data_at CompSpecs ?a ?b ?c] =>
        replace (@data_at CompSpecs a b c) with 
                (@data_at env_graph_gc.CompSpecs a b c)
       by (change_compspecs CompSpecs; reflexivity)
  end;
  let Hz := constr:(Z.of_nat N * 1024) in let Hz := eval compute in Hz in 
    change Hz with (1024 * (Z.of_nat N));
  let Nz := constr:(Z.of_nat (S N)) in let Nz := eval compute in Nz in  
  change (sem_add_ptr_long ?a ?b (Vlong (Int64.repr Nz))) with
         (sem_add_ptr_long a b (Vlong (Int64.repr (Z.of_nat (S N)))));
  rewrite !sem_add_pl_ptr_special by auto;
  rewrite !offset_offset_val; unfold force_val;
  change (Tpointer tvoid _) with int_or_ptr_type;
  repeat simple apply delete_LOCAL_from_ENTAIL;
  go_lower;
(*   clearbody N.*)
  repeat match goal with H := _ |- _ => subst H end;
  simple apply alloc_finish; auto.
*)

Lemma body_alloc_make_Coq_Init_Datatypes_nat_S :
  semax_body Vprog Gprog
             f_alloc_make_Coq_Init_Datatypes_nat_S
             alloc_make_Coq_Init_Datatypes_nat_S_spec.
Proof.
  alloc_start.
  change_compspecs CompSpecs.
  repeat forward; [solve [entailer!] | ].


(*  alloc_finish N. *)

  create_upd_first_n;
  repeat match goal with |- context [@data_at CompSpecs ?a ?b ?c] =>
        replace (@data_at CompSpecs a b c) with 
                (@data_at env_graph_gc.CompSpecs a b c)
       by (change_compspecs CompSpecs; reflexivity)
  end.
  assert_PROP (@field_compatible env_graph_gc.CompSpecs (tarray int_or_ptr_type space) []
        (offset_val (WORD_SIZE * used_space g0) (space_start g0))) as FC 
      by entailer!;
  let Hz := constr:(Z.of_nat N * 1024) in let Hz := eval compute in Hz in 
    change Hz with (1024 * (Z.of_nat N)).
  let Nz := constr:(Z.of_nat (S N)) in let Nz := eval compute in Nz in  
  change (sem_add_ptr_long ?a ?b (Vlong (Int64.repr Nz))) with
         (sem_add_ptr_long a b (Vlong (Int64.repr (Z.of_nat (S N))))).
  rewrite !sem_add_pl_ptr_special by auto.
  rewrite !offset_offset_val; unfold force_val;
  change (Tpointer tvoid _) with int_or_ptr_type.
  repeat simple apply delete_LOCAL_from_ENTAIL;
  go_lower;
(*   clearbody N.*)
  repeat match goal with H := _ |- _ => subst H end.
  match goal with |- context [upd_first_n ?vl'] => set (vl := vl') end.
  
(*  eapply alloc_finish; auto. *)
  rename H0 into gc_cond.
  rename H1 into ROOTS_IN.
  rename H3 into SPACE_NONEMPTY.
  rename H4 into isptr_g0.
  clear H5. (* wsh_g0 *)
  rename H6 into comp_g0.
  clear H2.
  clear - H HEADROOM gc_cond ROOTS_IN SPACE_NONEMPTY isptr_g0 comp_g0 FC vl.

   set (heap := ti_heap t_info : heap) in *.
   set (g0 := heap_head heap : space) in *.
   set (space := total_space g0 - used_space g0 : Z) in *.
   set (alloc := offset_val (WORD_SIZE * used_space g0) (space_start g0)) in *.
   set (limit := offset_val (WORD_SIZE * total_space g0) (space_start g0)).
   set (N := 1%nat) in HEADROOM,vl.
   change (Z.of_nat 2) with (Z.succ (Z.of_nat N)).



rewrite upd_first_n_app
  by (unfold default_val; simpl; rewrite Zlength_Zrepeat by lia;
       subst vl; simpl; list_solve).
assert (Zlength vl = Z.succ (Z.of_nat N)) by reflexivity.
change (default_val (tarray int_or_ptr_type space))
  with (Zrepeat Vundef space).
rewrite (split2_data_at_Tarray_app (Zlength vl)) by list_simplify.
rewrite Zlength_Zrepeat by lia.
rename H0 into LEN_N.
(*
gc_cond : gc_condition_prop g t_info roots outlier
ROOTS_IN : ~In (inr (new_copied_v g 0)) roots
space_rest : list GCGraph.space
SPACE_NONEMPTY : spaces heap = g0 :: tl (spaces heap)
isptr_g0 : isptr (space_start g0)
wsh_g0 : writable_share (space_sh g0)
comp_g0 : generation_space_compatible g (0%nat, nth_gen g 0, g0)
H_uneq : match p with
         | repNode v => v <> new_copied_v g 0
         | _ => True
         end
*)
  rewrite Z.mul_succ_r.
  change (sizeof int_or_ptr_type) with WORD_SIZE.
  assert (match p with | repNode v => v <> new_copied_v g 0 | _ => True end) as H_uneq.
   { clear - H; destruct p; try reflexivity. intros ->. apply (@has_v nat _) in H.
        eapply graph_has_v_not_eq; eauto. }
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

  assert (t_size: 0 <= 2 <= total_space (nth_space t_info 0) - used_space (nth_space t_info 0)). {
    pose proof heap_head_cons.
    destruct (heap_head_cons (ti_heap t_info)) as [s [l [H8' H9' ] ] ].
    unfold nth_space.
      subst s. rewrite H8'. simpl. fold heap. fold g0. subst space; lia.
  }
    pose (t_info' := graph_add.add_node_ti 0 t_info _ t_size).
    Exists t_info'.
  assert (add_node_compatible g (new_copied_v g 0) es).
    { unfold add_node_compatible. intros * Hx; subst es; destruct p; inversion Hx.
    - injection H0. intros. subst. simpl.  intuition eauto.
      + eauto using has_v.
      + rep_lia.
      + repeat constructor. eauto.
       - inversion H0. }

    entailer!;     clear H7 H8 H6 H5 H4 H3 H2.
  - split3.
    + (** In this new graph, we have (S n) at position v with our predicate. *)
      exists p. 
      change (is_in_graph (add_node g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es) x p /\
       graph_cRep (add_node g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es) (repNode v) (boxed 0 1) [p]).

       intuition (try congruence).
      * apply (@is_monotone _ Rep_nat); eauto; apply graph_has_gen_O.
      * unfold graph_cRep. intuition.
        -- split.
           ++ rewrite add_node_graph_has_gen; eauto; apply graph_has_gen_O.
           ++ apply add_node_has_index_new; eauto; apply graph_has_gen_O.
        -- rewrite add_node_vlabel.
           simpl. intuition eauto. repeat constructor.
           destruct p as [| |p_v]; try reflexivity.
           simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (v, 0%nat)); congruence.
    + destruct gc_cond. unfold gc_correct.sound_gc_graph, roots_compatible in *. intuition eauto. apply add_node_iso; eauto.
    + destruct comp_g0 as (C1&C2&C3).
      simpl. unfold vertex_address, vertex_offset.
      simpl. f_equal.
      * fold heap; fold g0. rewrite <- C3.
        assert (previous_vertices_size g 0 (number_of_vertices (nth_gen g 0)) = previous_vertices_size (add_node g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es) 0
     (number_of_vertices (nth_gen g 0))) as ->.
        { unfold previous_vertices_size, vertex_size_accum. unfold vertex_size.
          apply fold_left_ext. intros. rewrite add_node_vlabel_old. reflexivity.
          unfold GCGraph.nat_inc_list in H2. unfold new_copied_v.
          rewrite nat_seq_In_iff in H2. intros A. injection A. rep_lia. }
        assert (WORD_SIZE = 8) as -> by reflexivity; rep_lia.
      * rewrite add_node_gen_start; eauto; try apply graph_has_gen_O.
        unfold gen_start. if_tac. eauto. contradiction H2; apply graph_has_gen_O.
  - unfold full_gc.
    Intros. entailer!;     clear H7 H8 H6 H5 H4 H2.
    { eapply add_node_gc_condition_prop; try apply graph_has_gen_O; eauto. destruct p; 
       intuition (eauto using has_v).
        clear - H. exfalso.
       induction x; simpl. contradiction. destruct H as[p [? ? ] ]. contradiction.
     }

    (** Names *)

    unfold before_gc_thread_info_rep. Intros.
    unfold heap_rest_rep.
    simpl.
    progress fold heap.
    rewrite add_node_heap_start0.
    rewrite add_node_heap_used_space0.
    rewrite add_node_heap_total0.
    subst t_info'; rewrite add_node_heap_ti_token_rep
           by (fold heap; rewrite SPACE_NONEMPTY; Zlength_solve).
    progress fold g0.    
    rewrite Z.mul_add_distr_l.
    change 16 with (WORD_SIZE * 2).
    change (upd_Znth _ _ _) with (upd_first_n [add_node_space 0 (nth 0 (spaces heap) null_space) 2 t_size] (spaces heap)).
    rewrite upd_first_n_app by list_solve.
    simpl tl.
    fold limit.
    change (Zlength [_]) with 1.
    rewrite <- tl_sublist.
    rewrite iter_sepcon.iter_sepcon_app.
    simpl. 
    rewrite add_node_spatial; [ | apply graph_has_gen_O | apply gc_cond | | ].
    2: red; intros; apply gc_cond; auto.
    2:{ unfold new_copied_v; red.
        subst es. destruct p; intros; try contradiction.
        destruct H2; try contradiction. inv H2. simpl.
        subst v; simpl. split3; auto.
        split. eapply has_v; eauto.
        split3; auto. lia. repeat constructor; intro Hx ;inv Hx.
    }
    cancel.
    rewrite sepcon_comm.
    apply sepcon_derives.
    +
      unfold space_rest_rep, add_node_space; simpl.
      replace (nth 0 (spaces heap) null_space) with g0
       by (rewrite SPACE_NONEMPTY; reflexivity).
   rewrite if_false by (intro H0'; rewrite H0' in isptr_g0; simpl in *; contradiction).
   rewrite Z.sub_add_distr. fold space. rewrite LEN_N in *. change (Z.succ _) with 2 in *.
   unfold field_address0.
   rewrite if_true by auto with field_compatible.
   simpl.
   unfold alloc.
   rewrite offset_offset_val.
   rewrite Z.mul_add_distr_l.
   change (WORD_SIZE * 2)%Z with 16.
   cancel.
  +
    pattern vl at 2; replace vl with (sublist 0 1 vl ++ sublist 1 (Zlength vl) vl)
              by list_solve.
    rewrite (split2_data_at_Tarray_app 1) by list_solve.
    unfold spatial_gcgraph.vertex_at.
    destruct comp_g0 as [C1 [C2 C3 ] ].
    replace (nth_sh g 0) with (space_sh g0)
     by (unfold nth_sh; rewrite C2; auto).
    apply sepcon_derives.
   * unfold vertex_address, vertex_offset. rewrite offset_offset_val.
     rewrite add_node_gen_start by apply graph_has_gen_O.
     rewrite add_node_previous_vertices_size by apply Nat.le_refl.
     unfold new_copied_v; simpl.
     rewrite sublist_one by lia. 
     unfold vl. simpl. rewrite Znth_0_cons.
     unfold Z2val, header_new; simpl.
     change (tarray ?t 1) with (tarray t (Zlength (@nil val) + 1)).
     rewrite spatial_gcgraph.data_at_tarray_split_1 by reflexivity.
     rewrite data_at_zero_array_eq by (auto; repeat apply isptr_offset_val'; auto).
     rewrite C3. unfold alloc.
     rewrite sepcon_emp.
     change WORD_SIZE with 8.
     replace (8 * (used_space g0 + 1) + -8) with (8 * used_space g0) by lia.
      replace (gen_start g 0) with (space_start g0).
     rewrite data_at_int_or_ptr_long; apply derives_refl.
     rewrite <- C1.
     unfold gen_start.
     rewrite if_true by apply graph_has_gen_O; auto.
   * unfold field_address0; rewrite if_true by auto with field_compatible.
     simpl nested_field_offset.
     unfold fields_new; simpl. rewrite Zlength_map.
     rewrite add_node_vertex_address_new;  [ | apply graph_has_gen_O].
     rewrite make_fields_eq_length. simpl.
     unfold update_vlabel. rewrite if_true by reflexivity.
     unfold newRaw at 1; simpl. rewrite Zlength_cons, Zlength_nil.
     change (Z.succ 0) with 1.
     rewrite <- tl_sublist. subst vl; simpl.
     unfold new_copied_v, vertex_address, vertex_offset. simpl.
     rewrite C3.
     unfold alloc.
      rewrite offset_offset_val.
     rewrite Z.mul_add_distr_l. change (WORD_SIZE * 1) with 8.
     unfold gen_start. rewrite C1.
     rewrite if_true by apply graph_has_gen_O; auto.
     apply derives_refl'. f_equal.
     unfold make_fields, add_node at 2. simpl.
     unfold update_vlabel. rewrite if_true by reflexivity.
     subst v.
     unfold rep_type_val.
     destruct p; simpl; auto. f_equal.
     unfold vertex_address; simpl.
     unfold new_copied_v; simpl.
      unfold vgeneration; simpl. unfold updateEdgeFunc; simpl.
      rewrite if_true by reflexivity.
     rewrite add_node_gen_start by apply graph_has_gen_O.
     unfold vertex_offset.
     rewrite add_node_previous_vertices_size.
     reflexivity.
     red. 
     clear - H. apply has_v in H.
     destruct H. red in H0. lia.
Qed.
