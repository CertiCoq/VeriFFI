Require Import VeriFFI.examples.uint63nat.prog.

Require Import ZArith.
Require Import Psatz.

Require Import VeriFFI.verification.specs_general.

Require Import VeriFFI.generator.Rep.
Require Import VeriFFI.generator.Desc.

#[export] Obligation Tactic := gen.
MetaCoq Run (gen_for nat).
MetaCoq Run (desc_gen S).

Require Import VST.floyd.proofauto.
Require Import VeriFFI.examples.uint63nat.glue.
Require Import VeriFFI.library.meta.


Require Import VST.floyd.proofauto.
From CertiGraph.CertiGC Require Import GCGraph spatial_gcgraph.

From VeriFFI Require Import library.base_representation.
From VeriFFI Require Import library.meta.
From VeriFFI Require Import verification.graph_add.
From VeriFFI Require Import verification.specs_library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(* Specfication of alloc - would be generalized otherwise. *)
Definition alloc_make_Coq_Init_Datatypes_nat_S_spec : ident * funspec :=
  DECLARE _alloc_make_Coq_Init_Datatypes_nat_S
          (alloc_make_spec_general (@desc _ S _) 1).

Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := [ alloc_make_Coq_Init_Datatypes_nat_S_spec ] .


(* BEGIN delete this in the next VST release that has Ltac prove_cs_preserve_type
Converging two compspecs fit together.
*)
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

(* Implications can be removed. *)
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
    unfold gc_condition_prop in *.
    destruct gc_cond as (gc1&gc2&gc3&gc4&gc5&gc6&gc7&gc8&gc9&gc10).
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
 forall g (v := new_copied_v g 0 : VType) t flds R1 R2 R3 es ,
 copy_compatible g ->
 copy_compatible (add_node g 0 (newRaw v t flds R1 R2 R3) es).
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


Lemma add_node_rootpairs_compatible:
  forall rp roots g nr es,
    roots_graph_compatible roots g ->
    rootpairs_compatible g rp roots ->
    rootpairs_compatible (add_node g 0 nr es) rp roots.
Proof.
 intros.
    red in H0|-*. rewrite <- H0. clear H0.
    induction roots; simpl; f_equal; auto.
    destruct a; simpl; auto.
    apply add_node_vertex_address_old; auto.
    inv H; auto.
    apply graph_has_gen_O.
    apply IHroots; clear IHroots; auto.
    destruct a; auto. destruct v; auto. inv H; auto.
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
  {  
    unfold add_node_compatible. intros e scr trg H_In. subst es. destruct p; inversion H_In.
    - injection H2. intros. subst. simpl. intuition auto. lia. repeat constructor; intro Hx; inversion Hx.
    - inversion H2. }
  assert (  edge_compatible g 0 (newRaw v 0 [rep_field p] R1 R2 R3) es).
  { unfold edge_compatible. intros. simpl. destruct p; simpl; intuition eauto. }
    decompose [and] H1; clear H1; repeat simple apply conj.
  all: eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_thread_compatible, add_node_ti_size_spec, add_node_roots_compatible.
  + eapply add_node_ti_size_spec; eauto.  rewrite spaces_size.   rep_lia.
  + eapply add_node_outlier_compatible; eauto. (* Print rep_field. *)  simpl.
    destruct p eqn:Hp; hnf; simpl; intros; try contradiction; eauto.
    destruct H1; try contradiction; subst; auto.
  + apply add_node_rootpairs_compatible; auto.
    destruct H11; auto.
  + apply add_node_copy_compatible; auto.
Qed.

(*
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
(spatial_gcgraph.outlier_rep outlier *
   @data_at env_graph_gc.CompSpecs sh thread_info_type (alloc, (limit, (ti_heap_p t_info, ti_args t_info))) ti *
   spatial_gcgraph.heap_struct_rep sh
     ((space_start g0, (Vundef, limit)) :: map spatial_gcgraph.space_tri (tl (spaces heap)))
     (ti_heap_p t_info) *
   @data_at_ env_graph_gc.CompSpecs (space_sh g0) (tarray int_or_ptr_type (total_space g0 - used_space g0))
     (offset_val (WORD_SIZE * used_space g0) (space_start g0)) *
   msl.iter_sepcon.iter_sepcon (@space_rest_rep env_graph_gc.CompSpecs) (tl (spaces heap)) *
   spatial_gcgraph.ti_token_rep t_info *
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

   Intros.
   unfold heap_rest_rep. rewrite SPACE_NONEMPTY. simpl. Intros.
   unfold space_rest_rep at 1. fold g0.
   rewrite if_false by (intro H0; rewrite H0 in isptr_g0; simpl in *; contradiction).
   fold limit. fold alloc.
   rewrite prop_true_andp by auto 10.
   cancel.
Qed. *)

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

Local Ltac entailer_for_return ::= idtac.

(* Ltac alloc_start :=
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
  set (space := total_space g0 - used_space g0) in *. *)

(** For arguments, this would have the following form,
parametric only in the tag and the number of arguments n.
- Having the thread_info, and n arguments
- Requiring sth at alloc
- Requiring a condition on alloc/limit and their distance
- Requiring n + 1 positions at the pointer to alloc, where n is the number of arguments
- Putting tag t at alloc
- Putting the n arguments from alloc + 1 on
- Increasing alloc by n
- Returning alloc + 1
*)

Notation "'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE' [[ xs ]] P 'POST' [ tz ] Q" :=
 (NDmk_funspec (xs, tz) cc_default (t1*t2*t3*t4*t5*t6*t7)
 (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => P%assert end)
 (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
 (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
            x5 at level 0, x6 at level 0, x7 at level 0,
            P at level 100, Q at level 100) : funspec_scope.

Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons : A -> forall n, vector A n -> vector A (S n).
            
Fixpoint to_list {A : Type} {n : nat} (v : vector A n) :=
  match v with
    | vnil => nil
    | vcons x _ xs => cons x (to_list xs)
end.

Definition n_arguments (tag : Z) (n : nat) : funspec :=
      WITH sh_tinfo : share, sh_heap: share, ti : val, ps : vector val n, b : block, alloc: Z, limit: Z
PRE [[ tptr (Tstruct glue._thread_info noattr) :: repeat (talignas 3%N (tptr tvoid)) n ]]
      PROP ( writable_share sh_tinfo;
      writable_share sh_heap; Int.min_signed <= tag <= Int.max_signed)
      (PARAMSx (ti :: to_list ps)
      (GLOBALSx nil
      (SEPx (@field_at env_graph_gc.CompSpecs sh_tinfo thread_info_type [StructField gc_stack._alloc] (Vptr b (Ptrofs.repr alloc)) ti
             :: @field_at env_graph_gc.CompSpecs sh_tinfo  thread_info_type [StructField gc_stack._limit] (Vptr b (Ptrofs.repr limit)) ti
             :: @data_at_ env_graph_gc.CompSpecs sh_heap (tarray (* KS *) int_or_ptr_type (1 + (Z.of_nat n))) (Vptr b (Ptrofs.repr alloc)) (* Space between alloc and limit? *)
             :: nil))))
POST [ (talignas 3%N (tptr tvoid)) ]
    PROP ()
    RETURN (Vptr b (Ptrofs.repr (alloc + 8 (* KS: CHANGE sizeof (size_t) *))))
    SEP (@field_at env_graph_gc.CompSpecs sh_tinfo thread_info_type [StructField gc_stack._alloc] (offset_val (Z.of_nat (S n) * sizeof (* KS *) int_or_ptr_type) (Vptr b (Ptrofs.repr alloc))) ti;
        @field_at env_graph_gc.CompSpecs sh_tinfo thread_info_type [StructField gc_stack._limit] (Vptr b (Ptrofs.repr limit)) ti;
        @data_at env_graph_gc.CompSpecs sh_heap (tarray (* KS *) int_or_ptr_type (1 + (Z.of_nat n))) (Vlong (Int64.repr tag) :: to_list ps) (Vptr b (Ptrofs.repr alloc))
        ).

Ltac inv x := dependent inversion x; subst; clear x.
Ltac vector_inv :=
    repeat (match goal with H: vector _ _ |- _ => inv H end).
          
Ltac alloc_start_function :=
    start_function1;
    vector_inv;
    first [ erewrite compute_close_precondition_eq; [ | reflexivity | reflexivity] | rewrite close_precondition_main ];
    start_function3.

    Ltac custom_tactics :=
        first [forward_if True | forward_call (1) | now (simpl; entailer!; try normalize) | entailer! ].
      
    Ltac repeat_forward tac :=
    repeat ((* KS try (unfold f_alloc_assign, f_alloc_standard); *) first [forward | tac]).

Lemma body_alloc_make_Coq_Init_Datatypes_nat_S : 
semax_body Vprog Gprog
            f_alloc_make_Coq_Init_Datatypes_nat_S
            (_alloc_make_Coq_Init_Datatypes_nat_S, n_arguments 1024 1).
Proof.
 (* KS: Todo: to be fixed *)
(*    alloc_start_function. *)
 (*   change_compspecs CompSpecs. 
      (* TODO: Different definition of thread_info. 
    What should I do on my site? *)
    repeat_forward custom_tactics. (* Fast Forward Tactics - floyd/fast_forward *)
    f_equal.
    (* Question: Is there a tactic? *)
    autorewrite with norm norm1 norm2.
    rewrite ptrofs_of_int64_int64_repr; eauto.
    now autorewrite with norm.
Qed. *) 
Admitted.

Fixpoint get_fields g to (xs : list rep_type) (n: nat) :=
    let v := new_copied_v g to in 
    match xs with 
    | nil => nil 
    | cons x xs => match x with 
                  | repNode v_x => ((v, n), (v, v_x) ) :: get_fields g to xs (1 + n)
                  | _ => get_fields g to xs (1 + n)
                  end
    end.



Lemma get_fields_eq g to xs (n : nat):   
  let v := new_copied_v g to in 
    get_fields g to xs n = 
            filter_option (map (fun x => match (snd x) with | repNode v_x => Some ((v, (fst x)), (v, v_x) )  
                                           | _ => None
                                           end)
                           (combine  (nat_seq n (Datatypes.length xs)) xs)).
Proof. 
    intros. 
    revert n. 
    induction xs; intros; eauto.
    simpl. rewrite IHxs. 
    destruct a; eauto. 
 Qed.

Lemma make_fields'_eq xs v n :
make_fields' xs v n = map (fun x => match (snd x) with
| Some s =>
    match s with
    | inl z => inl (inl z) 
    | inr ptr => inl (inr ptr) 
    end
| None => inr (v, fst x) 
end) (combine (nat_seq n (Datatypes.length xs)) xs).
Proof. 
  revert n. 
  induction xs; eauto. 
  intros n. simpl. 
  replace (n +1)%nat with (S n) by lia.
  rewrite !IHxs. 
  destruct a; eauto. 
  -  destruct s; eauto. 
Qed.

Lemma nodup_getfields g ps n: 
NoDup (map fst (get_fields g 0 ps n)).
Proof.
  rewrite get_fields_eq. revert n. 
  induction ps; intros. 
  - simpl. constructor.
  - simpl. destruct a; eauto. 
    + simpl. constructor; eauto. 
      intros H.
      apply in_map_iff in H. 
      destruct H as ((v0 & m)  & A1).
      destruct A1. 
      apply filter_option_In_iff in H0. 
      apply in_map_iff in H0. 
      destruct H0 as (bla & B1).
      simpl in *. subst. destruct bla. simpl in *. destruct B1. destruct r; try congruence. 
      injection H. intros. subst. 
      apply in_combine_l in H0. 
      apply nat_seq_In_iff in H0.  lia. 
Qed.

Lemma add_node_compatible_new g ps t_info roots outlier:
let v := new_copied_v g 0 in
let es :=  get_fields g 0 ps 0 : list (VType * nat * (VType * VType)) in
Forall (fun p => match p with
| repNode v' => graph_has_v g v' /\ v <> v'
| _ => True
end) ps -> 
gc_condition_prop g t_info roots outlier 
 -> add_node_compatible g v es. 
Proof. 
  intros. 
  subst es. rewrite get_fields_eq.
  unfold add_node_compatible. intros e scr trg H_In.
  apply filter_option_In_iff in H_In.
  apply in_map_iff in H_In.
  destruct H_In as ((n&p)&(p_eq&H_In)). 
  pose (H_In' := in_combine_r _ _ _ _ H_In).
  simpl in *. 
 
  destruct p; try congruence. 
  rewrite Forall_forall in H. 
    specialize (H _ H_In').
  inversion p_eq. simpl. split3; eauto.
  subst. 
  split3; eauto. 
  -  intuition.
  - lia. 
  - split. 
    + assert (HH := nodup_getfields g ps 0). rewrite get_fields_eq in HH. eauto.

    + intuition. 
Qed.


    Lemma add_node_gc_condition_prop_general g ps t t_info roots outlier R1 R2 R3 t_size (H: graph_has_gen g 0) :
  let v := new_copied_v g 0 in
  let es :=  get_fields g 0 ps 0 : list (VType * nat * (VType * VType)) in
  let g' := add_node g 0 (newRaw v (Z.of_nat t) (map rep_field ps) R1 R2 R3) es in
  let t_info' := add_node_ti 0 t_info (1 + Zlength (map rep_field ps)) t_size in
  Forall (fun p => match p with
  | repNode v' => graph_has_v g v' /\ v <> v'
  | repOut v' => In v' outlier
  | _ => True
  end) ps
  ->
gc_condition_prop g t_info roots outlier -> gc_condition_prop g' t_info' roots outlier.
Proof.
  intros. unfold gc_condition_prop in *. unfold g'.
  assert ( add_node_compatible g (new_copied_v g 0) es).
  {  eapply add_node_compatible_new; eauto. 
      rewrite !Forall_forall in *. intros. specialize (H0 _ H2). destruct x; eauto. 
  }
  destruct H1 as (unmarked & (nobackward & (nodanging & (tisizespec & (safetocopy & (graphticompatible & (outliercompatible & (rootscompatible & (soundgcgraph & (rp_compatible & copycompatible)))))))))).

    assert (edge_compatible g 0 (newRaw v (Z.of_nat t) (map rep_field ps) R1 R2 R3) es).
    { unfold edge_compatible. intros. simpl. clear.  unfold es. generalize (0)%nat at 2 4.  induction ps; intros n; simpl; eauto.
    - reflexivity.
    - destruct a; simpl.
      + rewrite Nat.add_1_r.  apply IHps.
      + rewrite Nat.add_1_r.  apply IHps.
      + rewrite Nat.add_1_r. intuition eauto. right.  apply IHps; eauto.
        rewrite IHps. eauto. }

  split3;  eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_thread_compatible, add_node_ti_size_spec, add_node_roots_compatible.
  split3;  eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_thread_compatible, add_node_ti_size_spec, add_node_roots_compatible.

  + eapply add_node_ti_size_spec; eauto.  rewrite spaces_size.   rep_lia.
  + split3;  eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_thread_compatible, add_node_ti_size_spec, add_node_roots_compatible.
    * apply add_node_graph_thread_compatible; eauto. 
      unfold raw_fields. simpl. lia. 
    * split3;  eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_thread_compatible, add_node_ti_size_spec, add_node_roots_compatible.
    --  
    apply add_node_outlier_compatible; eauto.
    simpl.
    unfold incl. intros. apply filter_sum_right_In_iff in H3. 
    apply filter_option_In_iff in H3. apply in_map_iff in H3. 
    destruct H3 as (p & A1 & A2). destruct p; simpl in *; try congruence. 
    rewrite Forall_forall in H0. injection A1. intros. subst.  exact (H0 _ A2). 
    --  split3;  eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_thread_compatible, add_node_ti_size_spec, add_node_roots_compatible.
       ++ simpl. apply add_node_rootpairs_compatible; auto.
           destruct rootscompatible; auto. 
       ++ apply add_node_copy_compatible; eauto.   
Qed.

Definition X_in_graph_cons (descr : ctor_desc) (t: nat) : Prop :=
  forall (gr : graph) (ps : list rep_type)  (args_my : args (ctor_reified descr)),
  graph_has_gen gr 0 ->
  forall (R1 : 0 <= Z.of_nat t < 256)
    (R2 : 0 < Zlength (map rep_field ps) < two_power_pos 54)
    (R3 : NO_SCAN_TAG <= Z.of_nat t -> ~ In None (map rep_field ps)),
    in_graphs gr (ctor_reified descr) args_my ps ->
    add_node_compatible gr (new_copied_v gr 0) (get_fields gr 0 ps 0) -> 
    let r := result (ctor_reified descr) args_my in 
    @is_in_graph (projT1 r) (@field_in_graph (projT1 r) (projT2 r))  (add_node gr 0
    (newRaw (new_copied_v gr 0) (Z.of_nat t) (map rep_field ps) R1 R2 R3)
    (get_fields gr 0 ps 0)) (ctor_reflected descr args_my)  (repNode (new_copied_v gr 0))
.

Definition calc t n := Z.of_nat t + Z.shiftl (Z.of_nat n) 10.

Fixpoint from_list {X} (xs : list X) : vector X (length xs).
Proof.
  exact (match xs with
           | nil => vnil X
           | cons x xs => vcons X x _ (from_list X xs) end).
Defined.

Lemma to_from_vec {X} (xs : list X) :
  to_list (from_list xs) = xs.
Proof.
  induction xs; try reflexivity.
  simpl.
  simpl. f_equal. simpl. apply IHxs.
Qed.

Lemma in_graphs_has:
  forall (descr : ctor_desc) (gr : graph)
    (ps : list rep_type) (args_my : args (ctor_reified descr)),
    in_graphs gr (ctor_reified descr) args_my ps ->
    Forall
      (fun p : rep_type =>
         match p with
         | repNode v' => graph_has_v gr v' /\ new_copied_v gr 0 <> v'
         | _ => True
         end) ps.
Proof.
  intros.
  remember (ctor_reified descr) as d. clear Heqd. revert ps H. 
  induction d; eauto; intros. 
  - simpl in H.  destruct args_my.  destruct s. simpl in *. eauto. 
  - simpl in *. destruct args_my. destruct ps; eauto. 
    destruct H0. constructor. 
    + destruct r0. eauto. reflexivity. 
    split. 
      * eapply has_v; eauto. (* 
      (* TODO: BROKEN BY NEWEST COMMIT *)
      eapply H0.
      * intros B. eapply graph_has_v_not_eq. 2: rewrite B; reflexivity. eapply has_v; eauto.  
    + eauto. 


  -  simpl in *. destruct args_my. destruct ps; eauto. 
  destruct H0. constructor. 
  + destruct cls0. 
  
  destruct r0. eauto. reflexivity. 
  split. 
    * eapply has_v; eauto.
    * intros B. eapply graph_has_v_not_eq. 2: rewrite B; reflexivity. eapply has_v; eauto.  
  + eauto. 

  - simpl in *. destruct args_my. eauto. 
  - simpl in *. destruct args_my. destruct ps; eauto. inversion H. *) 
Admitted.


Definition X_in_graph_cons' (descr : ctor_desc) (t: nat) : Prop :=
  forall (gr : graph) (ps : list rep_type)  (args_my : args (ctor_reified descr)),
  graph_has_gen gr 0 ->
  forall (R1 : 0 <= Z.of_nat t < 256)
    (R2 : 0 < Zlength (map rep_field ps) < two_power_pos 54)
    (R3 : NO_SCAN_TAG <= Z.of_nat t -> ~ In None (map rep_field ps)),
    in_graphs gr (ctor_reified descr) args_my ps ->
    add_node_compatible gr (new_copied_v gr 0) (get_fields gr 0 ps 0) -> 
    let r := result (ctor_reified descr) args_my in 
    @is_in_graph (projT1 r) (@field_in_graph (projT1 r) (projT2 r))  (add_node gr 0
    (newRaw (new_copied_v gr 0) (Z.of_nat t) (map rep_field ps) R1 R2 R3)
    (get_fields gr 0 ps 0)) (ctor_reflected descr args_my)  (repNode (new_copied_v gr 0))
.

Definition field_t_rep_type (g : LGraph) x := 
  match x with 
  | inl (inl z) => repZ z 
  | inl (inr ptr) => repOut ptr 
  | inr e => repNode (dst (pg_lg g) e)
  end.


Definition general_subsumption A `(InGraph A) t n descr :
  X_in_graph_cons descr t ->  
  0 <= Z.of_nat t < 250 ->
  0 < Z.of_nat n < 2096895 ->
  funspec_sub (n_arguments (calc t n) n) (alloc_make_spec_general descr n).
Proof.
    do_funspec_sub.
    
    assert (HH : 0 < Z.of_nat n < two_power_pos 54).  { unfold two_power_pos. simpl. rep_lia. }
    assert (R1 : 0 <= Z.of_nat t < 256) by rep_lia.
    destruct w as 
    ((((((((gv&gr)&ps)&args_my)&roots)&sh)&tinfo_pos)&outliers)&tinfo).
    entailer.
  
    unfold argsHaveTyps in H2.
    simpl in H2.
    unfold specs_library.full_gc. Intros.
    unfold before_gc_thread_info_rep.
    assert (graph_has_gen_0 := graph_has_gen_O gr).
    destruct (heap_head_cons (ti_heap tinfo)) as (g0&space_rest&SPACE_NONEMPTY&g0_eq).
    assert (isptr (space_start g0) /\  writable_share (space_sh g0) /\ generation_space_compatible gr (0%nat, nth_gen gr 0, g0)) as (isptr_g0&wsh_g0&comp_g0).
    { subst; eapply spaces_g0; eauto. }
  
    eapply binop_lemmas4.isptr_e in isptr_g0 as (b&x'&isptr_eq).
    pose (alloc :=  Ptrofs.signed (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * used_space (heap_head (ti_heap tinfo)))))).
    pose (limit :=  Ptrofs.signed (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * total_space (heap_head (ti_heap tinfo)))))) .

    pose (vals := from_list (map (fun p => specs_library.rep_type_val gr p) ps)).
    assert (ps_size := in_graphs_size _ _ _ _ H4).
    rewrite ps_size.   erewrite <- map_length.
    rename H8 into Hgv.
    rename H9 into gc_cond.
    rename H5 into headroom_size.
    rename H0 into result_in_graph.
    rename H4 into args_in_graph.
  
    (* With Arguments of n_arguments *)
    Exists ((((((sh, space_sh (heap_head (ti_heap tinfo))), tinfo_pos) , vals), b),  alloc), limit).

(* 
spatial_gcgraph.heap_struct_rep
	 : share -> list (reptype env_graph_gc.space_type) -> val -> mpred *)

   unfold before_gc_thread_info_rep.


  (*        * data_at sh env_graph_gc.thread_info_type
         (offset_val (WORD_SIZE * used_space (heap_head (ti_heap tinfo)))
            (space_start (heap_head (ti_heap tinfo))),
          (offset_val (WORD_SIZE * total_space (heap_head (ti_heap tinfo)))
             (space_start (heap_head (ti_heap tinfo))),
           (ti_heap_p tinfo,
            (ti_args tinfo,
             (ti_fp tinfo, (Vptrofs (ti_nalloc tinfo), nullval))))))
         tinfo_pos     *)


    (* The frame *)
    Exists (outlier_rep outliers * ti_token_rep (ti_heap tinfo) (ti_heap_p tinfo) *
        @graph_rep  gr *
            @field_at env_graph_gc.CompSpecs sh specs_library.thread_info_type [StructField gc_stack._heap] (ti_heap_p tinfo) tinfo_pos *
            @field_at env_graph_gc.CompSpecs sh specs_library.thread_info_type [StructField gc_stack._args] (ti_args tinfo) tinfo_pos *
            heap_struct_rep sh
                            ((Vptr b x',
                              (Vundef,
                               (Vptr b (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * total_space (heap_head (ti_heap tinfo))))), 
                               Vptr b (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * total_space (heap_head (ti_heap tinfo))))))))
                               :: map space_tri (tl (spaces (ti_heap tinfo)))) (ti_heap_p tinfo)* 
                               iter_sepcon.iter_sepcon space_rest (* @specs_library.space_rest_rep env_graph_gc.CompSpecs *) space_rest_rep  *
           @data_at_ env_graph_gc.CompSpecs (space_sh (heap_head (ti_heap tinfo))) (tarray int_or_ptr_type (total_space (heap_head (ti_heap tinfo)) -
          used_space (heap_head (ti_heap tinfo)) - Z.of_nat (1 + Datatypes.length ps))) (@field_address0 env_graph_gc.CompSpecs (tarray int_or_ptr_type
            (total_space (heap_head (ti_heap tinfo)) -
             used_space (heap_head (ti_heap tinfo)))) [ArraySubsc (Z.of_nat (1 + Datatypes.length ps))]  (Vptr b
            (Ptrofs.add x'
               (Ptrofs.repr (WORD_SIZE * used_space (heap_head (ti_heap tinfo)))))))  
            *  frames_rep sh (ti_frames tinfo)
            * @field_at env_graph_gc.CompSpecs sh env_graph_gc.thread_info_type (DOT gc_stack._fp) (ti_fp tinfo)
            tinfo_pos
            * @field_at env_graph_gc.CompSpecs sh env_graph_gc.thread_info_type (DOT gc_stack._nalloc)
                (Vlong (Ptrofs.to_int64 (ti_nalloc tinfo))) tinfo_pos
(*             * field_at sh env_graph_gc.thread_info_type (DOT gc_stack._odata) nullval tinfo_pos *)
            * @field_at env_graph_gc.CompSpecs sh env_graph_gc.thread_info_type (DOT gc_stack._odata) nullval tinfo_pos
            * gc_spec.all_string_constants Ers gv
               )%logic.


(* The term "map space_tri (tl (spaces (ti_heap tinfo)))" has type
 "list (reptype env_graph_gc.space_type)" while it is expected to have type
 "list (val * (val * val))". *)               

    entailer!.

    + (* Postcondition entailment *)
    
    repeat match goal with |- context [@data_at CompSpecs ?a ?b ?c] =>
          replace (@data_at CompSpecs a b c) with 
                  (@data_at env_graph_gc.CompSpecs a b c)
         by (change_compspecs CompSpecs; reflexivity)
    end.

    split.

    2 : { split.
          - unfold calc. rewrite map_length. rewrite <- ps_size. unfold Z.shiftl. simpl. rep_lia.
          - unfold vals. now rewrite to_from_vec.  }

    intros rho. entailer!.

    pose (fds := map rep_field ps).
    assert (R3 : NO_SCAN_TAG <= Z.of_nat t -> ~ In None fds). rewrite NO_SCAN_TAG_eq. rep_lia.
    assert (R2 : 0 < Zlength fds < two_power_pos 54). { unfold fds. rewrite Zlength_map.
    rewrite Zlength_correct. rewrite <- ps_size. unfold two_power_pos. simpl. lia. } 


    pose (v := new_copied_v gr 0). Exists (repNode v).
     pose (es := get_fields gr 0 ps 0).
     Exists (add_node gr 0 (newRaw v (Z.of_nat t) fds R1 R2 R3) es).

      
   (* Ensuring that there's enough space on the heap. *)
    assert (t_size : 0 <= 1 + Zlength fds <= total_space (nth_space (ti_heap tinfo) 0) - used_space (nth_space (ti_heap tinfo) 0)).
   { unfold nth_space. rewrite SPACE_NONEMPTY. simpl in *.
    unfold fds. 
    rewrite Zlength_map.
    rewrite Zlength_correct.
    rewrite <- ps_size. 
    unfold headroom in headroom_size.
    lia. } 
 
   Exists (graph_add.add_node_ti 0 tinfo _ t_size).
   assert (add_node_compatible gr (new_copied_v gr 0) es). 
   { eapply add_node_compatible_new. eapply in_graphs_has; eauto. eauto.  } 
       
   entailer!.

   *  (* Ensuring that the propositional part holds. *)
  split3.
   -- apply result_in_graph; eauto. 
   -- split3.
      ++ split. 
        ** unfold headroom. simpl. autorewrite with graph_add.
           unfold fds.
           rewrite map_length. rewrite Zlength_map. 
           rewrite Zlength_correct. rep_lia.
        **  destruct gc_cond. unfold gc_correct.sound_gc_graph, roots_compatible in *.
            intuition eauto.
        apply add_node_iso; eauto. (* ~In (inr (new_copied_v gr 0)) roots *)
        eapply new_node_roots; eauto. 
        unfold roots_compatible. eauto. 
       ++ simpl. rewrite <- H9. autorewrite with graph_add; eauto. unfold alloc; eauto. unfold vertex_address.
          destruct comp_g0 as (comp_start&comp_sh&comp_prev).
          unfold gen_start. simpl. rewrite comp_start. unfold vertex_offset.
          simpl. rewrite comp_prev. if_tac; try contradiction.
          rewrite isptr_eq. simpl. f_equal.
          assert (8 = Ptrofs.signed (Ptrofs.repr 8)) as eq8 by reflexivity.
          rewrite eq8 at 1.
          rewrite <- Ptrofs.add_signed.
          rewrite !Ptrofs.add_assoc; f_equal.
          rewrite ptrofs_add_repr. f_equal. unfold WORD_SIZE. rep_lia.
       ++ simpl. autorewrite with graph_add; eauto. unfold vertex_address.
          destruct comp_g0 as (comp_start&comp_sh&comp_prev).
          unfold gen_start. simpl. rewrite comp_start. unfold vertex_offset.
          simpl. rewrite comp_prev. if_tac; try contradiction.
          rewrite isptr_eq. simpl. congruence.


   -- apply add_node_gc_condition_prop_general; eauto.
   admit. 
    (* eapply in_graphs_has; eauto. *)
     * (* Ensuring that the spatial part holds. *)

    (* ti_token_rep tinfo *)
    rewrite add_node_heap_ti_token_rep.
    2 : { split. lia. simpl. rewrite SPACE_NONEMPTY. rewrite Zlength_cons.
        assert (X := Zlength_nonneg space_rest). lia. } 
    simpl.
    entailer!.
   
    autorewrite with graph_add.
    simpl.

    (* thread_info_type *)
    unfold_data_at (data_at sh env_graph_gc.thread_info_type _  _).
    autorewrite with graph_add.
    
    simpl. cancel.
    
    (** alloc *)
    assert ((Vptr b
    (Ptrofs.repr
       (alloc
          + Z.pos
              (Pos.of_succ_nat
                 (Datatypes.length
                    (map (fun p : rep_type => rep_type_val gr p) ps))
                 * 8)))) = offset_val
                 (WORD_SIZE
                    * used_space
                        (heap_head
                           (ti_heap (add_node_ti 0 tinfo (1 + Zlength fds) t_size))))
                 (space_start
                    (heap_head (ti_heap (add_node_ti 0 tinfo (1 + Zlength fds) t_size))))) as ->.
    { unfold alloc, fds, WORD_SIZE.  simpl. 
      autorewrite with graph_add. rewrite isptr_eq. simpl. f_equal. 
      rewrite !map_length. autorewrite with norm.
      rewrite Zlength_map. 
      rewrite Pos2Z.inj_mul.
      rewrite Zpos_P_of_succ_nat.
      rewrite <- Zlength_correct.
      rewrite <- Ptrofs.signed_repr with (z := Z.succ (Zlength ps) * 8).
      2 : { rewrite Zlength_correct. rewrite <- ps_size. rep_lia.   }
      rewrite <- Ptrofs.add_signed. rewrite Ptrofs.add_assoc. f_equal.
      rewrite Ptrofs.add_signed. 
      f_equal. 
      rewrite !Ptrofs.signed_repr. 
      rep_lia. 
      - rewrite Zlength_correct. rewrite <- ps_size. rep_lia. 
      - destruct (heap_head (ti_heap tinfo)) eqn:myspace. unfold MAX_SPACE_SIZE in space_upper_bound. simpl.
       simpl in space_upper_bound. 
       unfold Ptrofs.min_signed, Ptrofs.max_signed. simpl. lia.
 }
 simpl. autorewrite with graph_add. cancel.

    (** limit *)
    assert ( Vptr b (Ptrofs.repr limit) = offset_val
    (WORD_SIZE
       * total_space
           (heap_head
              (ti_heap (add_node_ti 0 tinfo (1 + Zlength fds) t_size))))
    (space_start
       (heap_head (ti_heap (add_node_ti 0 tinfo (1 + Zlength fds) t_size))))) as ->. 
    {  unfold limit, fds, WORD_SIZE.
       simpl. autorewrite with graph_add. 
       rewrite isptr_eq.  simpl. f_equal. 
       rewrite Ptrofs.repr_signed. f_equal.  }
      
    simpl. autorewrite with graph_add. cancel.

    (* spatial_graph.graph_rep *)
    rewrite add_node_spatial; eauto.
    2 : { unfold gc_condition_prop in gc_cond. apply gc_cond. }
    2 : {  unfold gc_condition_prop in gc_cond.
         unfold copy_compatible in gc_cond. unfold copied_vertex_existence.
         clear -gc_cond. apply gc_cond. } 
    cancel.

    (* heap_rest_rep *)
    unfold heap_rest_rep. 
    simpl. rewrite SPACE_NONEMPTY at 4. 
    rewrite upd_Znth0.
    simpl. 
    autorewrite with graph_add; eauto. 
    cancel.

    (* heap_struct_rep *)
    assert (Vptr b x' = space_start
    (heap_head (ti_heap tinfo))) as <- by eauto.
    autorewrite with graph_add. 
    rewrite SPACE_NONEMPTY at 2. simpl. 
    rewrite upd_Znth0. simpl.
    rewrite SPACE_NONEMPTY at 1. simpl.
    cancel. 

    (* space_rest_rep *)
    unfold space_rest_rep. simpl. 
    if_tac.
    { exfalso. 
    rewrite SPACE_NONEMPTY in *. simpl in *.
    rewrite isptr_eq in *. unfold nullval in *. simpl in *. 
    congruence. }  
    simpl. 
    rewrite SPACE_NONEMPTY at 1. simpl.
  
     unfold vertex_at.
    simpl. 
    apply sepcon_derives.
    { apply derives_refl'. f_equal. 
      - f_equal. 
      unfold fds. rewrite Zlength_map. rewrite Zlength_correct.
      simpl. 
      rewrite SPACE_NONEMPTY. simpl. lia. 
      - unfold offset_val. unfold field_address0.
      simpl. rewrite !SPACE_NONEMPTY. simpl. 
      rewrite isptr_eq. simpl.
      unfold field_address0 in H30. 
      if_tac in H30. 
      + f_equal. rewrite Ptrofs.add_assoc. f_equal. 
      unfold fds. rewrite Zlength_map.  rewrite ptrofs_add_repr.
      f_equal. rewrite Zlength_correct. unfold WORD_SIZE. rep_lia. 
      + simpl in H30. hnf in H30. destruct H30; contradiction.
 }

    unfold vals. rewrite to_from_vec.
    autorewrite with graph_add; eauto. 

    assert (Zlength
    (fields_new (add_node gr 0 (newRaw v (Z.of_nat t) fds R1 R2 R3) es)
       (newRaw v (Z.of_nat t) fds R1 R2 R3) (new_copied_v gr 0)) = Z.of_nat (Datatypes.length (map (fun p : rep_type => specs_library.rep_type_val gr p) ps)))
    as ->.
 { unfold fields_new.  simpl. rewrite Zlength_map. unfold make_fields.
   simpl. rewrite map_length. autorewrite with graph_add. unfold update_vlabel. if_tac; try congruence.
   rewrite Zlength_correct. rewrite make_fields'_eq_length. simpl. unfold fds.
   rewrite map_length. reflexivity. }

   rewrite !map_length.

   assert (space_sh (heap_head (ti_heap tinfo)) = nth_sh gr 0) as ->.
   { destruct comp_g0 as (comp_start&comp_sh&comp_prev).
   rewrite <- comp_sh. reflexivity. }

    assert (vertex_address gr (new_copied_v gr 0) = offset_val WORD_SIZE (Vptr b (Ptrofs.repr alloc))) as ->.
    { unfold vertex_address.
    destruct comp_g0 as (comp_start&comp_sh&comp_prev).
    unfold gen_start. simpl. rewrite comp_start. unfold vertex_offset.
    simpl. rewrite comp_prev. if_tac; try contradiction.
    rewrite isptr_eq. simpl. f_equal.
    unfold WORD_SIZE.
    assert (8 = Ptrofs.signed (Ptrofs.repr 8)) as eq8 by reflexivity.
    subst alloc.
    unfold WORD_SIZE.
    autorewrite with norm. rewrite eq8.
    assert (0 <= 8 * (used_space (heap_head (ti_heap tinfo)) + 1) <= Ptrofs.max_signed). 
    { unfold Ptrofs.max_signed. destruct (heap_head (ti_heap tinfo)). 
      simpl in *. unfold MAX_SPACE_SIZE in *. simpl in *. lia. 
    }

    rewrite <- Ptrofs.add_signed.  rewrite Ptrofs.add_assoc. f_equal. 
    rewrite !Ptrofs.add_signed. f_equal. rewrite <- !eq8.
    rewrite !Ptrofs.signed_repr; try rep_lia.
 } 
 
    rewrite offset_offset_val. simpl. autorewrite with norm.

    unfold fields_new. simpl.
    unfold fds. simpl. unfold make_fields. simpl. autorewrite with graph_add. 
    unfold update_vlabel. if_tac; try congruence. simpl.
    
    assert (map (field2val (add_node gr 0 (newRaw v (Z.of_nat t) (map rep_field ps) R1 R2 R3) es))
    (make_fields' (map rep_field ps) (new_copied_v gr 0) 0) = map (rep_type_val gr) ps) as ->.
    { subst es. 
    rewrite make_fields'_eq. rewrite map_map.
    simpl.

  assert (forall g x, 
    rep_type_val g (field_t_rep_type g x) = field2val g x
  ).
  { intros. destruct x; eauto. simpl. destruct s; eauto.    }
  remember ( add_node gr 0
  (newRaw v (Z.of_nat t) (map rep_field ps) R1 R2 R3)
  (get_fields gr 0 ps 0)) as g'.
  rewrite combine_map_snd with (f := rep_field). simpl. 
  rewrite map_map.  
  replace (map (rep_type_val gr) ps) with (map (fun x => rep_type_val gr (snd x)) (combine (nat_seq 0 (Datatypes.length (map rep_field ps))) ps) 
  ).
  2 : { clear. generalize 0%nat as n.  induction ps; try reflexivity. intros. simpl. f_equal.  eauto.  }


  apply map_ext_in.
  intros ? In_seq. destruct a. 
  simpl. destruct r; eauto. 
  simpl. subst. simpl. 
  erewrite add_node_dst_new. 
  3 : { rewrite get_fields_eq.
    apply filter_option_In_iff.
    apply in_map_iff.
    exists (n, repNode v0).
    simpl. split; try reflexivity.
  
    rewrite !map_length in *; eauto. 
   }
  autorewrite with graph_add; eauto. 
  - assert (HHH := in_graphs_has _ _ _ _ args_in_graph). 
  rewrite Forall_forall in HHH. 
  apply in_combine_r in In_seq. specialize (HHH _ In_seq). simpl in HHH. intuition.  
  -  apply nodup_getfields.
  } 

    replace (Vlong (Int64.repr (calc t (Datatypes.length ps))) :: map (fun p : rep_type => rep_type_val gr p) ps)
    with ([Vlong (Int64.repr (calc t (Datatypes.length ps)))] ++ map (fun p : rep_type => rep_type_val gr p) ps); try reflexivity.
    erewrite split2_data_at_Tarray_app; try reflexivity.
    2 : { rewrite Zlength_map. rewrite Zlength_cons. rewrite Zlength_nil. simpl.  rewrite Zlength_length. 
        simpl. lia. lia. }

    rewrite Zlength_cons. rewrite Zlength_nil. simpl. 
    apply sepcon_derives.
    - erewrite data_at_singleton_array_eq; try reflexivity.
      rewrite data_at_int_or_ptr_long.
      unfold header_new. simpl. apply derives_refl'. f_equal.
      autorewrite with norm. unfold calc.
      simpl. unfold Z2val.
      rewrite Zlength_map.
      rewrite Zlength_correct. reflexivity.
    - replace (1 + Z.of_nat (Datatypes.length ps) - 1) with (Z.of_nat (Datatypes.length ps)) by lia. 
       unfold field_address0. simpl. entailer!. autorewrite with norm.
       if_tac in H33.
       2: { hnf in H33. destruct H33; contradiction. }
       entailer!. 

  + (* Precondition:
     The precondition of the actual general alloc entails the precondition of n_arguments. *)
  intros. subst alloc limit.
  entailer!.

  unfold before_gc_thread_info_rep.
  unfold_data_at (data_at sh _ _ _).
  rewrite !isptr_eq. simpl. rewrite !Ptrofs.repr_signed. entailer!.
  unfold heap_rest_rep.

  rewrite SPACE_NONEMPTY . (* TODO: Tactic *) 
  simpl.

  unfold space_rest_rep at 1.
  if_tac.
  { exfalso. unfold nullval in *. rewrite isptr_eq in *. revert H21. simple_if_tac; congruence. }
  simpl. Intros. entailer!.
  rewrite isptr_eq. unfold offset_val.
  rewrite data_at__tarray.
  assert (HEADROOM := H4).
  unfold headroom in headroom_size.
  rewrite ps_size in headroom_size.
  assert (exists sp, 
        (total_space (heap_head (ti_heap tinfo)) -
         used_space (heap_head (ti_heap tinfo))) = ((1 + Z.of_nat (length ps)) + sp) /\ 0 <= sp) as (sp&(sp_eq&sp_ge)).
 { exists (total_space (heap_head (ti_heap tinfo)) -
 used_space (heap_head (ti_heap tinfo)) - Z.of_nat (length ps) - 1).
    lia. }
  rewrite sp_eq.
  rewrite <- Zrepeat_app.
  erewrite split2_data_at_Tarray_app.
  2 : reflexivity.
  entailer!.
  rewrite Zlength_Zrepeat.
  entailer!.
  rewrite !map_length.
  entailer!.
  assert (Z.pos (Pos.of_succ_nat (Datatypes.length ps)) = 1 + Z.of_nat (Datatypes.length ps)) as -> by rep_lia.
  entailer!.

  * lia. 
  * rewrite Zlength_Zrepeat. rewrite Zlength_Zrepeat. lia.  
    -- lia.
    -- eauto. 
  * lia. 
  * eauto.
Admitted.


