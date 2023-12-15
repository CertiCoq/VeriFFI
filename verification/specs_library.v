(** * Library for Specifications

Kathrin Stark, 2021.
 *)

From VeriFFI.library Require Export base_representation.
From VeriFFI.verification Require Export graph_add.
From CertiGraph.CertiGC Require Import GCGraph gc_stack env_graph_gc spatial_gcgraph.
Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
(* TODO: Dependency. *)

Locate rep_type.
(** ** Library definitions for specifications *)

Require Import VST.floyd.proofauto.
From compcert Require Import export.Clightdefs.
(* Defining a canonical ident for [thread_info] so that
   we do not have to import a file compiled by Clightgen. *)
Definition _thread_info : ident := ident_of_string "thread_info".

(** Custom types for thread info *)
Definition thread_info_type := Tstruct _thread_info noattr.
Definition thread_info := tptr thread_info_type.

(* Representation of rep_type as a C value *)
Definition rep_type_val (g : graph) (x : rep_type) : val :=
match x with
| repZ y => odd_Z2val y
| repOut p => GC_Pointer2val p
| repNode v => vertex_address g v
end.

(** *** Graph Conditions *)

Definition array_type := int_or_ptr_type.

(** Propositional conditions from the garbage collector specification and getting the isomorphism property for the garbage collector:
The thread_info has to be a new one, roots and outlier stay preserved *)
Definition gc_condition_prop g (t_info: GCGraph.thread_info) roots outlier :=

graph_unmarked g /\ no_backward_edge g /\ no_dangling_dst g /\ ti_size_spec (ti_heap t_info) (** From garbage_collect_condition, removed that roots and finfo are compatible. *)
/\ safe_to_copy g
/\ graph_heap_compatible g (ti_heap t_info) /\ outlier_compatible g outlier 
/\ roots_compatible g outlier roots /\ rootpairs_compatible g (frames2rootpairs (ti_frames t_info)) roots
/\ gc_correct.sound_gc_graph g /\ copy_compatible g.

(*
Definition space_rest_rep {cs : compspecs} (sp: space): mpred :=
  if (Val.eq sp.(space_start) nullval)
  then emp
  else data_at_ (space_sh sp)
                (tarray int_or_ptr_type (sp.(total_space) - sp.(used_space)))
                (offset_val (WORD_SIZE * used_space sp) sp.(space_start)).

Definition heap_rest_rep {cs: compspecs} (hp: heap): mpred :=
  iter_sepcon space_rest_rep hp.(spaces).
*)

(* Full condition for the garbage collector *)
Definition full_gc g (t_info: GCGraph.thread_info) roots outlier ti sh gv :=
  (outlier_rep outlier * before_gc_thread_info_rep sh t_info ti 
  * ti_token_rep (ti_heap t_info) (ti_heap_p t_info) * graph_rep g 
  * gc_spec.all_string_constants Ers gv
  && !!gc_condition_prop g t_info roots outlier)%logic.

Lemma full_gc_fold:
  forall gv g t_info roots outlier ti sh,
  gc_condition_prop g t_info roots outlier ->
   outlier_rep outlier *
   before_gc_thread_info_rep sh t_info ti *
   ti_token_rep (ti_heap t_info) (ti_heap_p t_info) * 
   graph_rep g *
   gc_spec.all_string_constants Ers gv
  |--   full_gc g (t_info: GCGraph.thread_info) roots outlier ti sh gv.
Proof. intros. unfold full_gc. entailer!!.
Qed.

Definition frame_rep sh (fr vr prev: val) (al: list val) :=
  (*  fr is the address of the frame struct; vr is the local array address;
      prev is the previous top-of-stack; al is the list of valid values
  *)
  (data_at sh (Tstruct _stack_frame noattr)
    (offset_val (sizeof(int_or_ptr_type)*Zlength al) vr, (vr, prev)) fr
   * data_at sh (tarray int_or_ptr_type (Zlength al)) al vr)%logic.

Definition frame_rep_ sh (fr vr prev: val) (n: Z) :=
  (*  fr is the address of the frame struct; vr is the local array address;
      prev is the previous top-of-stack; n is the size of the local array;
      there are no valid values at present
  *)
  (data_at sh (Tstruct _stack_frame noattr)
    (Vundef, (vr, prev)) fr
   * data_at_ sh (tarray int_or_ptr_type n) vr)%logic.

Definition frame_rep_surplus sh (fr vr: val) (n: Z) (al: list val) :=
   !! field_compatible (tarray int_or_ptr_type n) [] vr 
   && data_at_ sh (tarray int_or_ptr_type (n-Zlength al))
       (field_address0 (tarray int_or_ptr_type n) [ArraySubsc (Zlength al)] vr) .

Lemma frame_rep_fold: forall sh fr vr prev n al,
  Zlength al <= n ->
  data_at sh (Tstruct _stack_frame noattr)
    (offset_val (sizeof(int_or_ptr_type)*Zlength al) vr, (vr, prev)) fr
   * data_at sh (tarray int_or_ptr_type n) (al++Zrepeat Vundef (n-Zlength al)) vr
  |-- frame_rep sh fr vr prev al
      * frame_rep_surplus sh fr vr n al.
Proof.
intros. unfold frame_rep, frame_rep_surplus.
 entailer!.
 erewrite split2_data_at_Tarray_app.
 2: reflexivity. 2: list_solve.
 cancel.
Qed.

Lemma frame_rep__fold: forall sh fr vr prev n any,
    data_at sh (Tstruct _stack_frame noattr) (any, (vr, prev)) fr
   * data_at_ sh (tarray int_or_ptr_type n) vr
  |-- frame_rep_ sh fr vr prev n.
Proof. intros. unfold frame_rep_. cancel.
  do 2 unfold_data_at (data_at _ _ _ _). cancel.
Qed.

Definition root_t_of_rep_type (v: rep_type) : root_t :=
   match v with
   | repZ i => inl (inl i)
   | repOut p => inl (inr p)
   | repNode x => inr x
  end.

Definition rep_type_of_root_t (v: root_t) : rep_type :=
  match v with
  | inl (inl i) => repZ i 
  | inl (inr p) => repOut p 
  | inr x => repNode x 
  end.


Lemma root_t_of_rep_type_of_root_t: forall r, root_t_of_rep_type (rep_type_of_root_t r) = r.
Proof.
destruct r; try destruct s; simpl; auto.
Qed.

Lemma rep_type_of_root_t_of_rep_type: forall r, rep_type_of_root_t (root_t_of_rep_type r) = r.
Proof.
destruct r; auto.
Qed.

Lemma graph_iso_Zlength: 
  forall (g1 :graph) (roots1: list root_t)
         (g2: graph) (roots2: list root_t),
    gc_graph_iso g1 roots1 g2 roots2 ->
    Zlength roots1 = Zlength roots2.
Proof.
intros.
destruct H as [? [? [? [? [? _ ] ] ] ] ].
subst.
list_solve.
Qed.

(* BEGIN patch for any VST versions 2.12,2.13  (perhaps won't be needed in 2.14) *)

Lemma typed_false_tlong_Vlong:
  forall v, typed_false tlong (Vlong v) -> v = Int64.zero.
Proof.
intros.
unfold typed_false, strict_bool_val in H. simpl in H.
pose proof (Int64.eq_spec v Int64.zero).
destruct (Int64.eq v Int64.zero); auto. discriminate.
Qed.

Lemma repr_inj_signed64:
  forall i j,
    Int64.min_signed <= i <= Int.max_signed ->
    Int64.min_signed <= j <= Int.max_signed ->
    Int64.repr i = Int64.repr j -> i=j.
Proof.
intros.
rewrite <- (Int64.signed_repr i) by rep_lia.
rewrite <- (Int64.signed_repr j) by rep_lia.
congruence.
Qed.

Ltac do_repr_inj H ::=
   simpl typeof in H;  (* this 'simpl' should be fine, since its argument is just clightgen-produced ASTs *)
   cbv delta [Int64.zero Int.zero] in H;
   lazymatch type of H with
      | typed_true _ ?A => 
           change (typed_true tuint) with (typed_true tint) in H;
           change (typed_true tulong) with (typed_true tlong) in H;
          let B := eval hnf in A in change A with B in H;
          try first
               [ simple apply typed_true_of_bool' in H
               | simple apply typed_true_ptr in H
               | simple apply typed_true_ptr' in H
               | apply typed_true_negb_bool_val_p in H
               | simple apply typed_true_tint_Vint in H
               | apply typed_true_nullptr3 in H
               | simple apply typed_true_Ceq_eq' in H
               | apply typed_true_nullptr4 in H
               | simple apply typed_true_Cne_neq' in H
               | simple apply typed_true_tlong_Vlong in H
              ]
      | typed_false _ ?A => 
           change (typed_false tuint) with (typed_false tint) in H;
           change (typed_false tulong) with (typed_false tlong) in H;
           let B := eval hnf in A in change A with B in H;
           try first
               [ simple apply typed_false_of_bool' in H
               | simple apply typed_false_ptr_e in H
               | simple apply typed_false_negb_bool_val_p in H; [| solve [auto ] ]
               | apply typed_false_negb_bool_val_p' in H
               | simple apply typed_false_tint_Vint in H
               | apply typed_false_nullptr3 in H
               | simple apply typed_false_Ceq_neq' in H
               | apply typed_false_nullptr4 in H
               | simple apply typed_false_Cne_eq' in H
               | simple apply typed_false_tlong_Vlong in H
               ]
     | _ => idtac
    end;
   rewrite ?ptrofs_to_int_repr in H;
   rewrite ?ptrofs_to_int64_repr in H by reflexivity;
   repeat (rewrite -> negb_true_iff in H || rewrite -> negb_false_iff in H);
   try apply int_eq_e in H;
   try apply int64_eq_e in H;
   try apply ptrofs_eq_e in H;
   match type of H with
(*  don't do these, because they weaken the statement, unfortunately.
          | _ <> _ => apply repr_neq_e (*int_eq_false_e*) in H
          | _ <> _ => apply repr64_neq_e in H
*)
          | _ <> _ => let H' := fresh H "'" in assert (H' := repr_neq_e _ _ H)
          | _ <> _ => let H' := fresh H "'" in assert (H' := repr64_neq_e _ _ H)
          | Int.eq _ _ = false => apply int_eq_false_e in H
          | Int64.eq _ _ = false => apply int64_eq_false_e in H
          | Ptrofs.eq _ _ = false => apply ptrofs_eq_false_e in H
          | _ => idtac
  end;
  first [ simple apply repr_inj_signed in H; [ | rep_lia | rep_lia ]
         | simple apply repr_inj_unsigned in H; [ | rep_lia | rep_lia ]
         | simple apply repr_inj_signed64 in H; [ | rep_lia | rep_lia ]
         | simple apply repr_inj_unsigned64 in H; [ | rep_lia | rep_lia ]
         | simple apply repr_inj_signed' in H; [ | rep_lia | rep_lia ]
         | simple apply repr_inj_unsigned' in H; [ | rep_lia | rep_lia ]
         | simple apply ltu_repr in H; [ | rep_lia | rep_lia]
         | simple apply ltu_repr64 in H; [ | rep_lia | rep_lia]
         | simple apply ltu_repr_false in H; [ | rep_lia | rep_lia]
         | simple apply ltu_repr_false64 in H; [ | rep_lia | rep_lia]
         | simple apply ltu_inv in H; cleanup_repr H
         | simple apply ltu_inv64 in H; cleanup_repr H
         | simple apply ltu_false_inv in H; cleanup_repr H
         | simple apply ltu_false_inv64 in H; cleanup_repr H
         | simple apply lt_repr in H; [ | rep_lia | rep_lia]
         | simple apply lt_repr64 in H; [ | rep_lia | rep_lia]
         | simple apply lt_repr_false in H; [ | rep_lia | rep_lia]
         | simple apply lt_repr_false64 in H; [ | rep_lia | rep_lia]
         | simple apply lt_inv in H; cleanup_repr H
         | simple apply lt_inv64 in H; cleanup_repr H
         | simple apply lt_false_inv in H; cleanup_repr H
         | simple apply lt_false_inv64 in H; cleanup_repr H
         | idtac
         ];
    rewrite ?Byte_signed_lem, ?Byte_signed_lem',
                 ?int_repr_byte_signed_eq0, ?int_repr_byte_signed_eq0
      in H.

