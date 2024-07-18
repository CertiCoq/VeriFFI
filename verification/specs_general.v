(** * General Specification of alloc functions

Kathrin Stark, 2021.

This file contains a general specification for the alloc function,
using a representation of constructors.
*)
Require Import Coq.Lists.List.
Import ListNotations.
Import SigTNotations.

Require Import VST.floyd.proofauto.
Require Import CertiGraph.CertiGC.GCGraph.

From VeriFFI Require Export library.base_representation.
From VeriFFI Require Export library.meta library.modelled.
From VeriFFI Require Export verification.graph_add.
(* From VeriFFI Require Export verification.example.glue. *)
From VeriFFI Require Export verification.specs_library.
Import spatial_gcgraph.



(** ** 3. A General Specification *)

(** Generation of the in_graphs predicate, given the constructor or function arguments. *)
Fixpoint in_graphs {ann: Type -> Type} (ing: forall T, ann T -> InGraph T)
         (g : graph) outliers (c : reified ann) (xs : args c) (ps : list rep_type) : Prop :=
  match c as l return (args l -> Prop) with
  | TYPEPARAM f =>
      fun H => let (X_, xs') := H in
               let (R_, xs') := xs' in
        in_graphs ing g outliers (f X_ R_) xs' ps
  | ARG X_ R_ f =>
      fun H  => let (x, xs') := H in
      match ps with
      | [] => False
      | p :: ps' => @is_in_graph X_ (ing X_ R_) g outliers x p /\ @in_graphs _ ing g outliers (f x) xs' ps'
      end
  | RES x _ => fun _ => ps = nil
  end xs.

Definition ctor_in_graphs := in_graphs (@field_in_graph).
Definition foreign_in_graphs := in_graphs (@foreign_in_graph).

(** List of [tulong] depending on the number of arguments
    represented in memory, needed for the parameters. *)
Fixpoint get_size (c : reified ctor_ann) (xs : args c) : nat :=
  match c as l return (args l -> nat) with
  | TYPEPARAM f =>
      fun H => let (X_, xs') := H in let (R_, xs') := xs' in get_size (f X_ R_) xs'
  | ARG _ X_ f => fun H  => let (x, xs') := H in S (get_size (f x) xs')
  | RES _ x => fun _ => O
  end xs.

Definition get_tulongs (c : reified ctor_ann) (xs : args c) : list type :=
  repeat tulong (get_size c xs).

Lemma ctor_in_graphs_size (g : graph) outliers (c : reified ctor_ann) (xs : args c) (ps : list rep_type) :
  ctor_in_graphs g outliers c xs ps -> get_size c xs = length ps.
Proof.
   unfold ctor_in_graphs.
  revert ps.
  induction c; simpl in *; intros; try (destruct xs); try (destruct s); eauto.
  all: destruct ps; simpl; intuition eauto; try congruence.
Qed.

(** Custom notation with a list for PRE to make the specification better readable. *)
Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE''  xs P 'POST' [ tz ] Q" :=
     (NDmk_funspec (xs, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Definition get_c_typesig
           (c : reified foreign_ann)
           (arity : nat) : compcert_rmaps.typesig :=
  (cons thread_info (repeat int_or_ptr_type arity), int_or_ptr_type).

Definition fn_desc_to_funspec (d : fn_desc) : ident * funspec :=
  DECLARE (ident_of_string (c_name d))
  WITH gv : globals, g : graph, roots : GCGraph.roots_t, sh : share,
       xs : args (fn_type_reified d), ps : list rep_type, ti : val,
       outlier : GCGraph.outlier_t, t_info : GCGraph.thread_info
   PRE' (cons thread_info (repeat int_or_ptr_type (fn_arity d)))
      PROP (writable_share sh ;
            foreign_in_graphs g outlier (fn_type_reified d) xs ps)
      (PARAMSx (ti :: map (rep_type_val g) ps)
       (GLOBALSx [gv]
        (SEPx (full_gc g t_info roots outlier ti sh gv :: library.mem_mgr gv :: nil))))
   POST [ int_or_ptr_type ]
     EX (p' : rep_type) (g' : graph) (roots': GCGraph.roots_t) (t_info' : GCGraph.thread_info),
       PROP (let r := result (fn_type_reified d) xs in
             @is_in_graph r.1 (@foreign_in_graph r.1 r.2) g'
               outlier (model_fn d xs) p' ;
             gc_graph_iso g roots g' roots')
       RETURN  (rep_type_val g' p')
       SEP (full_gc g' t_info' roots' outlier ti sh gv; library.mem_mgr gv).

Definition headroom (ti: GCGraph.thread_info) : Z :=
   let g0 := heap_head (ti_heap ti) in
      total_space g0 - used_space g0.

(*
Definition alloc_make_nat_S : funspec :=
  WITH gv : globals, g : graph, p : rep_type,
       x: nat, roots : roots_t, sh : share,
       ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
  PRE'  [thread_info ; tulong]
     PROP (is_in_graph g x p ;
           writable_share sh)
     PARAMS (ti ; rep_type_val g p)
     SEP (full_gc g t_info roots outlier ti sh)
  POST [ tulong ]
    EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info),
      PROP (is_in_graph g' (S x) p' ;
            gc_graph_iso g roots g' roots)
      RETURN  (rep_type_val g' p')
      SEP (full_gc g' t_info' roots outlier ti sh).
        *)

(* move ps to the spec args somehow instead of WITH args *)
Definition alloc_make_spec_general
           (c : ctor_desc)
           (n : nat) : (* ident * *) funspec :=
    WITH gv : globals, g : graph, ps : list rep_type,
         xs : args (ctor_reified c), roots : roots_t, sh : share,
         ti : val, outlier : outlier_t, t_info : GCGraph.thread_info
    PRE'  (thread_info :: repeat int_or_ptr_type n)
       PROP (n = get_size (ctor_reified c) xs ;
             ctor_in_graphs g outlier _ xs ps ;
             (Z.of_nat n) < headroom t_info ;
             writable_share sh)
       (PARAMSx (ti :: map (fun p => rep_type_val g p) ps)
       (GLOBALSx [gv]
       (SEPx (full_gc g t_info roots outlier ti sh gv :: nil))))
    POST [ int_or_ptr_type ]
      EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info),
        PROP (let r := result (ctor_reified c) xs in
              @is_in_graph r.1 (@field_in_graph r.1 r.2) g' outlier (ctor_reflected c xs) p' ;
              headroom t_info' = headroom t_info - Z.of_nat (S n);
              gc_graph_iso g roots g' roots;
              ti_frames t_info = ti_frames t_info'
              )
        RETURN  (rep_type_val g' p')
        SEP (full_gc g' t_info' roots outlier ti sh gv).



(* Implications can be removed. *)
Lemma intro_prop_through_close_precondition :
  forall {cs: compspecs} {Espec : OracleKind} Delta (p1 : Prop) f ps LS sf c post,
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

Ltac concretize_PARAMS :=
unfold ctor_in_graphs, foreign_in_graphs in *;
lazymatch goal with
| xs: args _, H0: in_graphs _ _ _ _ ?xs' ?ps  |- _ =>
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
   |  H: in_graphs _ _ _ _ _ (_ :: _) |- _ => destruct H
   |  H: in_graphs _ _ _ _ _ ps |- _ => hnf in H; subst ps
   end
   | _ => idtac
end;
 change (in_graphs (@field_in_graph)) with ctor_in_graphs in *;
 change (in_graphs (@foreign_in_graph)) with foreign_in_graphs in *.

Ltac start_function' :=
  start_function1;
  repeat (simple apply intro_prop_through_close_precondition; intro);
  concretize_PARAMS;
  start_function2;
  start_function3.

Definition need_composites := [gc_stack._space; gc_stack._heap; gc_stack._stack_frame; gc_stack._thread_info].

Definition filtered_composites : list composite_definition :=
  List.filter (fun c => match c with Composite i _ _ _ =>
                   in_dec Pos.eq_dec i need_composites end) gc_stack.composites.

Definition filtered_prog :=
  Clightdefs.mkprogram filtered_composites nil nil gc_stack._main Logic.I.


Definition filteredCompSpecs : compspecs.
let c := constr:(prog_types filtered_prog) in
let c := eval unfold prog_types, Clightdefs.mkprogram in c in
let c := eval hnf in c in
let c := eval simpl in c in
let comp' := make_composite_env c in
  match comp' with
  | Errors.OK ?ce => make_compspecs_cenv ce
  end.
Defined.


#[export] Instance CCE3: change_composite_env env_graph_gc.CompSpecs filteredCompSpecs.
make_cs_preserve env_graph_gc.CompSpecs filteredCompSpecs.
Defined.

Lemma is_pointer_or_integer_rep_type_val:
  forall {A} `{InG: InGraph A} g outlier (n: A) p,
   is_in_graph g outlier n p ->
   graph_rep g |-- !! is_pointer_or_integer (rep_type_val g p).
Proof.
intros.
destruct p; simpl; auto.
destruct g0; simpl; auto.
apply has_v in H.
sep_apply (graph_rep_valid_int_or_ptr g v).
entailer!!.
hnf in H0|-*.
destruct (vertex_address g v); auto.
destruct Archi.ptr64; auto.
Qed.

Lemma before_gc_thread_info_rep_fold:
  forall sh t_info (ti: val),
  @data_at env_graph_gc.CompSpecs sh env_graph_gc.thread_info_type
   (offset_val (WORD_SIZE * used_space (heap_head (ti_heap t_info))) (space_start (heap_head (ti_heap t_info))),
    (offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info))) (space_start (heap_head (ti_heap t_info))),
     (ti_heap_p t_info,
      (ti_args t_info,
        (spatial_gcgraph.ti_fp t_info, (Vptrofs (ti_nalloc t_info), nullval)))))) ti
  * spatial_gcgraph.frames_rep sh (ti_frames t_info)
  * spatial_gcgraph.heap_struct_rep sh
      ((space_start (heap_head (ti_heap t_info)),
       (Vundef,
       (offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info))) (space_start (heap_head (ti_heap t_info))),
         offset_val (WORD_SIZE * total_space (heap_head (ti_heap t_info))) (space_start (heap_head (ti_heap t_info))))))
         :: map spatial_gcgraph.space_tri (tl (spaces (ti_heap t_info))))
      (ti_heap_p t_info)
  * spatial_gcgraph.heap_rest_rep (ti_heap t_info)
  |-- before_gc_thread_info_rep sh t_info ti.
Proof.
 intros.
 unfold before_gc_thread_info_rep.
 unfold spatial_gcgraph.before_gc_thread_info_rep.
 cancel.
Qed.


Lemma frames_rep_cons:
 forall sh vf vr vl frames
  (SIZE: WORD_SIZE * Zlength vl <= Ptrofs.max_signed),
 (frame_rep sh vf vr (spatial_gcgraph.frames_p frames) vl *
  spatial_gcgraph.frames_rep sh frames)%logic
 = spatial_gcgraph.frames_rep sh
     ({|fr_adr:=vf; fr_root:=vr; fr_roots := vl|}::frames).
Proof.
intros.
unfold frame_rep.
simpl.
unfold tarray.
unfold spatial_gcgraph.frames_rep.
unfold frames2rootpairs.
simpl map.
change (concat (?A :: ?B)) with (A ++ concat B).
fold (frames2rootpairs frames).
unfold spatial_gcgraph.roots_rep.
rewrite iter_sepcon.iter_sepcon_app_sepcon.
unfold spatial_gcgraph.frames_shell_rep; fold (spatial_gcgraph.frames_shell_rep sh frames).
unfold frame2rootpairs.
simpl.
match goal with |- ?A = ?B =>
 transitivity (!! (@field_compatible0 env_graph_gc.CompSpecs (tarray int_or_ptr_type (@Zlength val vl)) [] vr) && A)%logic
 end.
   apply pred_ext; entailer!.
 normalize.
 apply andp_prop_ext. tauto.
 intro.
 rewrite spatial_gcgraph.iter_sepcon_frame2rootpairs' by auto.
replace  (field_address0 (tarray int_or_ptr_type (Zlength vl)) (SUB Zlength vl) vr)
with (offset_val (8 * Zlength vl) vr).
2:{ unfold field_address0.
  rewrite if_true. simpl. auto.
   eapply field_compatible0_cons_Tarray; [ | apply H| ].
   reflexivity. rep_lia.
}
apply pred_ext; cancel.
Qed.

Lemma frames_rep_push:
 forall sh vf vr vl frames
  (SIZE: WORD_SIZE * Zlength vl <= Ptrofs.max_signed),
frame_rep sh vf vr (spatial_gcgraph.frames_p frames) vl *
spatial_gcgraph.frames_rep sh frames
|-- spatial_gcgraph.frames_rep sh
     ({|fr_adr:=vf; fr_root:=vr; fr_roots := vl|}::frames).
Proof.
intros.
rewrite frames_rep_cons by auto. auto.
Qed.


Lemma frames_rep_pop:
 forall sh vf vr vl frames
  (SIZE: WORD_SIZE * Zlength vl <= Ptrofs.max_signed),
 spatial_gcgraph.frames_rep sh
     ({|fr_adr:=vf; fr_root:=vr; fr_roots := vl|}::frames)
|-- frame_rep sh vf vr (spatial_gcgraph.frames_p frames) vl *
    spatial_gcgraph.frames_rep sh frames.
Proof.
intros.
rewrite frames_rep_cons by auto. auto.
Qed.


Lemma headroom_check {cs: compspecs}:
 forall (n: Z) (hh: space) (startb: block) (starti: ptrofs),
  0 <= n <= Int64.max_signed ->
  typed_false tint
       match
         sem_unary_operation Onotbool tint
            (force_val
              (both_long (fun n1 n2 : int64 => Some (bool2val (negb (Int64.ltu n2 n1))))
                 sem_cast_pointer sem_cast_pointer (Vlong (Int64.repr n))
                 (force_val
                    (sem_sub_pp
                       (Tpointer tvoid
                          {| attr_volatile := false; attr_alignas := Some 3%N |})
                       (Vptr startb
                          (Ptrofs.add starti
                             (Ptrofs.repr
                                (WORD_SIZE * total_space hh))))
                       (Vptr startb
                          (Ptrofs.add starti
                             (Ptrofs.repr
                                (WORD_SIZE * used_space hh))))))))
       with
       | Some v' => v'
       | None => Vundef
       end ->
  total_space hh - used_space hh >= n.
Proof.
intros * H7 H8.
    assert (ORDER := space_order hh).
    assert (UB := space_upper_bound hh).
    set (tot := total_space hh) in *. clearbody tot.
    set (use := used_space hh) in *. clearbody use.
    simpl in H8.
    unfold sem_sub_pp in H8. simpl in *. rewrite if_true in H8 by auto. simpl in H8.
(*     rewrite Int.signed_repr in H8 by auto.*)
    destruct (Int64.ltu _ _) eqn:?H in H8; try discriminate.
    unfold Int64.ltu in H.
    if_tac in H; try discriminate. clear H H8.
    rewrite !(Ptrofs.add_commut starti), Ptrofs.sub_shifted, ptrofs_sub_repr in H0.
    unfold MAX_SPACE_SIZE in *. simpl in UB.
    rewrite <- Z.mul_sub_distr_l in H0.
    change WORD_SIZE with 8 in *.
    rewrite ptrofs_divs_repr in H0 by rep_lia.
    rewrite ptrofs_to_int64_repr in H0 by reflexivity.
    rewrite Z.mul_comm, Z.quot_mul in H0 by lia.
    rewrite !Int64.unsigned_repr in H0 by rep_lia.
    auto.
Qed.



Ltac sep_apply_compspecs cs H :=
  generalize H;
  limited_change_compspecs cs; (* Bug?  If there's no compspecs at all in H or the goal,
    then this fails, but perhaps in that case it should succeed. *)
  let Hx := fresh "Hx" in  intro Hx; sep_apply Hx; clear Hx.

Lemma space_start_isptr':
  forall [g tinfo roots outlier],
  gc_condition_prop g tinfo roots outlier ->
  isptr (space_start (heap_head (ti_heap tinfo))).
Proof.
 intros * GCP.
    red in GCP; decompose [and] GCP.
    destruct (heap_head_cons (ti_heap tinfo)) as [s [l [C1 C2]  ] ].
    rewrite C2.
    replace s with (Znth 0 (spaces (ti_heap tinfo))) by (rewrite C1; reflexivity).
    apply space_start_isptr with g; auto; try apply H1.
    rewrite C1; clear; list_solve.
    apply graph_has_gen_O.
Qed.

Local Open Scope logic.
Lemma semax_frame_PQR':
  forall Q2 R2 Espec {cs: compspecs} Delta R1 P Q S c,
     closed_wrt_modvars c (LOCALx Q2 (SEPx R2)) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R1))) c
                     (normal_ret_assert S) ->
     @semax cs Espec Delta (PROPx P (LOCALx (Q++Q2) (SEPx (R1++R2)))) c
                     (normal_ret_assert (sepcon S (PROPx nil (LOCALx Q2 (SEPx R2))))).
Proof.
intros.
replace (PROPx P (LOCALx (Q++Q2) (SEPx (R1 ++ R2))))
   with (PROPx P (LOCALx Q (SEPx (R1))) * (LOCALx Q2 (SEPx R2))).
eapply semax_pre_post; try (apply semax_frame; try eassumption).
apply andp_left2; auto.
apply andp_left2. intro rho; simpl; normalize.
 unfold PROPx, SEPx, LOCALx, local, lift1.
normalize.
simpl; normalize.
simpl; normalize.
simpl; normalize.
clear.
extensionality rho.
simpl.
unfold PROPx, LOCALx, local, lift1, SEPx.
rewrite fold_right_sepcon_app.
simpl. normalize.
f_equal.
rewrite map_app. rewrite fold_right_and_app.
apply pred_ext; normalize.
Qed.

Lemma semax_frame_PQR'':
  forall Q1 Q2 R1 R2 S1 Espec {cs: compspecs} Delta P Q R S c,
     closed_wrt_modvars c (LOCALx Q2 (SEPx R2)) ->
     PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx (Q1++Q2) (SEPx (R1++R2))) ->
     S1 * (PROPx nil (LOCALx Q2 (SEPx R2))) |-- S ->
     @semax cs Espec Delta (PROPx P (LOCALx Q1 (SEPx R1))) c
                     (normal_ret_assert S1) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c
                     (normal_ret_assert S).
Proof.
intros.
eapply semax_pre_post'; [ | | apply semax_frame_PQR' with (P:=P)].
apply andp_left2; eassumption.
apply andp_left2; eassumption.
auto.
auto.
Qed.

Definition __ALLOC : ident := ident_of_string "_ALLOC".
Definition __LIMIT : ident := ident_of_string "_LIMIT".
Definition __FRAME : ident := ident_of_string "_FRAME".
Definition _tinfo : ident := ident_of_string "tinfo".
Definition _alloc : ident := ident_of_string "alloc".
Definition _limit : ident := ident_of_string "limit".
Definition _next : ident := ident_of_string "next".
Definition _nalloc : ident := ident_of_string "nalloc".
Definition _save0 : ident := ident_of_string "save0".
Definition _save1 : ident := ident_of_string "save1".
Definition _save2 : ident := ident_of_string "save2".
Definition _save3 : ident := ident_of_string "save3".
Definition _fp : ident := ident_of_string "fp".
Definition _prev : ident := ident_of_string "prev".
Definition _stack_frame : ident := ident_of_string "stack_frame".
Definition _thread_info : ident := ident_of_string "thread_info".
Definition _garbage_collect : ident := ident_of_string "garbage_collect".
Definition ___FRAME__ : ident := ident_of_string "__FRAME__".
Definition ___ROOT__ : ident := ident_of_string "__ROOT__".
Definition ___RTEMP__ : ident := ident_of_string "__RTEMP__".
Definition ___PREV__ : ident := ident_of_string "__PREV__".


Definition GC_SAVE1 :=
                (Ssequence
                  (Ssequence
                    (Sset __LIMIT
                      (Efield
                        (Ederef
                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                          (Tstruct _thread_info noattr)) _limit
                        (tptr (talignas 3%N (tptr tvoid)))))
                    (Sset __ALLOC
                      (Efield
                        (Ederef
                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                          (Tstruct _thread_info noattr)) _alloc
                        (tptr (talignas 3%N (tptr tvoid))))))
                  (Sifthenelse (Eunop Onotbool
                                 (Ebinop Ole (Etempvar _nalloc tulong)
                                   (Ebinop Osub
                                     (Etempvar __LIMIT (tptr (talignas 3%N (tptr tvoid))))
                                     (Etempvar __ALLOC (tptr (talignas 3%N (tptr tvoid))))
                                     tlong) tint) tint)
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                            (Tstruct _thread_info noattr)) _nalloc tulong)
                        (Etempvar _nalloc tulong))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                                          (Tstruct _thread_info noattr)) _fp
                                        (tptr (Tstruct _stack_frame noattr)))
                                      (Eaddrof
                                        (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                        (tptr (Tstruct _stack_frame noattr))))
                                    (Sassign
                                      (Efield
                                        (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                                        _next
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (Ebinop Oadd
                                        (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr (talignas 3%N (tptr tvoid))))))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                        (Econst_int (Int.repr 0) tint)
                                        (tptr (talignas 3%N (tptr tvoid))))
                                      (talignas 3%N (tptr tvoid)))
                                    (Etempvar _save0 (talignas 3%N (tptr tvoid)))))
                                (Scall None
                                  (Evar _garbage_collect (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _thread_info noattr))
                                                             Tnil) tvoid
                                                           cc_default))
                                  ((Etempvar _tinfo (tptr (Tstruct _thread_info noattr))) ::
                                   nil)))
                              (Sset ___RTEMP__
                                (Ecast
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    (tptr tvoid))
                                  (talignas 3%N (tptr tvoid)))))
                            (Sset _save0
                              (Ederef
                                (Ebinop Oadd
                                  (Evar ___ROOT__ (tarray (talignas 3%N (tptr tvoid)) 1))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr (talignas 3%N (tptr tvoid))))
                                (talignas 3%N (tptr tvoid)))))
                          (Sset ___PREV__
                            (Efield
                              (Evar ___FRAME__ (Tstruct _stack_frame noattr))
                              _prev (tptr (Tstruct _stack_frame noattr)))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                              (Tstruct _thread_info noattr)) _fp
                            (tptr (Tstruct _stack_frame noattr)))
                          (Etempvar ___PREV__ (tptr (Tstruct _stack_frame noattr))))))
                    Sskip)).

Ltac get_rep_temps ti nalloc Q :=
 lazymatch Q with
 | nil => constr:(Q)
 | temp ti ?v :: ?r => let r' := get_rep_temps ti nalloc r in constr:(temp ti v :: r')
 | temp nalloc ?v :: ?r => let r' := get_rep_temps ti nalloc r in constr:(temp nalloc v :: r')
 | temp ?i (rep_type_val ?g ?v) :: ?r =>
    let r' := get_rep_temps ti nalloc r in constr:(temp i (rep_type_val g v) :: r')
 | temp ?i ?v :: ?r =>
    get_rep_temps ti nalloc r
 | ?t :: ?r => let r' := get_rep_temps ti nalloc r in constr:(t::r')
 end.

Ltac get_nonrep_temps ti nalloc Q :=
 match Q with
 | nil => constr:(Q)
 | temp ti _ :: ?r => get_nonrep_temps ti nalloc r
 | temp nalloc _ :: ?r => get_nonrep_temps ti nalloc r
 | temp ?i (rep_type_val ?g ?v) :: ?r =>
    get_nonrep_temps ti nalloc r
 | temp ?i ?x :: ?r =>
    let r' := get_nonrep_temps ti nalloc r in constr:(temp i x ::r')
 | _ :: ?r => get_nonrep_temps ti nalloc r
 end.

Ltac get_gc_mpreds R :=
 lazymatch R with
 | nil => constr:(R)
 | ?r1 :: ?r =>
   lazymatch r1 with
   | full_gc _ _ _ _ _ _ _  => let r' := get_gc_mpreds r in constr:(r1::r')
   | frame_rep_ _ _ _ _ _ => let r' := get_gc_mpreds r in constr:(r1::r')
   | library.mem_mgr _ => let r' := get_gc_mpreds r in constr:(r1::r')
   | is_in_graph _ _ => let r' := get_gc_mpreds r in constr:(r1::r')
   | _ => get_gc_mpreds r
   end
 end.

Ltac get_nongc_mpreds R :=
 lazymatch R with
 | nil => constr:(R)
 | ?r1 :: ?r =>
   lazymatch r1 with
   | full_gc _ _ _ _ _ _ _  => get_nongc_mpreds r
   | frame_rep_ _ _ _ _ _ => get_nongc_mpreds r
   | library.mem_mgr _ => get_nongc_mpreds r
   | is_in_graph _ _ => get_nongc_mpreds r
   | _ => let r' := get_nongc_mpreds r in constr:(r1::r')
   end
 end.

Lemma perhaps_gc_1_live_root_aux:
 forall P Q R Q2 R2,
  (EX (g': graph) (v0': rep_type) (roots': roots_t) (t_info': GCGraph.thread_info),
   PROPx (P g' v0' roots' t_info')
    (LOCALx (Q g' v0' roots' t_info')
     (SEPx (R g' v0' roots' t_info')))) * (PROPx nil (LOCALx Q2 (SEPx R2))) |--
  (EX (g': graph) (v0': rep_type) (roots': roots_t) (t_info': GCGraph.thread_info),
     PROPx (P g' v0' roots' t_info')
    (LOCALx (Q g' v0' roots' t_info' ++ Q2)
     (SEPx (R g' v0' roots' t_info' ++ R2)))).
Proof.
intros.
Intros a b c d; Exists a b c d.
rewrite PROP_combine.
rewrite app_nil_r.
auto.
Qed.


Ltac solve_load_rule_evaluation ::=
  (* See: https://github.com/PrincetonUniversity/VST/issues/748 *)
  eapply JMeq_trans;
  [ clear;
    repeat
    match goal with
    | A : _ |- _ => clear A
    | A := _ |- _ => clear A
    end;
    match goal with
    | |- JMeq (@proj_reptype _ _ ?gfs _) _ =>
      remember_indexes gfs
    end;
    match goal with
    | |- JMeq (@proj_reptype ?cs ?t ?gfs ?v) _ =>
        let opaque_v := fresh "opaque_v" in
              remember v as opaque_v;
              change @proj_reptype with @proj_reptype';
              cbv - [ sublist.Znth Int.repr JMeq myfst mysnd];
              change @myfst with @fst;
              change @mysnd with @snd;
              subst opaque_v;
              repeat match goal with
                     | |- context [@fst ?a ?b (?c,?d)] =>
                              let u := eval hnf in (@fst a b (c,d)) in
                                 change_no_check (@fst a b (c,d)) with c
                     | |- context [@snd ?a ?b (?c,?d)] =>
                               let u := eval hnf in (@snd a b (c,d)) in
                                  change_no_check (@snd a b (c,d)) with d
                    end

        end;
        subst; apply JMeq_refl
  | canon_load_result; apply JMeq_refl ].

Ltac solve_store_rule_evaluation ::=
  (* See: https://github.com/PrincetonUniversity/VST/issues/748 *)
  match goal with |- @upd_reptype ?cs ?t ?gfs ?v0 ?v1 = ?B =>
   let rhs := fresh "rhs" in set (rhs := B);
  match type of rhs with ?A =>
   let a := fresh "a" in set (a:=A) in rhs;
    lazy beta zeta iota delta [reptype reptype_gen] in a;
    cbn in a; subst a
  end;
   let h0 := fresh "h0" in let h1 := fresh "h1" in
   set (h0:=v0 : @reptype cs t);
   set (h1:=v1 : @reptype cs (@nested_field_type cs t gfs));
   change (@upd_reptype cs t gfs h0 h1 = rhs);
   remember_indexes gfs;
   let j := fresh "j" in match type of h0 with ?J => set (j := J) in h0 end;
   lazy beta zeta iota delta in j; subst j;
   change @upd_reptype with @upd_reptype';
   cbv - [rhs h0 h1 Znth upd_Znth Zlength myfst mysnd];
   change @myfst with @fst;
   change @mysnd with @snd;
   try unfold v1 in h1;
   revert h1; simplify_casts; cbv zeta;
   subst rhs h0; subst_indexes gfs;
  repeat match goal with
            | |- context [fst (@pair ?t1 ?t2 ?A ?B)] => change (fst(@pair t1 t2 A B)) with A
            | |- context [snd(@pair ?t1 ?t2 ?A ?B)] => change (snd(@pair t1 t2 A B)) with B
            | |-  context [@pair ?t1 ?t2 _ _] =>
                      let u1 := eval compute in t1 in
                      let u2 := eval compute in t2 in
                      progress (change_no_check t1 with u1; change_no_check t2 with u2)
            end;
  apply eq_refl
  end.

Ltac SEP_field_at_strong_unify gfs ::=
  (* See: https://github.com/PrincetonUniversity/VST/issues/748 *)
  match goal with
  | |- @data_at_ ?cs ?sh ?t ?p = _ /\ _ =>
        change (@data_at_ cs sh t p) with (@data_at cs sh t (@default_val _ t) p);
         SEP_field_at_strong_unify' gfs
  | |- @field_at_ ?cs _ _ _ _ = _ /\ _ =>
        unfold field_at_; SEP_field_at_strong_unify' gfs
  | _ => SEP_field_at_strong_unify' gfs
  end.


Ltac simplify_func_tycontext' DD ::=
  (* More general version of simplify_func_tycontext that makes
    fewer assumptions about the form of DD.
   Compared to the one in floyd/semax_tactics.v, this one
  does not assume that DD is in the form of a func_tycontext *)
let D1 := fresh "D1" in
let Delta := fresh "Delta" in
let DS := fresh "Delta_specs" in
pose (D1 := DD);
pose (Delta := @abbreviate tycontext D1);
change DD with Delta;
hnf in D1;
match goal with D1 := mk_tycontext _ _ _ _ ?d _ |- _ =>
 let d' := make_ground_PTree d in
 pose (DS := @abbreviate (Maps.PTree.t funspec) d');
  change d with DS in D1;
 cbv beta iota zeta delta - [DS] in D1;
 subst D1;
 check_ground_Delta
end.

Definition GC_SAVE1_G := [gc_spec.garbage_collect_spec].

Definition GC_SAVE1_tycontext :=
 mk_tycontext
  (make_tycontext_t [(_tinfo, (tptr (Tstruct _thread_info noattr)))]
         [(_save0, (talignas 3%N (tptr tvoid)));
          (__ALLOC, (tptr (talignas 3%N (tptr tvoid))));
          (__LIMIT, (tptr (talignas 3%N (tptr tvoid))));
          (___PREV__, (tptr (Tstruct _stack_frame noattr)));
          (___RTEMP__, (talignas 3%N (tptr tvoid)));
          (_nalloc, tulong)])
  (make_tycontext_v [(___ROOT__, (tarray (talignas 3%N (tptr tvoid)) 1));
              (___FRAME__, (Tstruct _stack_frame noattr))])
  int_or_ptr_type
  (make_tycontext_g nil GC_SAVE1_G)
  (make_tycontext_s GC_SAVE1_G)
  (make_tycontext_a nil).

  Require Import VeriFFI.generator.Isomorphism.


Lemma semax_GC_SAVE1:
 forall (n: Z) (Espec : OracleKind)
  (gv : globals) (sh : share)
  (ti : val)
  (outlier : outlier_t)
  (v___ROOT__  v___FRAME__ : val)
  (SH : writable_share sh)
  (v0 : rep_type)
  (T0: Type)
  (m0 : T0)
  (IG0: InGraph T0)
  (g : graph)
  (t_info : GCGraph.thread_info)
  (roots : roots_t)
  (Hn: 0 <= n <= Int64.max_signed)
  (H2 : @is_in_graph _ IG0 g outlier m0 v0)
  (GCP : gc_condition_prop g t_info roots outlier)
  (STARTptr : isptr (space_start (heap_head (ti_heap t_info)))),
@semax filteredCompSpecs _ GC_SAVE1_tycontext (*(func_tycontext f_uint63_to_nat Vprog Gprog nil)*)
  (PROP ( )
   LOCAL (temp _nalloc (Vlong (Int64.repr n));
   temp _save0 (rep_type_val g v0);
   lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
   lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; temp _tinfo ti;
   gvars gv)
   SEP (full_gc g t_info roots outlier ti sh gv;
   frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info) 1;
   library.mem_mgr gv))
  GC_SAVE1
  (normal_ret_assert
     (EX (g' : graph) (v0' : rep_type) (roots' : roots_t)
      (t_info' : GCGraph.thread_info),
      PROP (headroom t_info' >= n; is_in_graph g' outlier m0 v0';
      gc_condition_prop g' t_info' roots' outlier;
      gc_graph_iso g roots g' roots';
      frame_shells_eq (ti_frames t_info) (ti_frames t_info'))
      LOCAL (temp _save0 (rep_type_val g' v0'); temp _nalloc (Vlong (Int64.repr n));
      lvar ___FRAME__ (Tstruct _stack_frame noattr) v___FRAME__;
      lvar ___ROOT__ (tarray int_or_ptr_type 1) v___ROOT__; temp _tinfo ti;
      gvars gv)
      SEP (full_gc g' t_info' roots' outlier ti sh gv;
      frame_rep_ Tsh v___FRAME__ v___ROOT__ (ti_fp t_info') 1;
      library.mem_mgr gv))%argsassert).
Proof.
intros.
assert (H5 := I).
assert (H4 := I).
assert (H0 := I).
assert (H1 := I).
assert (H := I).
unfold GC_SAVE1.
abbreviate_semax.
  unfold full_gc.
  unfold before_gc_thread_info_rep (*;  limited_change_compspecs CompSpecs*).
  Intros.
  limited_change_compspecs filteredCompSpecs.
  forward.
  forward.
  destruct (space_start (heap_head (ti_heap t_info))) eqn:STARTeq; try contradiction.
  rename b into startb; rename i into starti.
  forward_if.
 + apply prop_right; simpl. destruct (peq startb startb); try contradiction. auto.
 +
  forward.
  forward.
  unfold frame_rep_.
  Intros.
  limited_change_compspecs filteredCompSpecs.
  forward.
  forward.
  deadvars!.
  change (upd_Znth 0 _ _) with [rep_type_val g v0].
  change (Tpointer tvoid _) with int_or_ptr_type.
  assert_PROP (force_val (@sem_add_ptr_int filteredCompSpecs int_or_ptr_type Signed v___ROOT__ (Vint (Int.repr 1))) =
      offset_val (@sizeof filteredCompSpecs int_or_ptr_type * 1) v___ROOT__)  as H99;
      [ entailer! | rewrite H99; clear H99].
  sep_apply_compspecs filteredCompSpecs
      (frame_rep_fold sh v___FRAME__ v___ROOT__ (ti_fp t_info) 1 [rep_type_val g v0]).
  unfold ti_fp.
  sep_apply (frames_rep_cons sh v___FRAME__ v___ROOT__ [rep_type_val g v0] (ti_frames t_info)).
  compute; clear; congruence.
  set (frames'' := _ :: ti_frames t_info).
  pose (t_info' := {| ti_heap_p := ti_heap_p t_info; ti_heap := ti_heap t_info;
                      arg_size := arg_size t_info; ti_frames := frames'';
                      ti_nalloc := Ptrofs.repr n |}).
  change frames'' with (ti_frames t_info').
(*  rewrite Int64.signed_repr by rep_lia.*)
  change (ti_args t_info) with (ti_args t_info').
  change (ti_heap_p t_info) with (ti_heap_p t_info').
  clear H3.
  forward_call (Ers, sh, gv, ti, g, t_info', root_t_of_rep_type v0 :: roots, outlier).
  *
   unfold before_gc_thread_info_rep.
   rewrite <- STARTeq.
   change (ti_heap t_info) with (ti_heap t_info').
   change (ti_fp t_info') with v___FRAME__.
   change (ti_nalloc t_info') with (Ptrofs.repr n).
   replace (Vptrofs (Ptrofs.repr n)) with (Vlong (Int64.repr n))
     by (rewrite Vptrofs_unfold_true by reflexivity;
         rewrite ptrofs_to_int64_repr by reflexivity; auto).
  limited_change_compspecs filteredCompSpecs.
   cancel.
  * simpl.
    split3; try apply GCP.
    red in GCP.
    split3. apply GCP. 2: split; try apply GCP.
    --
     subst frames''; clear t_info'.
     unfold frames2rootpairs. simpl concat.
     unfold rootpairs_compatible. simpl.
     f_equal.  destruct v0; auto.
     change (rootpairs_compatible g (frames2rootpairs (ti_frames t_info)) roots).
     apply GCP.
    -- decompose [and] GCP; clear GCP.
       red in H7; decompose [and] H7; clear H7.
       destruct H11.
       split.
       ++ clear t_info' frames'' STARTptr STARTeq startb starti.
          unfold root_t_of_rep_type.
          destruct v0; auto.
          pose proof (outlier_compat _ _ _ _ H14 H2).
          red in H7|-*. simpl.
          change (?A :: ?B) with ([A]++B).
          apply incl_app; auto.
          apply incl_cons; auto. apply incl_nil.
       ++ destruct v0; try apply H11. constructor; auto.
          clear - H2. unfold is_in_graph in H2.
          apply has_v in H2; auto.
  * (* after the call to garbage_collect() *)
   Intros vret. destruct vret as [ [g3 t_info3] roots3].
   simpl snd in *. simpl fst in *.
   rename H9 into FSE. rename H10 into ROOM.
   forward.
   unfold before_gc_thread_info_rep.
   simpl in FSE. unfold frames'' in FSE.
   remember (ti_frames t_info3) as frames3.
   inversion FSE; clear FSE. subst r1 fr1.
   destruct fr2 as [a3 r3 s3]; simpl in H11, H12, H13.
   subst a3 r3.
   destruct s3 as [ | v0x s3]. exfalso; clear - H13; list_solve.
   destruct s3. 2: exfalso; clear - H13; list_solve.
   subst frames3.
   sep_apply (frames_rep_pop sh v___FRAME__ v___ROOT__ [v0x] r2).
   compute; clear; congruence.
   unfold frame_rep at 1.
   Intros. change (Zlength [_]) with 1.
   assert (roots_graph_compatible (root_t_of_rep_type v0 :: roots) g). {
       destruct GCP as [_ [ [ _ [ _ [ [ _ RGC ] _ ] ] ] _ ] ].
       destruct v0; try apply RGC.
       constructor; auto.
       red in H2.
       eapply has_v; eauto.
    }

   pose (t_info4 := {|
    ti_heap_p := ti_heap_p t_info3;
    ti_heap := ti_heap t_info3;
    ti_args := ti_args t_info3;
    arg_size := arg_size t_info3;
    ti_frames := r2;
    ti_nalloc := ti_nalloc t_info3
  |} ).


   assert (ISO: gc_graph_iso g (root_t_of_rep_type v0 :: roots) g3 roots3). {
     red in H6; decompose [and] H6.
     apply garbage_collect_isomorphism; auto; try apply GCP.
    }
   assert (exists v0', exists roots3',
        v0x = rep_type_val g3 v0' /\ is_in_graph g3 outlier m0 v0' /\ roots3 = root_t_of_rep_type v0' :: roots3'
        /\ gc_condition_prop g3 t_info4 roots3' outlier). {
       rewrite <- H14 in H3. simpl frames2rootpairs in H3. 
       

      destruct ISO as (vmap12&vmap21&emap12&emap21&roots_eq&ISO).
       simpl in roots_eq.
       exists (lift vmap12 v0). exists (map (root_map vmap12) roots).
       pose (roots3' := map (root_map vmap12) roots).

       assert (GCP3: gc_condition_prop g3 t_info4 roots3' outlier).  {
        unfold gc_condition_prop, garbage_collect_condition.
        change (ti_heap t_info4) with (ti_heap t_info3).
        repeat simple apply conj; try apply GCP; try apply H7; auto.
        - destruct H3 as [? [? [ ?  ? ] ] ].
          destruct H11.
          red; unfold roots_compatible; repeat simple apply conj; auto.
          + subst roots3'.  rewrite roots_eq in H10. 
        (*   rewrite <- H14 in H10. *)
              unfold frames2rootpairs in H10. simpl in H10.
              red in H10. simpl in H10. inversion H10; subst; auto.
          +  red in H11|-*. subst roots3'. rewrite roots_eq in H11.
            intros p A. eapply H11. simpl. destruct v0; simpl;  eauto. 
          + red. red in H16. subst roots3'. rewrite roots_eq in H16.
            simpl in H16. destruct v0; eauto. simpl in H16. inversion H16; eauto. 
         - eapply gc_sound; eauto. apply GCP.
         - apply graph_unmarked_copy_compatible; apply H7.
      }

       split3. 
       - destruct H3. destruct H10.  unfold rootpairs_compatible in H10. simpl in H10. 
         rewrite roots_eq in H10. simpl in H10. injection H10. intros. subst. destruct v0; reflexivity. 
       - eapply meta.gc_preserved; try eapply ISO; try eauto.
        5 : { assert (root_t_of_rep_type v0 :: roots = map roots_rep_type (v0 ::map rep_type_of_root_t (roots))).
        simpl. f_equal. rewrite map_map. rewrite MCList.map_id_f; try eauto. intros x; destruct x; eauto. destruct s; eauto. 
      rewrite <- H10. 
      enough (roots3 = map (root_map vmap12) (root_t_of_rep_type v0 :: roots)) as <- by eauto. 
        now rewrite roots_eq. }
        + apply GCP. 
        + eapply GCP3. 
        + apply GCP. 
        + eapply (@in_graph_reachable T0 ); eauto. 
          eapply meta.has_v; eauto. 
          eapply GCP. now left.
        - split; eauto. rewrite roots_eq. f_equal. 
       destruct v0; reflexivity. } 

   destruct H10 as [v0' [roots3' [ ? [? [ ? GCP3]] ] ] ].
   subst v0x roots3.
  limited_change_compspecs filteredCompSpecs.
   forward. entailer!!. rewrite Znth_0_cons. {
        destruct v0'; simpl; auto. destruct g0; simpl; auto.
        apply has_v in H11. destruct H11 as [? _].
        pose proof (graph_has_gen_start_isptr _ _ H10).
        unfold vertex_address.
        destruct (gen_start g3 (vgeneration _)); auto.
    }
   forward.
   forward.

   Exists g3 v0' roots3' t_info4.
   rewrite Znth_0_cons.
    unfold full_gc.
    entailer!!.
    --  repeat simple apply conj; auto.
      ++ simpl ti_heap.

        clear - Hn ROOM. simpl in ROOM.
         rewrite Ptrofs.unsigned_repr in ROOM by rep_lia.
         unfold headroom. simpl.  lia.
      ++ apply gc_graph_iso_cons_roots_inv in ISO; auto.
    -- unfold before_gc_thread_info_rep, frame_rep_.
      limited_change_compspecs filteredCompSpecs.
      unfold ti_fp.
      unfold t_info4; simpl.
      replace (Vlong (Ptrofs.to_int64 (ti_nalloc t_info3))) with (Vptrofs (ti_nalloc t_info3))
        by (rewrite Vptrofs_unfold_true by reflexivity; reflexivity).
      cancel.
      generalize (frame_rep_unfold sh v___FRAME__ v___ROOT__ (frames_p r2) 1 [rep_type_val g3 v0']);
      limited_change_compspecs filteredCompSpecs;
        intro Hx; apply Hx; clear Hx; auto.
      compute; clear; congruence.
  + forward.
    apply headroom_check in H3; [ | rep_lia].
    Exists g v0 roots t_info.
    unfold full_gc, before_gc_thread_info_rep.
    rewrite <- STARTeq.
      limited_change_compspecs filteredCompSpecs.
    entailer!!.
    split.
    apply gc_graph_iso_refl.
    apply frame_shells_eq_refl.
Qed.

Ltac apply_semax_GC_SAVE1 :=
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ (normal_ret_assert ?Post) =>
  let Q1 := get_rep_temps _tinfo _nalloc Q in
  let Q2 := get_nonrep_temps _tinfo _nalloc Q in
  let R1 := get_gc_mpreds R in
  let R2 := get_nongc_mpreds R in
 eapply (semax_frame_PQR'' Q1 Q2 R1 R2);
  [solve [auto 50 with closed]
  | solve [go_lowerx; autorewrite with norm; cancel]
  | apply perhaps_gc_1_live_root_aux
  | eapply semax_GC_SAVE1; eauto ]
 end.

Import Maps.

Lemma prove_ptree_sub:
 forall {A} (m1 m2 : PTree.t A),
  PTree.fold (fun p i t => PTree.get i m2 = Some t /\ p) m1 True ->
  forall i, sub_option (PTree.get i m1) (PTree.get i m2).
Proof.
intros; hnf; intros.
rewrite PTree.fold_spec in H.
destruct (PTree.get i m1) eqn:?H; auto.
 apply PTree.elements_correct in H0.
 rewrite <- fold_left_rev_right in H.
 rewrite in_rev in H0.
 induction (rev (PTree.elements m1)).
 inversion H0.
 destruct H0.
 + subst a0. destruct H. auto.
 + destruct H as [_ ?]. apply IHl in H; auto.
Qed.

Lemma prove_cssub:
  forall CS1 CS2: compspecs,
  PTree.fold (fun p i t => PTree.get i (@cenv_cs CS2) = Some t /\ p) (@cenv_cs CS1) True ->
  PTree.fold (fun p i t => PTree.get i (@ha_env_cs CS2) = Some t /\ p) (@ha_env_cs CS1) True ->
  PTree.fold (fun p i t => PTree.get i (@la_env_cs CS2) = Some t /\ p) (@la_env_cs CS1) True ->
  cspecs_sub CS1 CS2.
Proof.
intros.
split3; red; apply prove_ptree_sub; auto.
Qed.

Lemma prove_tycontext_sub:
 forall D1 D2 : tycontext,
  (PTree.fold (fun p i t => PTree.get i (temp_types D2) = Some t /\ p) (temp_types D1) True) ->
  (PTree.fold (fun p i t => PTree.get i (var_types D2) = Some t /\ p) (var_types D1) True) ->
  (PTree.fold (fun p i t => PTree.get i (var_types D1) = Some t /\ p) (var_types D2) True) ->
  ret_type D1 = ret_type D2 ->
  (PTree.fold (fun p i t => PTree.get i (glob_types D2) = Some t /\ p) (glob_types D1) True) ->
  (PTree.fold (fun p i t => PTree.get i (glob_specs D2) = Some t /\ p) (glob_specs D1) True) ->
  annotations D1 = annotations D2 ->
  tycontext_sub D1 D2.
Proof.
intros ? ? Ht Hv Hv' Hr Hg Hs Ha.
split3; [ | | split3; [ | | split ] ].
- (* temps *)
 clear Hv Hv' Hr Hg Hs Ha.
 intro i; apply prove_ptree_sub with (i:=i) in Ht.
 red in Ht. destruct ((temp_types D1) ! i); auto. rewrite Ht; auto.
- (* vars *)
 intros.
 clear Ht Hr Hg Hs Ha.
 apply prove_ptree_sub with (i:=id) in Hv.
 apply prove_ptree_sub with (i:=id) in Hv'.
 red in Hv, Hv'. destruct ((var_types D1) ! id), ((var_types D2) ! id); auto.
- auto.
- clear Ht Hv Hv' Hr Hs Ha.
 intros.
 apply prove_ptree_sub; auto.
- clear Ht Hv Hv' Hr Hg Ha.
 intros.
 apply prove_ptree_sub with (i:=id) in Hs.
 red in Hs. destruct ((glob_specs D1) ! id); auto.  rewrite Hs.
 apply subsumespec_refl.
- clear Ht Hv Hv' Hr Hg Hs.
 intros. rewrite Ha. apply Annotation_sub_refl.
Qed.


Lemma semax_cssub:
(* A version of this is proved for the shallow-embedded semax, and it
  should be not severely difficult to prove for the deep-embedded one;
  but it might need to be by induction over the syntax... *)
  forall {CS CS' : compspecs},
  cspecs_sub CS CS' ->
  forall (Espec : OracleKind) (Delta : tycontext)
    (P : assert) (c : statement) (R : ret_assert),
  @semax CS Espec Delta P c R ->
  @semax CS' Espec Delta P c R.
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
            List_ext.filter_option (map (fun x => match (snd x) with | repNode v_x => Some ((v, (fst x)), (v, v_x) )
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
      apply List_ext.filter_option_In_iff in H0.
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
  apply List_ext.filter_option_In_iff in H_In.
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
  destruct H1 as (gcc & sup & safetocopy & soundgcgraph & copycompatible).
 red in gcc. destruct gcc as (unmarked & nobackward & nodangling & tisizespec).

(*

unmarked & (nobackward & (nodanging & (tisizespec & (safetocopy & (graphticompatible & (outliercompatible & (rootscompatible & (soundgcgraph & (rp_compatible & copycompatible)))))))))).
*)
    assert (edge_compatible g 0 (raw_fields (newRaw v (Z.of_nat t) (map rep_field ps) R1 R2 R3)) es).
    { unfold edge_compatible. intros. simpl. clear.  unfold es. generalize (0)%nat at 2 4.  induction ps; intros n; simpl; eauto.
    - reflexivity.
    - destruct a; simpl.
      + rewrite Nat.add_1_r.  apply IHps.
      + rewrite Nat.add_1_r.  apply IHps.
      + rewrite Nat.add_1_r. intuition eauto. right.  apply IHps; eauto.
        rewrite IHps. eauto. }

  split3; [ | | split3];  eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_heap_compatible, add_node_ti_size_spec, add_node_roots_compatible.
  split; [ | split3];  eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_heap_compatible, add_node_ti_size_spec, add_node_roots_compatible.

  + eapply add_node_ti_size_spec; eauto.  rewrite spaces_size.   rep_lia.
  + split; [ | split3];  eauto using add_node_no_backward_edge, add_node_outlier_compatible, add_node_roots_graph_compatible, sound_gc_graph, add_node_safe_to_copy0, add_node_no_dangling_dst, add_node_graph_unmarked, add_node_graph_heap_compatible, add_node_ti_size_spec, add_node_roots_compatible.
    * apply add_node_graph_heap_compatible; eauto; try apply sup.
      unfold raw_fields. simpl. lia.
    * apply add_node_rootpairs_compatible; auto; try apply sup.
    * apply add_node_roots_compatible; auto; try apply sup.
    *  apply add_node_outlier_compatible; eauto; try apply sup.
    simpl.
    unfold incl. intros. apply List_ext.filter_sum_right_In_iff in H3.
    apply List_ext.filter_option_In_iff in H3. apply in_map_iff in H3.
    destruct H3 as (p & A1 & A2). destruct p; simpl in *; try congruence.
    rewrite Forall_forall in H0. injection A1. intros. subst.  exact (H0 _ A2).
   + apply add_node_copy_compatible; try apply sup; eauto.
Qed.

(** If outliers/roots are compatible, the roots never contain the next new node.  *)
Lemma new_node_roots g outlier roots:
  roots_compatible g outlier roots -> ~ In (inr (new_copied_v g 0)) roots.
Proof.
  intros (RC1&RC2) A.
  rewrite List_ext.filter_sum_right_In_iff in A.
  apply (computable_theorems.Forall_forall1 _ _ RC2) in A. -
  apply graph_has_v_not_eq with (to := 0%nat) in A. congruence.
Qed.
