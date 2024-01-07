(** * General Specification of alloc functions

Kathrin Stark, 2021.

This file contains a general specification for the alloc function,
using a representation of constructors.
*)
Require Import Coq.Lists.List.
Import ListNotations.

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
         (g : graph) (c : reified ann) (xs : args c) (ps : list rep_type) : Prop :=
  match c as l return (args l -> Prop) with
  | TYPEPARAM f =>
      fun H => let (X_, xs') := H in
               let (R_, xs') := xs' in
        in_graphs ing g (f X_ R_) xs' ps
  | ARG X_ R_ f =>
      fun H  => let (x, xs') := H in
      match ps with
      | [] => False
      | p :: ps' => @is_in_graph X_ (ing X_ R_) g x p /\ @in_graphs _ ing g (f x) xs' ps'
      end
  | RES x _ => fun _ => ps = nil
  end xs.

Definition ctor_in_graphs := in_graphs (@field_in_graph).
Definition prim_in_graphs := in_graphs (@prim_in_graph).

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

Lemma ctor_in_graphs_size (g : graph) (c : reified ctor_ann) (xs : args c) (ps : list rep_type) :
  ctor_in_graphs g c xs ps -> get_size c xs = length ps.
Proof.
   unfold ctor_in_graphs.
  revert ps.
  induction c; simpl in *; intros; try (destruct xs); try (destruct s); eauto.
  all: destruct ps; simpl; intuition eauto; try congruence.
Qed.

(** Custom notation with a list for PRE to make the specification better readable. *)
Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [[ xs ]] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (xs, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100) : funspec_scope.


Definition get_c_typesig
           (c : reified prim_ann)
           (arity : nat) : compcert_rmaps.typesig :=
  (cons thread_info (repeat int_or_ptr_type arity), int_or_ptr_type).

Definition fn_desc_to_funspec_aux
           (c : reified prim_ann)
           (model_fn : meta.reflect c)
           (arity : nat) : funspec :=
  WITH gv : globals, g : graph, roots : GCGraph.roots_t, sh : share,
       xs : args c, ps : list rep_type, ti : val,
       outlier : GCGraph.outlier_t, t_info : GCGraph.thread_info
   PRE [[ cons thread_info (repeat int_or_ptr_type arity) ]]
       PROP (writable_share sh ;
              prim_in_graphs g c xs ps)
       (PARAMSx (ti :: map (rep_type_val g) ps)
        (GLOBALSx [gv]
         (SEPx (full_gc g t_info roots outlier ti sh gv :: nil))))
   POST [ int_or_ptr_type ]
       EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info),
          PROP (let r := result c xs in
                @is_in_graph (projT1 r) (@prim_in_graph (projT1 r) (projT2 r)) g'
                  (model_fn xs) p' ;
                gc_graph_iso g roots g' roots)
          RETURN  (rep_type_val g' p')
          SEP (full_gc g' t_info' roots outlier ti sh gv).

Definition fn_desc_to_funspec (d : fn_desc) : ident * funspec :=
  (ident_of_string (c_name d),
   fn_desc_to_funspec_aux (type_desc d) (model_fn d) (f_arity d)).


Definition headroom (ti: GCGraph.thread_info) : Z :=
   let g0 := heap_head (ti_heap ti) in
      total_space g0 - used_space g0.

(*
Definition alloc_make_nat_S : funspec :=
  WITH gv : globals, g : graph, p : rep_type,
       x: nat, roots : roots_t, sh : share,
       ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
  PRE  [[ [thread_info ; tulong] ]]
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
    PRE  [[ thread_info :: repeat int_or_ptr_type n ]]
       PROP (n = get_size (ctor_reified c) xs ;
             ctor_in_graphs g _ xs ps ;
             (Z.of_nat n) < headroom t_info ;
             writable_share sh)
       (PARAMSx (ti :: map (fun p => rep_type_val g p) ps)
       (GLOBALSx [gv]
       (SEPx (full_gc g t_info roots outlier ti sh gv :: nil))))
    POST [ int_or_ptr_type ]
      EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info),
        PROP (let r := result (ctor_reified c) xs in
              @is_in_graph (projT1 r) (@field_in_graph (projT1 r) (projT2 r)) g' (ctor_reflected c xs) p' ;
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
unfold ctor_in_graphs, prim_in_graphs in *;
lazymatch goal with
| xs: args _, H0: in_graphs _ _ _ ?xs' ?ps  |- _ =>
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
   |  H: in_graphs _ _ _ _ (_ :: _) |- _ => destruct H
   |  H: in_graphs _ _ _ _ ps |- _ => hnf in H; subst ps
   end
   | _ => idtac
end;
 change (in_graphs (@field_in_graph)) with ctor_in_graphs in *;
 change (in_graphs (@prim_in_graph)) with prim_in_graphs in *.

Ltac start_function' := 
  start_function1; 
  repeat (simple apply intro_prop_through_close_precondition; intro);
  concretize_PARAMS;
  start_function2;
  start_function3.


Lemma is_pointer_or_integer_rep_type_val:
  forall {A} `{InG: InGraph A} g (n: A) p, 
   is_in_graph g n p ->
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
  Int.min_signed <= n <= Int.max_signed ->
  typed_false tint
       match
         sem_unary_operation Onotbool tint
           (force_val
              (both_long
                 (fun n1 n2 : int64 => Some (bool2val (negb (Int64.lt n2 n1))))
                 (sem_cast_i2l Signed) sem_cast_pointer 
                 (Vint (Int.repr n))
                 (force_val
                    (sem_sub_pp
                       int_or_ptr_type
                       (Vptr startb
                          (Ptrofs.add starti
                             (Ptrofs.repr
                                (WORD_SIZE
                                   * total_space hh))))
                       (Vptr startb
                          (Ptrofs.add starti
                             (Ptrofs.repr
                                (WORD_SIZE
                                   * used_space hh))))))))
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
     rewrite Int.signed_repr in H8 by auto.
    destruct (Int64.lt _ _) eqn:?H in H8; try discriminate.
    unfold Int64.lt in H.
    if_tac in H; try discriminate. clear H H8.
    rewrite !(Ptrofs.add_commut starti), Ptrofs.sub_shifted, ptrofs_sub_repr in H0.
    unfold MAX_SPACE_SIZE in *. simpl in UB.
    rewrite <- Z.mul_sub_distr_l in H0.
    change WORD_SIZE with 8 in *.
    rewrite ptrofs_divs_repr in H0 by rep_lia.
    rewrite ptrofs_to_int64_repr in H0 by reflexivity.
    rewrite Z.mul_comm, Z.quot_mul in H0 by lia.
    rewrite !Int64.signed_repr in H0 by rep_lia. auto.
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


Definition GC_SAVE1 n := 
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
                                 (Ebinop Ole (Econst_int (Int.repr n) tint)
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
                        (Econst_int (Int.repr n) tint))
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


Ltac get_rep_temps ti Q :=
 lazymatch Q with
 | nil => constr:(Q)
 | temp ti ?v :: ?r => let r' := get_rep_temps ti r in constr:(temp ti v :: r')
 | temp ?i (rep_type_val ?g ?v) :: ?r => 
    let r' := get_rep_temps ti r in constr:(temp i (rep_type_val g v) :: r')
 | temp ?i ?v :: ?r => get_rep_temps ti r
 | ?t :: ?r => let r' := get_rep_temps ti r in constr:(t::r')
 end.

Ltac get_nonrep_temps ti Q :=
 lazymatch Q with
 | nil => constr:(Q)
 | temp ti _ :: ?r => get_nonrep_temps ti r 
 | temp ?i (rep_type_val ?g ?v) :: ?r => get_nonrep_temps ti r
 | temp ?i ?x :: ?r => let r' := get_nonrep_temps ti r in constr:(temp i x ::r')
 | _ :: ?r => get_nonrep_temps ti r
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


