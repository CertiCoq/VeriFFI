(** * Summary of Subsumption
 *)

(* From VC Require Export graphCRep. *)
(* From VC Require Export graph_add. *)
(* From VC Require Export glue. *)
Require Import VST.floyd.proofauto.
Require Import VeriFFI.examples.uint63nat.glue.
Require Import VeriFFI.library.meta.
Require Import CertiGraph.CertiGC.GCGraph.


Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
Definition Gprog := ltac:(with_library prog (@nil (ident * funspec))).


(** Custom types *)
Definition thread_info_type := Tstruct _thread_info noattr.
Definition thread_info := tptr thread_info_type.

Set Nested Proofs Allowed.

Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons : A -> forall n, vector A n -> vector A (S n).

Fixpoint to_list {A : Type} {n : nat} (v : vector A n) :=
  match v with
    | vnil => nil
    | vcons x _ xs => cons x (to_list xs)
end.

Ltac updater := repeat (try rewrite !upd_Znth0; try (rewrite upd_Znth_cons; [|rep_lia]); simpl).

Ltac inv x := dependent inversion x; subst; clear x.

Ltac vector_inv :=
  repeat (match goal with H: vector _ _ |- _ => inv H end).


(** *** Step 1 : A general definition of the Clight representation of the glue function.
This representation will be parametric in:
- identifiers _argv, _alloc, etc.
- a tag z : Z
- a list of identifiers, args.
The length of the list corresponds to the number of arguments, e.g. 1 for nat/S.

General representation of a C function, e.g. for nat/S:

unsigned long long * alloc_make_Coq_Init_Datatypes_nat_S(struct thread_info *tinfo, unsigned long long arg0)
{
  unsigned long long *argv;
  argv = ( *tinfo).alloc;
  if (tinfo->limit - tinfo->alloc < 3) exit(1);
  * ((unsigned long long * ) argv + 0) = 1024;
  * ((unsigned long long * ) argv + 1) = arg0;
  ( * tinfo).alloc = ( *tinfo).alloc + 2;
  return argv + 1;
}

 *)

(** C code that assigns the argument _arg into the array _argv with corresponding offset,
e.g. for nat/S:

  * ((unsigned long long * ) argv + 1) = arg0;

 *)
Definition f_alloc_assign (_argv : ident) (offset : Z) (_arg: ident) :=
(Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
              (Econst_int (Int.repr offset) tint) (tptr tulong)) tulong)
          (Etempvar _arg tulong)).

(** C code for the changing of alloc/returning,
e.g. for nat/S:

  ( * tinfo).alloc = ( *tinfo).alloc + 2;
  return argv + 1;
*)
Definition f_alloc_standard (n: Z) :=  (Ssequence
            (Ssequence
              (Sset _t'1
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _alloc (tptr tulong))
                (Ebinop Oadd (Etempvar _t'1 (tptr tulong))
                  (Econst_int (Int.repr n) tint) (tptr tulong))))
            (Sreturn (Some (Ebinop Oadd (Etempvar _argv (tptr tulong))
                             (Econst_int (Int.repr 1) tint) (tptr tulong))))).

(** C code for all assignments of previous arguments,
    e.g. for nat/S:

  * ((unsigned long long * ) argv + 1) = arg0;
  ( * tinfo).alloc = ( *tinfo).alloc + 2;
  return argv + 1;
*)
Fixpoint f_alloc_assigns (_argv : ident) (z : Z) (args : list ident) :=
  match args with
  | nil => f_alloc_standard z
  | arg :: args' => Ssequence (f_alloc_assign _argv z arg) (f_alloc_assigns _argv (1 + z) args')
end.

(** C code for the whole function *)
Definition f_alloc_make_general (_argv : ident) (args: list ident) (tag : Z) := {|
  fn_return := (tptr tulong);
  fn_callconv := cc_default;
  fn_params := ((_tinfo, (tptr (Tstruct _thread_info noattr))) ::
                map (fun x => (x, tulong)) args );
  fn_vars := nil;
  fn_temps := ((_argv, (tptr tulong)) :: (_t'3, (tptr tulong)) ::
               (_t'2, (tptr tulong)) :: (_t'1, (tptr tulong)) :: nil);
  fn_body :=
(Ssequence
  (Sset _argv
    (Efield
      (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _limit (tptr tulong)))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _alloc (tptr tulong)))
        (Sifthenelse (Ebinop Olt
                       (Ebinop Osub (Etempvar _t'2 (tptr tulong))
                         (Etempvar _t'3 (tptr tulong)) tlong)
                       (Econst_int (Int.repr (2 + Zlength args)) tint) tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _argv (tptr tulong)) (tptr tulong))
            (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong)
        (Econst_int (Int.repr tag) tint))
        (f_alloc_assigns _argv 1 args))))
|}.

(** This one is definitionally equal to the original code: *)

Lemma f_alloc_cons_eq1: f_alloc_make_general _argv [_arg0; _arg1] 2048 = f_alloc_make_Coq_Init_Datatypes_list_cons.
Proof. autounfold. reflexivity. Qed.

Goal f_alloc_make_general _argv [_arg0] 1024 = f_alloc_make_Coq_Init_Datatypes_nat_S.
Proof. autounfold. reflexivity. Qed.


(** Step 2: Define a general function specification which ignores graphs and propositinal predicates relating to this. *)

(** E.g., for zero arguments this one would look like this, being parametric only in the tag: *)
Definition zero_arguments (t : Z) : funspec :=
  WITH u : unit
  PRE  [ ]
       PROP ()
       PARAMS ()
       GLOBALS ()
       SEP ()
  POST [ tulong ]
     PROP ()
     LOCAL (temp ret_temp (Z2val t))
     SEP ().

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

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [[ xs ]] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (xs, tz) cc_default (t1*t2*t3*t4*t5*t6*t7)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

(* TODO: Do we want a condition on alloc and limit? - I don't think so. *)
Definition  n_arguments (tag : Z) (n : nat) : funspec :=
        WITH sh_tinfo : share, sh_heap: share,  ti : val, ps : vector val n, b : block, alloc: Z, limit: Z
  PRE  [[ thread_info :: repeat tulong n ]]
       PROP ( writable_share sh_tinfo; writable_share sh_heap; Int.min_signed <= tag <= Int.max_signed)
       (PARAMSx (ti :: to_list ps)
       (GLOBALSx nil
       (SEPx (field_at sh_tinfo thread_info_type [StructField _alloc] (Vptr b (Ptrofs.repr alloc)) ti
                       :: field_at sh_tinfo thread_info_type [StructField _limit] (Vptr b (Ptrofs.repr limit)) ti
                       :: data_at_ sh_heap (tarray tulong (1 + (Z.of_nat n))) (Vptr b (Ptrofs.repr alloc))
                       :: nil))))
  POST [ tptr tulong  ]
     PROP ()
     RETURN  (Vptr b (Ptrofs.repr (alloc + 8)))
     SEP (field_at sh_tinfo thread_info_type [StructField _alloc] (offset_val (Z.of_nat (S n) * sizeof tulong) (Vptr b (Ptrofs.repr alloc))) ti;
         field_at sh_tinfo thread_info_type [StructField _limit] (Vptr b (Ptrofs.repr limit)) ti;
         data_at sh_heap (tarray tulong (1 + (Z.of_nat n))) (Vlong (Int64.repr tag) :: to_list ps) (Vptr b (Ptrofs.repr alloc))
         ).


(** Step 3: Prove this general function specification correct.
This should be parametric in the function name, the arguments and the tag.
 *)

Fixpoint make_args (n : nat) : list ident :=
  match n with
 | O => []
 | S n => make_args n ++ [Pos.of_nat (S n)]
end.

Ltac simplify_func_tycontext_ks' DD :=
  match DD with context [(func_tycontext ?f ?V ?G ?A)] =>
    let D1 := fresh "D1" in let Delta := fresh "Delta" in
    pose (Delta := @abbreviate tycontext (func_tycontext f V G A));
    change (func_tycontext f V G A) with Delta;
    unfold func_tycontext, make_tycontext in Delta;
    let DS := fresh "Delta_specs" in let DS1 := fresh "DS1" in
    pose (DS1 := make_tycontext_s G);
    pose (DS := @abbreviate (PTree.t funspec) DS1);
    change (make_tycontext_s G) with DS in Delta;
    hnf in DS1;
    cbv beta iota delta [ptree_set] in DS1;
    subst DS1;
    cbv beta iota zeta delta - [abbreviate DS] in Delta
   end.

Ltac simplify_func_tycontext_ks :=
match goal with
 | |- semax ?DD _ _ _ => simplify_func_tycontext_ks'  DD
 | |- ENTAIL ?DD, _ |-- _ => simplify_func_tycontext_ks'  DD
end.

Hint Unfold f_alloc_assign.

Ltac alloc_start_function :=
    start_function1;
    vector_inv;
    first [ erewrite compute_close_precondition_eq; [ | reflexivity | reflexivity] | rewrite close_precondition_main ];
    start_function2.

Ltac custom_tactics :=
  first [forward_if True | forward_call (1) | now (simpl; entailer!; try normalize) | entailer! ].

Ltac repeat_forward tac :=
  repeat (try (unfold f_alloc_assign, f_alloc_standard); first [forward | tac]).

Lemma alloc_make_nat_general_proof1 _alloc_f (t: Z) : semax_body Vprog Gprog (f_alloc_make_general _argv (make_args 1) t) (_alloc_f, n_arguments t 1).
Proof.
  alloc_start_function.
  repeat_forward custom_tactics.
Qed.

Lemma alloc_make_nat_general_proof2  _alloc_f (t: Z) : semax_body Vprog Gprog (f_alloc_make_general _argv (make_args 2) t) (_alloc_f, n_arguments t 2).
Proof.
  alloc_start_function.
  repeat_forward custom_tactics.
Qed.

(*
Lemma alloc_make_nat_general_proof3 _alloc_f (t: Z) : semax_body Vprog Gprog (f_alloc_make_general _argv (make_args 3) t) (_alloc_f, n_arguments t 3).
Proof.
  alloc_start_function.
   repeat_forward custom_tactics.
Qed.

Lemma alloc_make_nat_general_proof4 _alloc_f (t: Z) : semax_body Vprog Gprog (f_alloc_make_general _argv (make_args 4) t) (_alloc_f, n_arguments t 4).
Proof.
  alloc_start_function.
  repeat_forward custom_tactics.
Qed.


Lemma alloc_make_nat_general_proof5 _alloc_f (t: Z) : semax_body Vprog Gprog (f_alloc_make_general _argv (make_args 5) t) (_alloc_f, n_arguments t 5).
Proof.
  alloc_start_function.
  repeat_forward custom_tactics.
Qed. *)


(** Step 4: Show that the specification we actually want is subsumed.  *)

(** In the trivial case of zero arguments, this is easy: *)

Fixpoint rep_type_val (g : graph) (x : rep_type) : val :=
match x with
| repZ y => odd_Z2val y
| repOut p => GC_Pointer2val p
| repNode v => vertex_address g v
end.

Definition make_nat_0_spec : ident * funspec :=
 DECLARE _make_Coq_Init_Datatypes_nat_O
  WITH gv : globals, g : graph
  PRE  [ ]
       PROP ()
       PARAMS ()
       GLOBALS ()
       SEP (graph_rep g)
  POST [ tulong ]
     EX (x : rep_type),
     PROP (nat_in_graph g O x)
     LOCAL (temp ret_temp (rep_type_val g x))
     SEP (graph_rep g).

Definition test_subsumption :
  funspec_sub (zero_arguments 1) (snd make_nat_0_spec).
Proof.
  unfold  make_nat_0_spec, zero_arguments. simpl.
  repeat split; eauto.
  intros. Intros. destruct x2 as (gv&g).
  Exists (@nil Type). Exists tt. Exists (graph_rep g).
  entailer. hint.
  entailer!.
  - normalize. intros.  Exists (repZ 0).
    simpl. unfold odd_Z2val. simpl.
    unfold Z2val.  admit.
  - simpl. entailer!.
    normalize.
Admitted.


Lemma isptr_Vptr p :
  isptr p -> exists b x, p = Vptr b x.
Proof.
  destruct p; simpl; try contradiction; eauto.
Qed.

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


From VC Require Import specs_general proofs_library_general.

Lemma add_node_monotone_list  (X_rep : representable_X) g to lb e n p:
 add_node_compatible g (new_copied_v g to) e -> graph_has_gen g to -> list_in_graph (X_in_graph X_rep) g n p -> list_in_graph (X_in_graph X_rep) (add_node g to lb e) n p.
Proof.
  intros C G. revert p. induction n; eauto. (* Number of cases depends. *)
  - intros p (p1&p2&H1&H2&H3). (* TODO: MORE TO SEPARATE, exists. *)
    exists p1. exists p2.
    repeat split; eauto using X_monotone, graph_cRep_add_node.
Qed.

Lemma list_in_graph_cons:
  forall (g : graph) (p_x : rep_type) (X : representable_X) (x : X_type X) (p_xs : rep_type) (xs : list (X_type X)),
    graph_has_gen g 0 ->
    forall (R1 : 0 <= 0 < 256)
      (R2 : 0 < Zlength [rep_field p_x; rep_field p_xs] < two_power_nat 22)
      (R3 : NO_SCAN_TAG <= 0 -> ~ In None [rep_field p_x; rep_field p_xs]),
      X_in_graph X g x p_x ->
      list_in_graph (X_in_graph X) g xs p_xs ->
      add_node_compatible g (new_copied_v g 0) (get_fields g 0 [p_x; p_xs] 0) ->
      list_in_graph (X_in_graph X)
                    (add_node g 0 (newRaw (new_copied_v g 0) 0 [rep_field p_x; rep_field p_xs] R1 R2 R3)
                              (get_fields g 0 [p_x; p_xs] 0)) (x :: xs) (repNode (new_copied_v g 0)).
Proof.
  intros g p_x X x p_xs xs graph_has_gen_0 R1 R2 R3.
  exists p_x, p_xs. (* CHANGED *) intuition (try congruence).
  * destruct X. simpl in *. apply X_monotone; eauto.  (* TODO: REQUIRE MONOTONICITY RESULT IN THE ASSUMPTIONS *)
  * eauto using add_node_monotone_list.  (* CHANGED: One for each. Generate respective hints. *)
  * unfold graph_cRep, tag_list. (* CHANGED to tag_list *) intuition eauto.
    -- split.
       ++ rewrite add_node_graph_has_gen; eauto.
       ++ apply add_node_has_index_new; eauto.
    -- rewrite add_node_vlabel.
       simpl. intuition eauto. repeat constructor.
       ++ (* CHANGED: Now two things *) (* subst es. *)
         destruct p_xs as [| |v_xs]; try reflexivity. simpl.
         destruct p_x as [| |v_x]; try reflexivity. (* TODO: CHANGED *)
         ** simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (new_copied_v g 0, 1%nat)); congruence.
         ** simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (new_copied_v g 0, 1%nat)); congruence.
         ** simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (new_copied_v g 0, 1%nat)); congruence.
       ++ (* CHANGED: Now two things *)
         destruct p_x as [| |v_x]; try reflexivity.
         destruct p_xs as [| |v_xs]; try reflexivity.
         ** simpl. unfold updateEdgeFunc. destruct EquivDec.equiv_dec; try congruence.
         ** simpl. unfold updateEdgeFunc. destruct EquivDec.equiv_dec; congruence.
         ** simpl. unfold updateEdgeFunc. destruct EquivDec.equiv_dec; try congruence.
            destruct EquivDec.equiv_dec; congruence.
 Qed.

Definition X_in_graph_cons (descr : specs_general.constructor_description) (t: nat) :=
  forall (gr : graph) (ps : list rep_type) (args_my : specs_general.args (constr descr)),
    graph_has_gen gr 0 ->
    forall (R1 : 0 <= Z.of_nat t < 256)
      (R2 : 0 < Zlength (map rep_field ps) < two_power_pos 54)
      (R3 : NO_SCAN_TAG <= Z.of_nat t -> ~ In None (map rep_field ps)),
      in_graphs gr (constr descr) args_my ps ->
      add_node_compatible gr (new_copied_v gr 0) (get_fields gr 0 ps 0) ->
      specs_general.X_in_graph (getRes (constr descr) args_my)
                               (add_node gr 0
                                         (newRaw (new_copied_v gr 0) (Z.of_nat t) (map rep_field ps) R1 R2 R3)
                                         (get_fields gr 0 ps 0)) (coqConstr descr args_my)
                               (repNode (new_copied_v gr 0)).

Lemma X_list_in_graph_cons:  X_in_graph_cons consDescr 0.
Proof.
  unfold X_in_graph_cons.
  intros g ps args_my graph_has_gen_0 R1 R2 R3 H. simpl in *.
  destruct args_my. destruct p.  destruct p. simpl in *. Search compatible.
  destruct ps; try inv H. destruct ps; try inv H1.
  exists r, r0. simpl in *. (* CHANGED *) intuition (try congruence).
  * destruct x. apply X_monotone; eauto.
  * eapply add_node_monotone_list; eauto.
  * split.
           ++ rewrite add_node_graph_has_gen; eauto.
       ++ apply add_node_has_index_new; eauto.
  * unfold update_vlabel. if_tac; try congruence.
    simpl. intuition eauto.
    repeat constructor.
    ++ destruct r0 as [| |v_xs]; try reflexivity. simpl.
       destruct r as [| |v_x]; try reflexivity. (* TODO: CHANGED *)
       ** simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (new_copied_v g 0, 1%nat)); congruence.
       ** simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (new_copied_v g 0, 1%nat)); congruence.
       ** simpl. unfold updateEdgeFunc. destruct (EquivDec.equiv_dec (new_copied_v g 0, 1%nat)); congruence.
    ++  (* CHANGED: Now two things *)
      destruct r as [| |v_x]; try reflexivity.
      destruct r0 as [| |v_xs]; try reflexivity.
      ** simpl. unfold updateEdgeFunc. destruct EquivDec.equiv_dec; try congruence.
      ** simpl. unfold updateEdgeFunc. destruct EquivDec.equiv_dec; congruence.
      ** simpl. unfold updateEdgeFunc. destruct EquivDec.equiv_dec; try congruence.
         destruct EquivDec.equiv_dec; congruence.
Qed.

Goal  forall  (g : graph) (descr : specs_general.constructor_description) (t: nat) (ps : list rep_type) (args_my : specs_general.args (constr descr)) ,
    graph_has_gen g 0 ->
    forall (R1 : 0 <= Z.of_nat t < 256)
      (R2 : 0 < Zlength (map rep_field ps) < two_power_pos 54)
      (R3 : NO_SCAN_TAG <= Z.of_nat t -> ~ In None (map rep_field ps)),
  compatible
          (add_node g 0 (newRaw (new_copied_v g 0) (Z.of_nat t) (map rep_field ps) R1 R2 R3)
             (get_fields g 0 ps 0)) (new_copied_v g 0) 0 (map rep_field ps) ps.
Proof.
  intros. generalize O at 4 6. revert g H.
  intros. Check nth. Print rep_type.
  assert (forall m, (m < n)%nat -> (match (nth m ps (repZ 0)) with
                      | (repNode v_x) => In (new_copied_v g 0, m, (new_copied_v g 0, v_x))  (get_fields g 0 ps n)
                      | _ => True end)).
  { induction ps.  simpl. admit. admit. }
  revert H0. generalize (get_fields g 0 ps n).
  intros.
  generalize ps at 2 3 as ps'. intros.  revert ps' n g H0 H.
  induction ps'; intros.
  - simpl. constructor.
  - change (map rep_field (a :: ps')) with (rep_field a :: map rep_field ps'). constructor.
    + eapply IHps'; eauto.  (*
    + destruct a; try reflexivity.

      simpl. Search dst. erewrite add_node_dst_new; try eauto.
      2: { left. reflexivity. }
      simpl. admit. (* some NoDup story *)


eapply IHps'.

    + eapply IHps'.

 admit. (* apply IHps. simpl. Print compatible.
      Print get_fields.
      Search compatible add_node.
(* TODO: IHps *) admit. *)
    + destruct a; try reflexivity.

      simpl. Search dst. erewrite add_node_dst_new; try eauto.
      2: { left. reflexivity. }
      simpl. admit. (* some NoDup story *)


 autorewrite with graph_add. unfold pregraph_add_v. simpl.
      * reflexivity.
      * simpl.

eapply IHps.

 destruct a.
    + simpl.


repeat constructor; eauto.
    + admit.
    + destruct a; simpl; try reflexivity.
      simpl. simpl.  admit.
*)
Admitted.


Definition calc t n := Z.of_nat t + Z.shiftl (Z.of_nat n) 10.

Lemma in_graphs_has:
  forall (descr : specs_general.constructor_description) (gr : graph)
    (ps : list rep_type) (args_my : specs_general.args (constr descr)),
    in_graphs gr (constr descr) args_my ps ->
    Forall
      (fun p : rep_type =>
         match p with
         | repNode v' => graph_has_v gr v' /\ new_copied_v gr 0 <> v'
         | _ => True
         end) ps.
Proof.
  intros descr gr ps args_my H0.

  destruct descr; simpl in *. clear coqConstr. revert ps H0.
  induction constr; intros; simpl in *; eauto.
  all: try (now ( destruct args_my; eapply H; eauto)).
  ++ destruct args_my. destruct ps; try contradiction.
     constructor.
     ** destruct r; eauto. destruct X_; simpl in *.
        split.
        eapply X_has_v. apply H0. (* TODO: WHERE DOES THIS COME FROM *)
        intros A. eapply graph_has_v_not_eq. eapply X_has_v, H0. eauto.
     ** eapply H; eauto. eapply H0.
  ++ destruct args_my. destruct ps; try contradiction.
     constructor.
     ** destruct r0; eauto. simpl in *. destruct r; simpl in *.
        split.
        eapply X_has_v. apply H0. (* TODO: WHERE DOES THIS COME FROM *)
        intros A. eapply graph_has_v_not_eq. eapply X_has_v, H0. eauto.
     ** eapply IHconstr; eauto. eapply H0.
  ++ destruct args_my. destruct ps; try contradiction.
     constructor.
     ** destruct r; eauto. destruct X_; simpl in *.
        split.
        eapply X_has_v. apply H0. (* TODO: WHERE DOES THIS COME FROM *)
        intros A. eapply graph_has_v_not_eq. eapply X_has_v, H0. eauto.
     ** eapply H; eauto. eapply H0.
  ++ subst. constructor.
Qed.

Check get_size.

(* Lemma ucov_rawmark: forall g old_v new_v,
    raw_mark (update_copied_old_vlabel g old_v new_v old_v) = true.
Proof.
  intros. unfold update_copied_old_vlabel, update_vlabel. rewrite if_true. unfold copy_v_mod_rvb. simpl.  ; easy.
Qed. *)

Definition geneeral_subsumption t n descr :
  X_in_graph_cons descr t ->
  0 <= Z.of_nat t < 250 ->
  (* n = get_size (constr descr) margs -> *)
  0 < Z.of_nat n < 2096895 ->
  funspec_sub (n_arguments (calc t n) n) (snd (alloc_make_spec_general descr n)).
Proof.
  intros t_eq A  HHA.
  assert (HH : 0 < Z.of_nat n < two_power_pos 54).  { unfold two_power_pos. simpl. rep_lia. }
  assert (R1 : 0 <= Z.of_nat t < 256) by rep_lia.
  apply NDsubsume_subsume.
  split; try reflexivity.
  split. unfold get_tulongs. subst. split; eauto.
  intros w; simpl in w; intros [g args]. normalize. unfold_for_go_lower; simpl; entailer!.
  destruct w as (((((((((gv&gr)&ps)&args_my)&roots)&sh)&tinfo_pos)&outliers)&finfo)&tinfo).
  simpl in H.
  entailer.

  unfold argsHaveTyps in H.
  simpl in H. inv H.
  unfold specs_library.full_gc. Intros.
  unfold before_gc_thread_info_rep.
  assert (graph_has_gen_0 := graph_has_gen_O gr).
  assert (~ In (inr (new_copied_v gr 0)) roots) as ROOTS_IN by (eapply new_node_roots; eapply H).
  destruct (heap_head_cons (ti_heap tinfo)) as (g0&space_rest&SPACE_NONEMPTY&g0_eq).
  assert (isptr (space_start g0) /\  writable_share (space_sh g0) /\ generation_space_compatible gr (0%nat, nth_gen gr 0, g0)) as (isptr_g0&wsh_g0&comp_g0).
  { subst; eapply spaces_g0; eauto. }
  simpl in H2. injection H2. intros. subst x. clear H2.

  eapply isptr_Vptr in isptr_g0 as (b&x'&isptr_eq).
  pose (alloc :=  Ptrofs.signed (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * used_space (heap_head (ti_heap tinfo)))))).
  pose (limit :=  Ptrofs.signed (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * total_space (heap_head (ti_heap tinfo)))))) .

  pose (vals := from_list (map (fun p => specs_library.rep_type_val gr p) ps)).
  assert (ps_size := in_graphs_size _ _ _ _ H0).
  rewrite ps_size.   erewrite <- map_length.

  Exists ((((((sh, space_sh (heap_head (ti_heap tinfo))), tinfo_pos) , vals), b),  alloc), limit).
  Exists (outlier_rep outliers * ti_token_rep tinfo *
          graph_rep gr * field_at sh specs_library.thread_info_type [StructField _heap] (ti_heap_p tinfo) tinfo_pos *
          field_at sh specs_library.thread_info_type [StructField glue._args] (ti_args tinfo) tinfo_pos *
          heap_struct_rep sh
                          ((Vptr b x',
                            (Vundef,
                             Vptr b (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * total_space (heap_head (ti_heap tinfo)))))))
                             :: map space_tri (tl (spaces (ti_heap tinfo)))) (ti_heap_p tinfo)* iter_sepcon specs_library.space_rest_rep space_rest *
         data_at_ (space_sh (heap_head (ti_heap tinfo))) (tarray int_or_ptr_type (total_space (heap_head (ti_heap tinfo)) -
        used_space (heap_head (ti_heap tinfo)) - Z.of_nat (1 + Datatypes.length ps))) (field_address0 (tarray int_or_ptr_type
          (total_space (heap_head (ti_heap tinfo)) -
           used_space (heap_head (ti_heap tinfo)))) [ArraySubsc (Z.of_nat (1 + Datatypes.length ps))]  (Vptr b
          (Ptrofs.add x'
             (Ptrofs.repr (WORD_SIZE * used_space (heap_head (ti_heap tinfo))))))) )%logic.


  entailer!.
  + (* Postcondition entailment *)
    split.

    2 : { split.
          - unfold calc. rewrite map_length. rewrite <- ps_size. unfold Z.shiftl. simpl. rep_lia.
          - unfold vals. now rewrite to_from_vec.  }

    intros rho. entailer!.

    pose (fds := map rep_field ps).
    assert (R3 : NO_SCAN_TAG <= Z.of_nat t -> ~ In None fds). rewrite NO_SCAN_TAG_eq. rep_lia.
    assert (R2 : 0 < Zlength fds < two_power_pos 54). unfold fds. rewrite Zlength_map.
    rewrite Zlength_correct. rewrite <- ps_size. rep_lia.

    pose (v := new_copied_v gr 0). Exists (repNode v).
   pose (es := get_fields gr 0 ps 0).
   Exists (add_node gr 0 (newRaw v (Z.of_nat t) fds R1 R2 R3) es).

    assert (t_size : 0 <= 1 + Zlength fds <= total_space (nth_space tinfo 0) - used_space (nth_space tinfo 0)).
   { unfold nth_space. rewrite SPACE_NONEMPTY. simpl in *. admit. (*
                                                                      0 <= 1 + Zlength fds <=
  total_space (heap_head (ti_heap tinfo)) - used_space (heap_head (ti_heap tinfo))
   TODO: Move to start. rep_lia. *) }

    Exists (graph_add.add_node_ti 0 tinfo _ t_size).
   assert (add_node_compatible gr (new_copied_v gr 0) es) by (apply get_fields_add_node_compatible).
   entailer!.

   *  split3.
      -- apply t_eq; eauto.
      -- split3.
         ++ destruct H. unfold gc_correct.sound_gc_graph, roots_compatible in *. intuition eauto. apply add_node_iso; eauto.
          ++ simpl. rewrite <- H5. autorewrite with graph_add; eauto. unfold alloc; eauto. unfold vertex_address.
             destruct comp_g0 as (comp_start&comp_sh&comp_prev).
             unfold gen_start. simpl. rewrite comp_start. unfold vertex_offset.
             simpl. rewrite comp_prev. if_tac; try contradiction.
             rewrite isptr_eq. simpl. f_equal.
             assert (8 = Ptrofs.signed (Ptrofs.repr 8)) by reflexivity.
             rewrite H23 at 1.
             rewrite <- Ptrofs.add_signed.
             rewrite !Ptrofs.add_assoc; f_equal.
             rewrite ptrofs_add_repr. f_equal. unfold WORD_SIZE. rep_lia.
          ++ simpl. autorewrite with graph_add; eauto. unfold vertex_address.
             destruct comp_g0 as (comp_start&comp_sh&comp_prev).
             unfold gen_start. simpl. rewrite comp_start. unfold vertex_offset.
             simpl. rewrite comp_prev. if_tac; try contradiction.
             rewrite isptr_eq. simpl. congruence.

      -- apply add_node_gc_condition_prop_general; eauto.
         eapply in_graphs_has; eauto.
   * unfold full_gc.

     unfold specs_library.before_gc_thread_info_rep.
     autorewrite with graph_add.
     unfold specs_library.heap_rest_rep.
     simpl. cancel.
     unfold_data_at (data_at sh specs_library.thread_info_type _  _).
     cancel. simpl.

     autorewrite with graph_add.
     rewrite !isptr_eq. simpl. unfold alloc.
     rewrite !Ptrofs.repr_signed.
     assert (Ptrofs.repr
          (Ptrofs.signed
             (Ptrofs.add x'
                (Ptrofs.repr (WORD_SIZE * used_space (heap_head (ti_heap tinfo))))) +
           Z.pos (Pos.of_succ_nat ((Datatypes.length (map (fun p : rep_type => specs_library.rep_type_val gr p) ps))) * 8)) = Ptrofs.add x'
              (Ptrofs.repr
                 (WORD_SIZE *
                  (used_space (heap_head (ti_heap tinfo)) + (1 + Zlength fds))))).
     { rewrite map_length. unfold fds. rewrite Zlength_map.
       Search Ptrofs.repr Ptrofs.signed.
       rewrite <- (Ptrofs.repr_signed x').
       rewrite ptrofs_add_repr.
       rewrite ptrofs_add_repr.
       rewrite Ptrofs.signed_repr. f_equal. rewrite Zlength_correct. unfold WORD_SIZE. rep_lia.
       admit.
     (*  Ptrofs.min_signed <= Ptrofs.signed x' + WORD_SIZE * used_space (heap_head (ti_heap tinfo)) <=
  Ptrofs.max_signed *) }

     rewrite H22. cancel.
     unfold limit. rewrite !Ptrofs.repr_signed. cancel.
     2 : { rewrite SPACE_NONEMPTY. updater. rewrite Zlength_cons. rep_lia. }
     rewrite !sepcon_assoc.
     rewrite sepcon_comm. Intros.

     cancel_left.
     -- rewrite SPACE_NONEMPTY at 1.  rewrite SPACE_NONEMPTY at 1.   updater. entailer!.
     -- cancel.
        rewrite SPACE_NONEMPTY at 1. updater. cancel.
        erewrite add_node_spatial; eauto.
        cancel.

        entailer.
        unfold vertex_at.
        rewrite !data_at_tarray_split_1'; eauto.
        cancel_left.
        { unfold specs_library.space_rest_rep. simpl.
          if_tac.
          - rewrite SPACE_NONEMPTY in H25. simpl in H25.
            rewrite isptr_eq in H25. unfold nullval in H25. destruct Archi.ptr64; congruence.
          - rewrite SPACE_NONEMPTY. simpl.
            assert (total_space (heap_head (ti_heap tinfo)) - used_space (heap_head (ti_heap tinfo)) -
        Z.pos (Pos.of_succ_nat (Datatypes.length ps)) = total_space (heap_head (ti_heap tinfo)) -
            (used_space (heap_head (ti_heap tinfo)) + (1 + Zlength fds))) as <-.
            { unfold fds. rewrite Zlength_map. rewrite Zlength_correct. rep_lia. }
            rewrite isptr_eq. simpl.
            enough (field_address0
       (tarray int_or_ptr_type
          (total_space (heap_head (ti_heap tinfo)) - used_space (heap_head (ti_heap tinfo))))
       [ArraySubsc (Z.pos (Pos.of_succ_nat (Datatypes.length ps)))]
       (Vptr b (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * used_space (heap_head (ti_heap tinfo))))))
       = Vptr b
           (Ptrofs.add x'
              (Ptrofs.repr
                 (WORD_SIZE * (used_space (heap_head (ti_heap tinfo)) + (1 + Zlength fds)))))) as -> by eauto.
            unfold field_address0. simpl. if_tac. unfold nested_field_offset. simpl.
            ++ f_equal. Search Ptrofs.add. rewrite Ptrofs.add_assoc. f_equal.
               Search Ptrofs.add Ptrofs.repr.
               rewrite Ptrofs.add_signed.
               f_equal. unfold fds. rewrite Zlength_map. rewrite Zlength_correct.
               admit.
            ++ exfalso. eapply H26. eauto. Search field_compatible0 field_compatible.
               apply field_compatible_field_compatible0. clear -H13.
               admit.

 }
        cancel_left.
        ++
          simpl.
           eapply derives_refl'.
            change_compspecs CompSpecs.

            unfold WORD_SIZE.
            autorewrite with graph_add; eauto.
            assert (space_sh (heap_head (ti_heap tinfo)) = nth_sh gr 0) as ->.
            { destruct comp_g0 as (comp_start&comp_sh&comp_prev). rewrite <- comp_sh.  reflexivity. }
            Print Z2val. Print header_new.
            unfold header_new. (* Z.of_nat t + Z.shiftl t 10 *)  simpl.
            erewrite <- space_start_vertex_address_header with (g0 := (heap_head (ti_heap tinfo))); eauto.
            unfold offset_val. rewrite isptr_eq. f_equal. simpl. unfold Z2val. unfold calc. f_equal. f_equal.
            simpl. rewrite map_length. unfold fds. rewrite Zlength_map. rewrite Zlength_correct.
            rep_lia.

        ++  assert (space_sh (heap_head (ti_heap tinfo)) = nth_sh gr 0) as ->.
            { destruct comp_g0 as (comp_start&comp_sh&comp_prev). rewrite <- comp_sh.  reflexivity. }

           autorewrite with graph_add; eauto.
           assert (1 + Z.of_nat (Datatypes.length (map (fun p : rep_type => specs_library.rep_type_val gr p) ps)) - 1 = Z.of_nat (Datatypes.length (map (fun p : rep_type => specs_library.rep_type_val gr p) ps))) as -> by rep_lia.
           assert (Zlength
              (fields_new (add_node gr 0 (newRaw v (Z.of_nat t) fds R1 R2 R3) es)
                 (newRaw v (Z.of_nat t) fds R1 R2 R3) (new_copied_v gr 0)) = Z.of_nat (Datatypes.length (map (fun p : rep_type => specs_library.rep_type_val gr p) ps))).
           { unfold fields_new.  simpl. rewrite Zlength_map. unfold make_fields.
             simpl. rewrite map_length. autorewrite with graph_add. unfold update_vlabel. if_tac; try congruence.
             rewrite Zlength_correct. rewrite make_fields'_eq_length. simpl. unfold fds.
             rewrite map_length. reflexivity. }
           rewrite H25.
           change_compspecs CompSpecs.
           assert (to_list vals = fields_new (add_node gr 0 (newRaw v (Z.of_nat t) fds R1 R2 R3) es)
           (newRaw v (Z.of_nat t) fds R1 R2 R3) (new_copied_v gr 0)) as <-.
           { unfold fields_new. simpl.

Search map make_fields.
(* lacv_field2val_make_fields_new:
  forall (g : LGraph) (v : VType) (to : nat),
  graph_has_v g v ->
  graph_has_gen g to ->
  no_dangling_dst g ->
  map (field2val (lgraph_add_copied_v g v to))
    (make_fields (lgraph_add_copied_v g v to) (new_copied_v g to)) =
  map (field2val g) (make_fields g v) *)

Print lgraph_add_copied_v.

Print add_node. Print pregraph_add_v.



 Search make_fields new_copied_v. autorewrite with graph_add.
             unfold vals.
rewrite to_from_vec.
unfold make_fields. simpl. unfold update_vlabel. if_tac; try congruence.
clear - graph_has_gen_0.
simpl. unfold fds.

remember (newRaw v (Z.of_nat t) (map rep_field ps) R1 R2 R3) as v'.
unfold es. clear es.
generalize (0)%nat at 3 5 .
clear v  Heqv' R3 R2 R1 fds. (* generalize es. clear es. *) induction ps; eauto.
simpl. intros n. assert (n +1 = S n)%nat as -> by rep_lia.  destruct a; simpl; eauto.
- intros. f_equal.  eapply IHps; eauto.
- intros. f_equal. eapply IHps.
- intros. f_equal.
  + simpl. erewrite add_node_dst_new.
    3 : { left. reflexivity. }
    * rewrite add_node_vertex_address; eauto.
      admit.
    * simpl. admit.
  + simpl. admit.

 }




           sep_apply data_at_int_or_ptr_ptr_array.
           unfold vertex_address. simpl.
           destruct comp_g0 as (comp_start&comp_sh&comp_prev).
           unfold gen_start. if_tac; try contradiction. rewrite comp_start. rewrite isptr_eq. entailer!.
           simpl. unfold vertex_offset. simpl. rewrite   comp_prev. entailer!.
           assert (WORD_SIZE * used_space (heap_head (ti_heap tinfo)) + 8 = WORD_SIZE * (used_space (heap_head (ti_heap tinfo)) + 1))%Z as ->.
           { unfold WORD_SIZE. rep_lia. }
           entailer!.
       ++ unfold vals. rewrite to_from_vec. rewrite Zlength_correct. rewrite !map_length. rep_lia.
       ++ unfold  specs_library.gc_condition_prop in *. intuition eauto.
       ++ unfold  specs_library.gc_condition_prop in *. unfold copied_vertex_existence. clear - H.
          unfold copy_compatible in H. intuition eauto.  eapply H9; eauto. simpl. (* TODO: ADAPT *)
          unfold graph_unmarked in *.

          Search raw_mark. ucov_rawmark
          admit.
  + (* Precondition entailment *)

    intros. subst alloc limit.
    unfold specs_library.before_gc_thread_info_rep.
    unfold_data_at (data_at sh _ _ _).
    rewrite !isptr_eq. simpl. rewrite !Ptrofs.repr_signed. entailer!.
    unfold specs_library.heap_rest_rep.
    rewrite SPACE_NONEMPTY. (* TODO: Tactic *)
    simpl.
    unfold specs_library.space_rest_rep at 1.
    if_tac.
    { exfalso. unfold nullval in H12. rewrite isptr_eq in *. revert H12. simple_if_tac; congruence. }
    simpl. Intros. entailer!.
    rewrite isptr_eq. unfold offset_val.
    rewrite data_at__tarray.
    assert (exists sp, Z.to_nat  (total_space (heap_head (ti_heap tinfo)) -
           used_space (heap_head (ti_heap tinfo))) = ((1 + Datatypes.length ps) + sp)%nat) as (sp&sp_eq) by admit.
    rewrite sp_eq.
    rewrite <- list_repeat_app.
    erewrite split2_data_at_Tarray_app.
    2 : reflexivity.
    entailer!.
    rewrite Zlength_list_repeat'.
    updater. cancel.
    2 : { rewrite !Zlength_list_repeat' in *. rep_lia. }
    entailer.  rewrite !map_length.
    assert (Z.pos (Pos.of_succ_nat (Datatypes.length ps)) = 1 + Z.of_nat (Datatypes.length ps)) as -> by rep_lia.
    sep_apply data_at_tulong_int_or_ptr_array.

    entailer!.

    Unshelve. all: auto using  change_composite_env_CertiGraph.
    * unfold fds in R3. simpl in R3. intros H1 H2. eapply R3; eauto.
    * unfold fds in R2. simpl in R2.
      (* TODO: How do I know this? *)
    admit.


 Admitted.

Definition subsumption_S :
  funspec_sub (n_arguments 1024 2) (snd (alloc_make_spec_general consDescr)).
Proof.
  do_funspec_sub.
  destruct w as (((((((((gv&gr)&ps)&args_my)&roots)&sh)&tinfo_pos)&outliers)&finfo)&tinfo).
  (* KS: Specific to consDescr. *)
  destruct args_my as (X_&(x& (xs & u))).
  simpl in H.
  entailer.

  unfold argsHaveTyps in H.
  simpl in H.
  inv H. inv H7. inv H8. inv H9.
  unfold specs_library.full_gc. Intros.
  unfold before_gc_thread_info_rep.
  assert (graph_has_gen_0 := graph_has_gen_O gr).
  (* assert (~ In (inr (new_copied_v gr 0)) roots) as ROOTS_IN by (eapply new_node_roots; eapply gc_cond). *)
  destruct (heap_head_cons (ti_heap tinfo)) as (g0&space_rest&SPACE_NONEMPTY&g0_eq).
  assert (isptr (space_start g0) /\  writable_share (space_sh g0) /\ generation_space_compatible gr (0%nat, nth_gen gr 0, g0)) as (isptr_g0&wsh_g0&comp_g0).
  { subst; eapply spaces_g0; eauto. }

  eapply isptr_Vptr in isptr_g0 as (b&x'&isptr_eq).
  pose (alloc :=  Ptrofs.signed (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * used_space (heap_head (ti_heap tinfo)))))).
  pose (limit :=  Ptrofs.signed (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * total_space (heap_head (ti_heap tinfo)))))) .
  Exists (((((sh, x0) , subsumptiontests.vcons _ x1 _ (subsumptiontests.vcons _ x2 _ (@subsumptiontests.vnil _))), b),  alloc), limit).
  Exists (outlier_rep outliers * ti_token_rep tinfo *
          graph_rep gr * field_at sh specs_library.thread_info_type [StructField _heap] (ti_heap_p tinfo) tinfo_pos *
          field_at sh specs_library.thread_info_type [StructField glue._args] (ti_args tinfo) tinfo_pos *
          heap_struct_rep sh
                          ((Vptr b x',
                            (Vundef,
                             Vptr b (Ptrofs.add x' (Ptrofs.repr (WORD_SIZE * total_space (heap_head (ti_heap tinfo)))))))
                             :: map space_tri (tl (spaces (ti_heap tinfo)))) (ti_heap_p tinfo)* iter_sepcon specs_library.space_rest_rep space_rest)%logic.
  entailer!.
  + (* Postcondition entailment *)
    intros. simpl.
    Print rep_type.
    Exists (repNode (new_copied_v gr 0)).
    (* TODO:
       - Define the correct graph
       - Define the right thread info.
       - Ensure all the conditions are still correct.
         + in_graph_predicate of new thing
         + garbage collection conditon
         + etc.
     *)
    rewrite <- H4.



    (* pose (fds := [rep_field x1; rep_field x2]).
         assert (R1 : 0 <= 0 < 256) by lia.
         assert (R3 : NO_SCAN_TAG <= 0 -> ~ In None fds). rewrite NO_SCAN_TAG_eq. lia.
         assert (R2 : 0 < Zlength fds < two_power_pos 54) by (unfold two_power_pos; cbn; lia). *)

    admit.
  + (* Precondition entailment *)
    simpl in H2. injection H2. intros. subst.
    subst alloc limit.
    unfold specs_library.before_gc_thread_info_rep.
    entailer!.
    unfold_data_at (data_at sh _ _ _).

    rewrite !isptr_eq.
    simpl. rewrite !Ptrofs.repr_signed.
    entailer!.

    unfold specs_library.heap_rest_rep.
    rewrite SPACE_NONEMPTY.
    simpl.
    unfold specs_library.space_rest_rep at 1.
    if_tac. admit.
    simpl. Intros. entailer!.
    (* TODOS
          - Fix sh
          - Fix array int_or_ptr_type / tulong  - see proofs_library.v, but probably need the lemma in the other direction
          - Guarantee the size
     *)
    rewrite isptr_eq. unfold offset_val.
    assert (sh = space_sh (heap_head (ti_heap tinfo))) as -> .
    { admit. }
    assert (int_or_ptr_type = tulong) as -> by admit.
    assert (total_space (heap_head (ti_heap tinfo)) - used_space (heap_head (ti_heap tinfo)) > 3) by admit.
    (* See other stuff. *)

 Admitted.


Lemma alloc_make_nat_proof  : semax_body subsumptiontests.Vprog subsumptiontests.Gprog f_alloc_make_Coq_Init_Datatypes_list_cons alloc_make_list_cons_spec.
Proof.
  rewrite <- f_alloc_cons_eq1.
  assert ((subsumptiontests.make_args 2) = [_arg0; _arg1])  as <- by admit.
  assert (_argv = _alloc_make_Coq_Init_Datatypes_list_cons) as -> by admit.
  (* assert (_argv = c *)
  rewrite cons_same_spec.
  apply (@semax_body_funspec_sub) with (phi := n_arguments 2048 2).
  -  assert (_argv = _alloc_make_Coq_Init_Datatypes_list_cons) as <- by admit.
    apply alloc_make_nat_general_proof2.
  -  admit.
  - admit.

    simpl. apply alloc_make_nat_general_proof2.


 try apply alloc_make_nat_general_proof2.
Admitted.


(* In the non-trivial case, this will require the kind of lemmas which are now burried in the current
semax_body proof on the garbage collector and the add relation.

For example, for S this will look as the following:
 *)

Definition array_type := int_or_ptr_type.

(** Propositional conditions from the garbage collector specification and getting the isomorphism property for the garbage collector:
The thread_info has to be a new one, roots and outlier stay preserved *)
Definition gc_condition_prop g t_info roots outlier :=
graph_unmarked g /\ no_backward_edge g /\ no_dangling_dst g /\ ti_size_spec t_info (** From garbage_collect_condition, removed that roots and finfo are compatible. *)
/\ safe_to_copy g
/\ graph_thread_info_compatible g t_info /\ outlier_compatible g outlier /\ roots_compatible g outlier roots
/\ gc_correct.sound_gc_graph g /\ copy_compatible g.

Definition space_rest_rep (sp: space): mpred :=
  if (Val.eq sp.(space_start) nullval)
  then emp
  else data_at_ (space_sh sp)
                (tarray int_or_ptr_type (sp.(total_space) - sp.(used_space)))
                (offset_val (WORD_SIZE * used_space sp) sp.(space_start)).

Definition heap_rest_rep (hp: heap): mpred :=
  iter_sepcon  space_rest_rep hp.(spaces).

(* Taken from Shengyi to get the right GC *)
Definition before_gc_thread_info_rep (sh: share) (ti: CertiGraph.CertiGC.GCGraph.thread_info) (t: val) :=
  let nursery := heap_head ti.(ti_heap) in
  let p := nursery.(space_start) in
  let n_lim := offset_val (WORD_SIZE * nursery.(total_space)) p in
  (data_at sh thread_info_type
          (offset_val (WORD_SIZE * nursery.(used_space)) p,
           (n_lim, (ti.(ti_heap_p), ti.(ti_args)))) t *
  heap_struct_rep
    sh ((p, (Vundef, n_lim))
          :: map space_tri (tl ti.(ti_heap).(spaces))) ti.(ti_heap_p) *
  heap_rest_rep ti.(ti_heap))%logic.

Definition full_gc g t_info roots outlier ti sh :=
  (outlier_rep outlier * before_gc_thread_info_rep sh t_info ti * ti_token_rep t_info * graph_rep g && !!gc_condition_prop g t_info roots outlier)%logic.


(* The generated actual specification, probably generated by Joomy via MetaCoq or OCaml or something else: *)
Definition alloc_make_nat_S_spec : ident * funspec :=
 DECLARE _alloc_make_Coq_Init_Datatypes_nat_S
  WITH gv : globals, g : graph, p : rep_type, n : nat, roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
  PRE  [thread_info, tulong]
       PROP (nat_in_graph g n p;
             writable_share sh
             )
       PARAMS (ti;
              rep_type_val g p)
       GLOBALS ()
       SEP ( full_gc g t_info roots outlier ti sh )
  POST [ tptr tulong ]
     EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info),
     PROP (nat_in_graph g' (S n) p';
           gc_graph_iso g roots g' roots
         )
     LOCAL (temp ret_temp (rep_type_val g' p'))
     SEP (full_gc g' t_info' roots outlier ti sh).

