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



