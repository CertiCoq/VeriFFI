Require Import String.

Require Import ZArith.
Require Import Psatz.
Require Import List.
Import ListNotations.

Require Import VeriFFI.library.isomorphism.
Require Import VeriFFI.library.meta.
Require Import VeriFFI.library.modelled.

Require Import VeriFFI.verification.graph_add.
Require Import VeriFFI.verification.specs_library.
Require Import VeriFFI.verification.specs_general.

Require Import VST.floyd.proofauto.

Definition tvalue : type :=
  talignas (if Archi.ptr64 then 3%N else 2%N) (tptr tvoid).

Definition t_tinfo : type := Tstruct (ident_of_string "thread_info") noattr.

Definition get_c_typesig
           (c : reified prim_ann)
           (arity : nat) : compcert_rmaps.typesig :=
  (cons t_tinfo (repeat tvalue arity), tvalue).

(** Generation of the in_graph predicates, given the constructor arguments. *)
Fixpoint in_graphs
         (g : graph) (c : reified prim_ann) (xs : args c) (ps : list rep_type) : Prop :=
  match c as l return (args l -> Prop) with
  | TYPEPARAM f =>
      fun H =>
        let '(A; (ann; xs')) := H in
        in_graphs g (f A ann) xs' ps
  | ARG A ann f =>
      fun H =>
        let '(x; xs') := H in
        match ps with
        | [] => False
        | p :: ps' => @is_in_graph A (@prim_in_graph A ann) g x p /\ in_graphs g (f x) xs' ps'
        end
  | RES x _ => fun _ => ps = nil
  end xs.

Definition fn_desc_to_funspec_aux
           (c : reified prim_ann)
           (model_fn : meta.reflect c)
           (arity : nat) : funspec :=
  WITH gv : globals, g : graph, roots : GCGraph.roots_t, sh : share,
       xs : args c, ps : list rep_type, ti : val,
       outlier : GCGraph.outlier_t, t_info : GCGraph.thread_info
   PRE [[ cons t_tinfo (repeat tvalue arity) ]]
       PROP (writable_share sh ;
              in_graphs g c xs ps)
       (PARAMSx (ti :: map (rep_type_val g) ps)
         (SEPx (full_gc g t_info roots outlier ti sh gv :: nil)))
   POST [ tvalue ]
       EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info),
          PROP (let r := result c xs in
                @is_in_graph (projT1 r) (@prim_in_graph (projT1 r) (projT2 r)) g'
                  (model_fn xs) p' ;
                gc_graph_iso g roots g' roots)
          RETURN  (rep_type_val g' p')
          SEP (full_gc g' t_info' roots outlier ti sh gv).

Definition fn_desc_to_funspec (d : fn_desc) (xs : args (type_desc d)) : ident * funspec :=
  (ident_of_string (c_name d),
   fn_desc_to_funspec_aux (type_desc d) (model_fn d) (f_arity d)).
