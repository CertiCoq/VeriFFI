Require Import String.

Require Import ZArith.
Require Import Psatz.
Require Import List.
Import ListNotations.

Require Import VeriFFI.library.isomorphism.
Require Import VeriFFI.library.meta.

Ltac eq_refl_match :=
  match goal with
  | [ |- context[match ?x with | eq_refl => _ end] ] => destruct x
  (* | [ _ : context[match ?x with | eq_refl => _ end] |- _] => destruct x *)
  end.

Ltac prim_rewrites :=
  repeat eq_refl_match;
  repeat rewrite ?from_to, ?to_from.

Ltac props x :=
  let P := fresh in
  pose proof x as P;
  hnf in P;
  simpl in P;
  rewrite !P;
  unfold id, eq_rect in *;
  clear P.

(* opaque and transparent *)
(* Inductive annotated : Type := *)
(* | TYPEPARAM : (forall (A : Type) `{InGraph A}, annotated) -> annotated *)
(* | OPAQUE : forall (prim_type model_type : Type) *)
(*                     `{Isomorphism prim_type model_type}, *)
(*                     (option (prim_type -> annotated)) -> *)
(*                     annotated *)
(* | TRANSPARENT : forall (A : Type) `{InGraph A}, (option (A -> annotated)) -> annotated. *)


(* Inductive prim_ann (actual_type : Type) `(InGraph actual_type) : Type := *)
(* | OPAQUE : forall (model_type : Type) `{InGraph actual_type}, `{Isomorphism actual_type model_type} -> prim_ann actual_type *)
(* | TRANSPARENT : `{InGraph actual_type} -> prim_ann actual_type. *)


Class prim_ann (primary : Type) : Type :=
  { prim_in_graph : InGraph primary
  ; secondary : Type
  ; prim_iso : Isomorphism primary secondary
  }.

Definition transparent {A : Type} `{IG_A : InGraph A} : prim_ann A :=
  {| prim_in_graph := IG_A
   ; secondary := A
   ; prim_iso := Isomorphism_refl
   |}.

Definition opaque {A : Type} (B : Type)
                 `{IG_A : InGraph A} `{Iso : Isomorphism A B} : prim_ann A :=
  {| prim_in_graph := IG_A
   ; secondary := B
   ; prim_iso := Iso
   |}.

Definition prim_ann_any {A} : prim_ann A := @transparent A InGraph_any.

Fixpoint to_model_fn_type (r : reified prim_ann) : Type :=
  match r with
  | TYPEPARAM f =>
      forall (A : Type) (H : prim_ann A),
        to_model_fn_type (f A H)
  | ARG primary ann k => forall (p : primary), to_model_fn_type (k p)
  | RES primary ann => primary
  end.

Fixpoint to_prim_fn_type (r : reified prim_ann) : Type :=
  match r with
  | TYPEPARAM f =>
      forall (A : Type),
        to_prim_fn_type (f A prim_ann_any)
  | ARG primary ann k =>
      forall (m : secondary),
        to_prim_fn_type (k (@to primary secondary prim_iso m))
  | RES _ ann => secondary
  end.

Fixpoint uncurry (r : reified prim_ann)
                 (mt : to_model_fn_type r) {struct r} : reflect r.
Proof.
  destruct r; simpl in mt; intros P; unfold reflect in *.
  * destruct P as [A [ H rest ]].
    specialize (mt _ H).
    simpl in *.
    specialize (uncurry _ mt).
    auto.
  * destruct P as [a rest].
    specialize (mt a).
    simpl in *.
    specialize (uncurry _ mt).
    auto.
  * auto.
Defined. 

Record fn_desc :=
  { type_desc : reified prim_ann
  ; prim_fn : to_prim_fn_type type_desc
  ; model_fn : to_model_fn_type type_desc
  ; f_arity : nat
  ; c_name : string
  }.

Definition uncurried_model_fn (d : fn_desc) : reflect (type_desc d) :=
  uncurry (type_desc d) (model_fn d).

(*
From Equations Require Import Equations Signature.

Ltac rewrite_apply lem t :=
  let m := fresh "m" in
  pose (m := t);
  rewrite lem in m;
  apply m.

Equations model_spec_aux
          (a : reified prim_ann)
          (pt : to_prim_fn_type a)
          (mt : to_model_fn_type a) : Prop :=
model_spec_aux (@TYPEPARAM f) pt mt :=
  forall (A : Type), model_spec_aux (f A prim_ann_any) (pt A) (mt A) ;
model_spec_aux (@ARG primary ann k) pt mt :=
  forall (x : primary),
    model_spec_aux (k x) (pt x)
      (ltac: (rewrite_apply (@from_to _ _ prim_iso) (mt (@from _ _ prim_iso x)))) ;
model_spec_aux (@RES primary ann) pt mt :=
  pt = @to _ _ prim_iso mt.
*)

Fixpoint model_spec_aux
         (a : reified prim_ann)
         (ft : to_prim_fn_type a)
         (mt : to_model_fn_type a) {struct a} : Prop.
Proof.
  destruct a as [f | primary ann k | A ann]; simpl in ft, mt.
  * exact (forall (A : Type),
              model_spec_aux (f A prim_ann_any) (ft A) (mt A prim_ann_any)).
  * destruct ann as [IG secondary Iso].
    refine (forall (x : secondary), model_spec_aux (k (to x)) (ft x) (mt (to x))).
    (* pose (m := ft (@from primary secondary _ x)). *)
    (* rewrite from_to in m. *)
    (* exact m. *)
  * destruct ann as [IG secondary Iso].
    exact (ft = from mt).
Defined.

Definition model_spec (d : fn_desc) : Prop :=
  model_spec_aux (type_desc d) (prim_fn d) (model_fn d).
