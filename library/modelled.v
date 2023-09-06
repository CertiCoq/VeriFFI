Require Import String.

Require Import ZArith.
Require Import Psatz.
Require Import List.
Import ListNotations.

Require Import VeriFFI.library.isomorphism.
Require Import VeriFFI.library.meta.

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

(*
(* Old version with extra parameter: *)
Fixpoint to_model_fn_type (r : reified prim_ann) : Type :=
  match r with
  | TYPEPARAM f =>
      forall (A : Type) (H : prim_ann A),
        to_model_fn_type (f A H)
  | ARG primary ann k => forall (p : primary), to_model_fn_type (k p)
  | RES primary ann => primary
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
*)

Fixpoint to_model_fn_type (r : reified prim_ann) : Type :=
  match r with
  | TYPEPARAM f =>
      forall (A : Type),
        to_model_fn_type (f A prim_ann_any)
  | ARG primary ann k => forall (p : primary), to_model_fn_type (k p)
  | RES primary ann => primary
  end.

Fixpoint curry_model_fn
         (r : reified prim_ann)
         (mt : reflect r) {struct r} : to_model_fn_type r.
Proof.
  unfold reflect in *.
  destruct r.
  * intro A.
    refine (curry_model_fn (r A prim_ann_any) (fun P => _)).
    change (projT1 (result (TYPEPARAM prim_ann r) (A; (prim_ann_any; P)))).
    apply mt.
  * intro a.
    refine (curry_model_fn (r a) (fun P => _)).
    change (projT1 (result (ARG prim_ann A r) (a; P))).
    apply mt.
  * exact (mt tt).
Defined.

Record fn_desc :=
  { type_desc : reified prim_ann
  ; prim_fn : to_prim_fn_type type_desc
  ; model_fn : reflect type_desc
  ; f_arity : nat
  ; c_name : string
  }.

Definition curried_model_fn (d : fn_desc) : to_model_fn_type (type_desc d) :=
  curry_model_fn (type_desc d) (model_fn d).

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
  forall (x : secondary),
    model_spec_aux (k (to x)) (pt x) (mt (to x)) ;
model_spec_aux (@RES primary ann) pt mt :=
  pt = @from _ _ prim_iso mt.
*)

Fixpoint model_spec_aux
         (a : reified prim_ann)
         (ft : to_prim_fn_type a)
         (mt : to_model_fn_type a) {struct a} : Prop.
Proof.
  destruct a as [f | primary ann k | A ann]; simpl in ft, mt.
  * exact (forall (A : Type),
              model_spec_aux (f A prim_ann_any) (ft A) (mt A)).
  * destruct ann as [IG secondary Iso].
    refine (forall (x : secondary), model_spec_aux (k (to x)) (ft x) (mt (to x))).
  * destruct ann as [IG secondary Iso].
    exact (ft = from mt).
Defined.

Definition model_spec (d : fn_desc) : Prop :=
  model_spec_aux (type_desc d) (prim_fn d) (curried_model_fn d).

Ltac eq_refl_match :=
  match goal with
  | [ |- context[match ?x with | eq_refl => _ end] ] => destruct x
  (* | [ _ : context[match ?x with | eq_refl => _ end] |- _] => destruct x *)
  end.

Ltac prim_rewrites :=
  unfold curried_model_fn, curry_model_fn; simpl;
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
