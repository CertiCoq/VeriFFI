Require Import String.

Require Import ZArith.
Require Import Psatz.
Require Import List.
Import ListNotations.

Require Import VeriFFI.library.isomorphism.
Require Import VeriFFI.library.meta.

Class ForeignInGraph (model foreign  : Type) : Type :=
  model_in_graph : InGraph model.

Class foreign_ann (primary : Type) : Type :=
  { secondary : Type
  ; foreign_in_graph :: ForeignInGraph primary secondary
  ; foreign_iso : Isomorphism primary secondary
  }.

Definition transparent {A : Type} `{IG_A : InGraph A} : foreign_ann A :=
  {| secondary := A
   ; foreign_in_graph := IG_A
   ; foreign_iso := Isomorphism_refl
   |}.

Definition opaque {A B : Type}
                 `{IG_A : ForeignInGraph A B}
                 `{Iso : Isomorphism A B} : foreign_ann A :=
  {| secondary := B
   ; foreign_in_graph := IG_A
   ; foreign_iso := Iso
   |}.

Definition foreign_ann_any {A} : foreign_ann A := @transparent A InGraph_any.

Fixpoint to_foreign_fn_type (r : reified foreign_ann) : Type :=
  match r with
  | TYPEPARAM f =>
      forall (A : Type),
        to_foreign_fn_type (f A foreign_ann_any)
  | ARG primary ann k =>
      forall (m : secondary),
        to_foreign_fn_type (k (@to primary secondary foreign_iso m))
  | RES _ ann => secondary
  end.

Fixpoint to_model_fn_type (r : reified foreign_ann) : Type :=
  match r with
  | TYPEPARAM f =>
      forall (A : Type),
        to_model_fn_type (f A foreign_ann_any)
  | ARG primary ann k => forall (p : primary), to_model_fn_type (k p)
  | RES primary ann => primary
  end.

Fixpoint curry_model_fn
         (r : reified foreign_ann)
         (mt : reflect r) {struct r} : to_model_fn_type r.
Proof.
  unfold reflect in *.
  destruct r.
  * intro A.
    refine (curry_model_fn (r A foreign_ann_any) (fun P => _)).
    change (projT1 (result (TYPEPARAM foreign_ann r) (A; (foreign_ann_any; P)))).
    apply mt.
  * intro a.
    refine (curry_model_fn (r a) (fun P => _)).
    change (projT1 (result (ARG foreign_ann A r) (a; P))).
    apply mt.
  * exact (mt tt).
Defined.

Record fn_desc :=
  { type_desc : reified foreign_ann
  ; foreign_fn : to_foreign_fn_type type_desc
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
          (a : reified foreign_ann)
          (pt : to_foreign_fn_type a)
          (mt : to_model_fn_type a) : Prop :=
model_spec_aux (@TYPEPARAM f) pt mt :=
  forall (A : Type), model_spec_aux (f A foreign_ann_any) (pt A) (mt A) ;
model_spec_aux (@ARG primary ann k) pt mt :=
  forall (x : secondary),
    model_spec_aux (k (to x)) (pt x) (mt (to x)) ;
model_spec_aux (@RES primary ann) pt mt :=
  pt = @from _ _ foreign_iso mt.
*)

Fixpoint model_spec_aux
         (a : reified foreign_ann)
         (ft : to_foreign_fn_type a)
         (mt : to_model_fn_type a) {struct a} : Prop.
Proof.
  destruct a as [f | primary ann k | A ann]; simpl in ft, mt.
  * exact (forall (A : Type),
              model_spec_aux (f A foreign_ann_any) (ft A) (mt A)).
  * destruct ann as [secondary FIG Iso].
    unfold ForeignInGraph in FIG.
    refine (forall (x : secondary), model_spec_aux (k (to x)) (ft x) (mt (to x))).
  * destruct ann as [secondary IG Iso].
    exact (ft = from mt).
Defined.

Definition model_spec (d : fn_desc) : Prop :=
  model_spec_aux (type_desc d) (foreign_fn d) (curried_model_fn d).

Ltac eq_refl_match :=
  match goal with
  | [ |- context[match ?x with | eq_refl => _ end] ] => destruct x
  (* | [ _ : context[match ?x with | eq_refl => _ end] |- _] => destruct x *)
  end.

Ltac foreign_rewrites :=
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
