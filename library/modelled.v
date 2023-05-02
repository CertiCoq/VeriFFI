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
  rewrite ?from_to, ?to_from.

Ltac props x :=
  let P := fresh in
  pose proof x as P;
  hnf in P;
  simpl in P;
  rewrite !P;
  unfold id, eq_rect in *;
  clear P.

(* opaque and transparent *)
Inductive annotated : Type :=
| TYPEPARAM : (forall (A : Type) `{Rep A}, annotated) -> annotated
| OPAQUE : forall (prim_type model_type : Type)
                    `{Isomorphism prim_type model_type},
                    (option (prim_type -> annotated)) ->
                    annotated
| TRANSPARENT : forall (A : Type) `{Rep A}, (option (A -> annotated)) -> annotated.

(* Theorem InGraph_any : forall {A : Type}, InGraph A. *)
(* Proof. intros. constructor. intros. exact False. Defined. *)
Theorem Rep_any : forall {A : Type}, Rep A. Admitted.

Fixpoint to_prim_fn_type (r : annotated) : Type :=
  match r with
  | TYPEPARAM f => forall (A : Type), to_prim_fn_type (f A Rep_any)
  | OPAQUE pt mt Iso k =>
      match k with
      | None => pt
      | Some fp => forall (p : pt), to_prim_fn_type (fp p)
      end
  | TRANSPARENT t Rep_A k =>
      match k with
      | None => t
      | Some f => forall (x : t), to_prim_fn_type (f x)
      end
  end.

Fixpoint to_model_fn_type (r : annotated) : Type :=
  match r with
  | TYPEPARAM f => forall (A : Type), to_model_fn_type (f A Rep_any)
  | OPAQUE pt mt Iso k =>
      match k with
      | None => mt
      | Some fp => forall (m : mt), to_model_fn_type (fp (@to pt mt Iso m))
      end
  | TRANSPARENT t Rep_A k =>
      match k with
      | None => t
      | Some f => forall (x : t), to_model_fn_type (f x)
      end
  end.

Record extern_properties :=
  { type_desc : annotated
  ; prim_fn : to_prim_fn_type type_desc
  ; model_fn : to_model_fn_type type_desc
  ; c_name : string
  }.

(*
From Equations Require Import Equations Signature.

Ltac rewrite_apply lem t :=
  let m := fresh "m" in
  pose (m := t);
  rewrite lem in m;
  apply m.

Equations model_spec_aux
          (a : annotated)
          (pt : to_prim_fn_type a)
          (mt : to_model_fn_type a) : Prop :=
model_spec_aux (@TYPEPARAM f) pt mt :=
  forall (A : Type), model_spec_aux (f A Rep_any) (pt A) (mt A) ;
model_spec_aux (@OPAQUE prim_type model_type Iso (Some k)) pt mt :=
  forall (x : prim_type),
    model_spec_aux (k x) (pt x)
      (mt (ltac: (rewrite_apply from_to (@from prim_type model_type Iso x)))) ;
      (* (ltac: (rewrite_apply from_to (mt (@from prim_type model_type Iso x)))) ; *)
model_spec_aux (@OPAQUE prim_type model_type Iso None) pt mt :=
  pt = to mt ;
model_spec_aux (@TRANSPARENT A Rep_A (Some k)) pt mt :=
  forall (x : A), model_spec_aux (k x) (pt x) (mt x) ;
model_spec_aux (@TRANSPARENT A Rep_A None) pt mt :=
  pt = mt.
Check from_to.
*)

Fixpoint model_spec_aux
         (a : annotated)
         (ft : to_prim_fn_type a)
         (mt : to_model_fn_type a) {struct a} : Prop.
destruct a as [f|prim_type model_type M|A R o]; simpl in ft, mt.
* exact (forall (A : Type), model_spec_aux (f A Rep_any) (ft A) (mt A)).
* destruct o as [pf|].
  - refine (forall (x : prim_type), model_spec_aux (pf x) (ft x) _).
    pose (m := mt (@from prim_type model_type M x)).
    rewrite from_to in m.
    exact m.
  - exact (ft = to mt).
* destruct o as [pf|].
  - exact (forall (x : A), model_spec_aux (pf x) (ft x) (mt x)).
  - exact (ft = mt).
Defined.

Definition model_spec (ep : extern_properties) : Prop :=
  model_spec_aux (type_desc ep) (prim_fn ep) (model_fn ep).


