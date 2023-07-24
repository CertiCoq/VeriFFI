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
(* Inductive annotated : Type := *)
(* | TYPEPARAM : (forall (A : Type) `{InGraph A}, annotated) -> annotated *)
(* | OPAQUE : forall (prim_type model_type : Type) *)
(*                     `{Isomorphism prim_type model_type}, *)
(*                     (option (prim_type -> annotated)) -> *)
(*                     annotated *)
(* | TRANSPARENT : forall (A : Type) `{InGraph A}, (option (A -> annotated)) -> annotated. *)

Inductive prim_ann (actual_type : Type) : Type :=
| OPAQUE : forall (model_type : Type) `{InGraph actual_type}, `{Isomorphism actual_type model_type} -> prim_ann actual_type
| TRANSPARENT : `{InGraph actual_type} -> prim_ann actual_type.

Definition prim_in_graph {A : Type} (p : prim_ann A) : InGraph A :=
  match p with
  | @OPAQUE _ mt ig _ => ig
  | @TRANSPARENT _ ig => ig
  end.

Fixpoint to_prim_fn_type (r : reified prim_ann) : Type :=
  match r with
  | TYPEPARAM f =>
      forall (A : Type),
        to_prim_fn_type (f A (@TRANSPARENT A InGraph_any))
  | ARG pt ann k =>
      match ann with
      | OPAQUE mt _ Iso => forall (p : pt), to_prim_fn_type (k p)
      | TRANSPARENT InGraph_A => forall (x : pt), to_prim_fn_type (k x)
      end
 | RES pt ann =>
      match ann with
      | OPAQUE mt _ Iso => pt
      | TRANSPARENT InGraph_A => pt
      end
  end.

Fixpoint to_model_fn_type (r : reified prim_ann) : Type :=
  match r with
  | TYPEPARAM f =>
      forall (A : Type),
        to_model_fn_type (f A (@TRANSPARENT A InGraph_any))
  | ARG pt ann k =>
      match ann with
      | OPAQUE mt _ Iso => forall (m : mt), to_model_fn_type (k (@to pt mt Iso m))
      | TRANSPARENT InGraph_A => forall (x : pt), to_model_fn_type (k x)
      end
 | RES pt ann =>
      match ann with
      | OPAQUE mt _ Iso => mt
      | TRANSPARENT InGraph_A => pt
      end
  end.

Record extern_properties :=
  { type_desc : reified prim_ann
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
  forall (A : Type), model_spec_aux (f A InGraph_any) (pt A) (mt A) ;
model_spec_aux (@OPAQUE prim_type model_type Iso (Some k)) pt mt :=
  forall (x : prim_type),
    model_spec_aux (k x) (pt x)
      (mt (ltac: (rewrite_apply from_to (@from prim_type model_type Iso x)))) ;
      (* (ltac: (rewrite_apply from_to (mt (@from prim_type model_type Iso x)))) ; *)
model_spec_aux (@OPAQUE prim_type model_type Iso None) pt mt :=
  pt = to mt ;
model_spec_aux (@TRANSPARENT A InGraph_A (Some k)) pt mt :=
  forall (x : A), model_spec_aux (k x) (pt x) (mt x) ;
model_spec_aux (@TRANSPARENT A InGraph_A None) pt mt :=
  pt = mt.
Check from_to.
*)


Fixpoint model_spec_aux
         (a : reified prim_ann)
         (ft : to_prim_fn_type a)
         (mt : to_model_fn_type a) {struct a} : Prop.
Proof.
  destruct a as [f | prim_type ann k | A ann]; simpl in ft, mt.
  * exact (forall (A : Type),
              model_spec_aux (f A (@TRANSPARENT A InGraph_any)) (ft A) (mt A)).
  * destruct ann as [model_type Iso | R].
    - refine (forall (x : prim_type), model_spec_aux (k x) (ft x) _).
      pose (m := mt (@from prim_type model_type _ x)).
      rewrite from_to in m.
      exact m.
    - exact (forall (x : prim_type), model_spec_aux (k x) (ft x) (mt x)).
  * destruct ann as [model_type Iso | R].
    - exact (ft = to mt).
    - exact (ft = mt).
Defined.

Definition model_spec (ep : extern_properties) : Prop :=
  model_spec_aux (type_desc ep) (prim_fn ep) (model_fn ep).
