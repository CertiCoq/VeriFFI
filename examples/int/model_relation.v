Require Import MetaCoq.Template.All.
Require Import String.

Require Import ZArith.
Require Import List.
Import ListNotations.


Module Type Int63.
  Axiom t : Type.
  Axiom from_Z : Z -> t.
  Axiom to_Z : t -> Z.
  Axiom add : t -> t -> t.
End Int63.

(* Axiom VSU : Type. *)
(* Axiom int63_vsu : VSU. *)
(* Axiom lift : forall {A : Type}, A -> VSU -> string -> A. *)

Module FM : Int63.
  Definition t := {z : Z | 0 <= z < 2^63}%Z.
  Definition from_Z (z : Z) : t.
    exists (Z.rem (Z.abs z) (2^63)).
    apply Z.rem_bound_pos_pos.
    apply Z.pow_pos_nonneg.
    constructor.
    apply Pos2Z.is_nonneg.
    apply Z.abs_nonneg.
  Defined.

  Definition to_Z (z : t) : Z := proj1_sig z.
  Definition add (x y : t) : t.
    destruct x as [xz x_pf], y as [yz y_pf].
    exists ((xz + yz) mod (2^63))%Z.
    split.
    * destruct x_pf as [x_pf1 _], y_pf as [y_pf1 _].
      apply Z_mod_nonneg_nonneg.
      apply Z.add_nonneg_nonneg.
      assumption. assumption.
      apply Pos2Z.is_nonneg.
    * apply Z.mod_pos_bound.
      constructor.
  Defined.
End FM.

(* Class Empty (A : Type) := {}. *)
(* Instance All_Empty : forall (A : Type), Empty A := {||}. *)

Record model_relation :=
  { mt : Type
  ; pt : Type
  ; mt_to_pt : mt -> pt
  ; pt_to_mt : pt -> mt
  ; round1 : forall (x : pt), mt_to_pt (pt_to_mt x) = x
  ; round2 : forall (x : mt), pt_to_mt (mt_to_pt x) = x
  }.

Definition identity_model_relation (T : Type) : model_relation :=
  {| mt := T
   ; pt := T
   ; mt_to_pt := id
   ; pt_to_mt := id
   ; round1 := fun x => eq_refl
   ; round2 := fun x => eq_refl
   |}.

Fixpoint f_type (arity : list model_relation) (result : model_relation) : Type :=
  match arity with
  | nil => pt result
  | cons rel arity' => pt rel -> f_type arity' result
  end.

Fixpoint model_type (arity : list model_relation) (result : model_relation) : Type :=
  match arity with
  | nil => mt result
  | cons rel arity' => mt rel -> model_type arity' result
  end.

Record extern_properties :=
  { arity : list model_relation
  ; result : model_relation
  ; f : f_type arity result
  ; model : model_type arity result
  ; c_name : string
  }.

(* Fixpoint model_spec_aux (arity : list model_relation) (result : model_relation) (f : f_type arity result) (model : model_type arity result) {struct arity} : Prop. *)
(* destruct arity. *)
(* pose (x := pt_to_mt result). *)
(* simpl in *. *)
(* exact (f = mt_to_pt result model). *)

(* simpl in *. *)
(* exact (forall (x : pt m), model_spec_aux arity0 result (f x) (model (pt_to_mt m x))). *)
(* Defined. *)
(* Print model_spec_aux. *)

Fixpoint model_spec_aux
  (arity : list model_relation) (result : model_relation)
  (f : f_type arity result) (model : model_type arity result) {struct arity} : Prop :=
  match arity as l return (f_type l result -> model_type l result -> Prop) with
  | []%list =>
      fun (f0 : f_type [] result)
        (model0 : model_type [] result) =>
      f0 = mt_to_pt result model0
  | (a :: l)%list =>
      (fun (m : model_relation)
         (arity0 : list model_relation)
         (f0 : f_type (m :: arity0) result)
         (model0 : model_type (m :: arity0)
                     result) =>
       forall x : pt m,
       model_spec_aux arity0 result
         (f0 x) (model0 (pt_to_mt m x))) a l
  end f model.

Definition model_spec (ep : extern_properties) : Prop :=
  model_spec_aux (arity ep) (result ep) (f ep) (model ep).

Module C_Int63.
  Axiom rel' : {r : model_relation | mt r = FM.t}.
  Definition rel := proj1_sig rel'.

  Definition t := pt rel.

  Axiom add : t -> t -> t.
  Axiom from_Z : Z -> t.
  Axiom to_Z : t -> Z.

  Definition from_Z_ep : extern_properties.
    apply (Build_extern_properties [identity_model_relation Z] rel).
    exact from_Z.
    simpl.
      pose proof (x := proj2_sig rel').
      simpl in x.
      fold rel in x.
      rewrite x. exact FM.from_Z.
    exact "int63_from_Z"%string.
  Defined.

  Definition to_Z_ep : extern_properties.
    apply (Build_extern_properties [rel] (identity_model_relation Z)).
    exact to_Z.
    simpl.
      pose proof (x := proj2_sig rel').
      simpl in x.
      fold rel in x.
      rewrite x. exact FM.to_Z.
    exact "int63_to_Z"%string.
  Defined.

  Definition add_ep : extern_properties.
    apply (Build_extern_properties [rel;rel] rel).
    exact add.
    simpl.
      pose proof (x := proj2_sig rel').
      simpl in x.
      fold rel in x.
      rewrite x. exact FM.add.
    exact "int63_add"%string.
  Defined.


Print add_ep.


  (* Definition add_ep : extern_properties := *)
  (*   (* ltac:(check FM.add int63_vsu "int63_add"). *) *)
  (*   {| arity := [rel; rel] *)
  (*   ; result := rel *)
  (*   ; f := add *)
  (*   ; model := FM.add *)
  (*   ; c_name := "int63_add" *)
  (*   |}. *)

  (* Axiom add_properties : ltac:(check add_ep). *)

  Axiom add_properties : model_spec add_ep.
  Axiom from_Z_properties : model_spec from_Z_ep.
  Axiom to_Z_properties : model_spec to_Z_ep.

End C_Int63.


Lemma seven : C_Int63.to_Z (C_Int63.add (C_Int63.from_Z 3%Z) (C_Int63.from_Z 4%Z)) = 7%Z.
Proof.
  pose proof (FP := C_Int63.from_Z_properties).
  pose proof (TP := C_Int63.to_Z_properties).
  pose proof (AP := C_Int63.add_properties).
  hnf in FP, TP, AP.
  simpl in FP, TP, AP.
  rewrite !FP, !TP, !AP.
  pose proof (x := proj2_sig C_Int63.rel'). simpl in x.
  unfold id, eq_rect_r in *.
  repeat rewrite (round2 C_Int63.rel).

  About rew_compose.


  (* rewrite (C_Int63.add_properties). *)
  (* simpl. *)
  (* rewrite (round2 C_Int63.rel). *)
  (* rewrite (round2 C_Int63.rel). *)
  (* unfold eq_rect_r. *)
  (* Search _ (eq_rect). *)

(* Proof. *)
(*   pose proof (C_Int63.from_Z_properties). *)
(*   pose proof (C_Int63.from_Z_properties). *)
(*   hnf in H. *)
(*   simpl in H. *)
(*   rewrite !H. *)
(*   pose proof (x := proj2_sig C_Int63.rel'). *)
(*   simpl. *)
(*   unfold id in *. *)
(*   rewrite (C_Int63.add_properties). *)
(*   simpl. *)
(*   rewrite (round2 C_Int63.rel). *)
(*   rewrite (round2 C_Int63.rel). *)
(*   unfold eq_rect_r. *)
(*   Search _ (eq_rect). *)



  (* (* unfinished *) *)
  (* destruct (proj2_sig C_Int63.rel'). *)
  (* About rew_compose. *)
  (* unfold eq_sym. *)
  (* rewrite rew_compose. *)
  (* Search _ (eq_rect). *)
  (* simpl. *)
Qed.

(* Class Verified {model_type : Type} {prim_type : Type} *)
(*                {fn_type : Type} (fn : fn_type) := *)
(*   {| c_name : string *)
(*    ; vsu : VSU *)
(*    ; model : T *)
(*    |}. *)

(* Instance Verified_add : @Verified C_Int63.t _ C_Int63.add := *)
(*   {| c_name := "int63_add" *)
(*    ; vsu := int63_vsu *)
(*    ; model := FM.add *)
(*    |}. *)

(* CertiCoq Compile prog Extract Constants [add => "int63_add"]. *)
