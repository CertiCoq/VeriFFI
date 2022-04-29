Require Import MetaCoq.Template.All.
Require Import String.

Require Import ZArith.
Require Import Psatz.
Require Import List.
Import ListNotations.

Ltac eq_refl_match :=
  match goal with
  | [ |- context[match ?x with | eq_refl => _ end] ] => destruct x
  (* | [ _ : context[match ?x with | eq_refl => _ end] |- _] => destruct x *)
  end.

Ltac props x :=
  let P := fresh in
  pose proof x as P;
  hnf in P;
  simpl in P;
  rewrite !P;
  unfold id, eq_rect in *.

Class Modelled (prim_type model_type : Type) :=
  { model_to_prim : model_type -> prim_type
  ; prim_to_model : prim_type -> model_type
  ; prim_to_model_to_prim : forall (x : prim_type), model_to_prim (prim_to_model x) = x
  ; model_to_prim_to_model : forall (x : model_type), prim_to_model (model_to_prim x) = x
  }.

Instance Modelled_same {A : Type} : Modelled A A.
  refine (@Build_Modelled A A id id _ _); auto.
Defined.

Require Import VeriFFI.library.meta.

(* opaque and transparent *)
Inductive annotated : Type :=
| TYPEPARAM : (forall (A : Type) `{Rep A}, annotated) -> annotated
| OPAQUE : forall (prim_type model_type : Type)
                    `{Modelled prim_type model_type},
                    (option (prim_type -> annotated)) ->
                    annotated
| TRANSPARENT : forall (A : Type) `{Rep A}, (option (A -> annotated)) -> annotated.

Definition Rep_Z : Rep Z. Admitted.

Theorem Rep_any : forall {A : Type}, Rep A. Admitted.

Fixpoint to_prim_fn_type (r : annotated) : Type :=
  match r with
  | TYPEPARAM f => forall (A : Type), to_prim_fn_type (f A Rep_any)
  | OPAQUE pt mt M o =>
      match o with
      | None => pt
      | Some fp => forall (p : pt), to_prim_fn_type (fp p)
      end
  | TRANSPARENT t R o =>
      match o with
      | None => t
      | Some f => forall (x : t), to_prim_fn_type (f x)
      end
  end.

Fixpoint to_model_fn_type (r : annotated) : Type :=
  match r with
  | TYPEPARAM f => forall (A : Type), to_model_fn_type (f A Rep_any)
  | OPAQUE pt mt M o =>
      match o with
      | None => mt
      | Some fp => forall (m : mt), to_model_fn_type (fp (model_to_prim m))
      end
  | TRANSPARENT t R o =>
      match o with
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

Fixpoint model_spec_aux
         (a : annotated)
         (ft : to_prim_fn_type a)
         (mt : to_model_fn_type a) {struct a} : Prop.
destruct a as [f|prim_type model_type M|A R o]; simpl in ft, mt.
* exact (forall (A : Type), model_spec_aux (f A Rep_any) (ft A) (mt A)).
* destruct o as [pf|].
  - refine (forall (x : prim_type), model_spec_aux (pf x) (ft x) _).
    pose (m := mt (prim_to_model x)).
    rewrite prim_to_model_to_prim in m.
    exact m.
  - exact (ft = model_to_prim mt).
* destruct o as [pf|].
  - exact (forall (x : A), model_spec_aux (pf x) (ft x) (mt x)).
  - exact (ft = mt).
Defined.

Definition model_spec (ep : extern_properties) : Prop :=
  model_spec_aux (type_desc ep) (prim_fn ep) (model_fn ep).

Module IntVerification.

Module Type UInt63.
  Axiom t : Type.
  Axiom from_Z : Z -> t.
  Axiom to_Z : t -> Z.
  Axiom add : t -> t -> t.
  Axiom mul : t -> t -> t.
End UInt63.

(* Axiom VSU : Type. *)
(* Axiom int63_vsu : VSU. *)
(* Axiom lift : forall {A : Type}, A -> VSU -> string -> A. *)

Module FM <: UInt63.
  Definition t := {z : Z | 0 <= z < 2^63}%Z.
  Definition from_Z (z : Z) : t.
    exists (Z.modulo z (2^63)).
    apply Z_mod_lt.
    constructor.
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

  Definition mul (x y : t) : t.
    destruct x as [xz x_pf], y as [yz y_pf].
    exists ((xz * yz) mod (2^63))%Z.
    split.
    * destruct x_pf as [x_pf1 _], y_pf as [y_pf1 _].
      apply Z_mod_nonneg_nonneg.
      apply Z.mul_nonneg_nonneg.
      assumption. assumption.
      apply Pos2Z.is_nonneg.
    * apply Z.mod_pos_bound.
      constructor.
  Defined.
End FM.

Module C : UInt63.
  Axiom t : Type.
  Axiom from_Z : Z -> t.
  Axiom to_Z : t -> Z.
  Axiom add : t -> t -> t.
  Axiom mul : t -> t -> t.
End C.



Module UInt63_Proofs.
  Definition Rep_Z : Rep Z. Admitted.
  Axiom Modelled_t : Modelled C.t FM.t.

  Definition from_Z_ep : extern_properties :=
    {| type_desc :=
        @TRANSPARENT Z Rep_Z
           (Some (fun z => @OPAQUE _ _ Modelled_t None))
     ; prim_fn := C.from_Z
     ; model_fn := FM.from_Z
     ; c_name := "int63_from_Z"
     |}.

  Definition to_Z_ep : extern_properties :=
    {| type_desc :=
        @OPAQUE _ _ Modelled_t
           (Some (fun z => @TRANSPARENT Z Rep_Z None))
     ; prim_fn := C.to_Z
     ; model_fn := FM.to_Z
     ; c_name := "int63_to_Z"
     |}.

  Definition add_ep : extern_properties :=
    {| type_desc :=
          @OPAQUE _ _ Modelled_t
            (Some (fun i =>
              @OPAQUE _ _ Modelled_t
                (Some (fun i => @OPAQUE _ _ Modelled_t None))))
     ; prim_fn := C.add
     ; model_fn := FM.add
     ; c_name := "int63_add"
     |}.

  Definition mul_ep : extern_properties :=
    {| type_desc :=
          @OPAQUE _ _ Modelled_t
            (Some (fun i =>
              @OPAQUE _ _ Modelled_t
                (Some (fun i => @OPAQUE _ _ Modelled_t None))))
     ; prim_fn := C.mul
     ; model_fn := FM.mul
     ; c_name := "int63_mul"
     |}.

  Axiom from_Z_properties : model_spec from_Z_ep.
  Axiom to_Z_properties : model_spec to_Z_ep.
  Axiom add_properties : model_spec add_ep.
  Axiom mul_properties : model_spec mul_ep.

  Lemma seven : C.to_Z (C.add (C.from_Z 3%Z) (C.from_Z 4%Z)) = 7%Z.
  Proof.
    props from_Z_properties.
    props to_Z_properties.
    props add_properties.
    repeat eq_refl_match.
    rewrite !prim_to_model_to_prim, !model_to_prim_to_model.
    unfold FM.to_Z, FM.add, FM.from_Z.
    simpl.
    rewrite Z.mod_small.
    auto.
    lia.
  Qed.

  Check Z.add_assoc.
  Lemma add_assoc : forall (x y z : Z),
    C.to_Z (C.add (C.from_Z x) (C.add (C.from_Z y) (C.from_Z z))) =
    C.to_Z (C.add (C.add (C.from_Z x) (C.from_Z y)) (C.from_Z z)).
  Proof.
    intros x y z.
    props from_Z_properties.
    props to_Z_properties.
    props add_properties.
    repeat eq_refl_match.
    rewrite !prim_to_model_to_prim, !model_to_prim_to_model.
    unfold FM.add, FM.from_Z, FM.to_Z.
    simpl.
    rewrite <- !(Z.add_mod y z).
    rewrite <- !(Z.add_mod x y).
    rewrite <- !(Z.add_mod).
    f_equal.
    apply Z.add_assoc.
    all: lia.
  Qed.

  Lemma mul_add_distr_l : forall (x y z : Z),
    C.to_Z (C.mul (C.from_Z x) (C.add (C.from_Z y) (C.from_Z z))) =
    C.to_Z (C.add (C.mul (C.from_Z x) (C.from_Z y)) (C.mul (C.from_Z x) (C.from_Z z))).
  Proof.
    intros x y z.
    props from_Z_properties.
    props to_Z_properties.
    props add_properties.
    props mul_properties.
    repeat eq_refl_match.
    rewrite !prim_to_model_to_prim, !model_to_prim_to_model.
    unfold FM.mul, FM.add, FM.from_Z, FM.to_Z.
    simpl.
    pose (y' := Z.modulo y (Z.pow_pos 2 63)); fold y'.
    pose (z' := Z.modulo z (Z.pow_pos 2 63)); fold z'.
    rewrite <- Zplus_mod.
    rewrite <- Z.mul_add_distr_l.
    rewrite Zmult_mod_idemp_r.
    auto.
  Qed.

  Lemma mul_add_distr_r : forall (x y z : Z),
    C.to_Z (C.mul (C.add (C.from_Z x) (C.from_Z y)) (C.from_Z z)) =
    C.to_Z (C.add (C.mul (C.from_Z x) (C.from_Z z)) (C.mul (C.from_Z y) (C.from_Z z))).
  Proof.
    intros x y z.
    props from_Z_properties.
    props to_Z_properties.
    props add_properties.
    props mul_properties.
    repeat eq_refl_match.
    rewrite !prim_to_model_to_prim, !model_to_prim_to_model.
    unfold FM.mul, FM.add, FM.from_Z, FM.to_Z.
    simpl.
    pose (x' := Z.modulo y (Z.pow_pos 2 63)); fold x'.
    pose (y' := Z.modulo y (Z.pow_pos 2 63)); fold y'.
    pose (z' := Z.modulo z (Z.pow_pos 2 63)); fold z'.
    rewrite <- Zplus_mod.
    rewrite <- Z.mul_add_distr_r.
    rewrite Zmult_mod_idemp_l.
    auto.
  Qed.

End UInt63_Proofs.

End IntVerification.

Module ArrayVerification.

Module Type Array.
  Axiom ST : Type -> Type.
  Axiom array : Type -> Type.
  Axiom new : forall {A}, N -> A -> ST (array A).
  Axiom set : forall {A}, array A -> N -> A -> ST unit.
  Axiom get : forall {A}, array A -> N -> ST (option A).
  Axiom delete : forall {A}, array A -> ST unit.
End Array.

Module FM <: Array.
  Definition ST (A : Type) : Type. Admitted.
  Definition array (A : Type) : Type := list A.
  Definition new {A} (length : N) (fill : A) : ST (array A). Admitted.
  Definition set {A} (arr : array A) (index : N) (elt : A) : ST unit. Admitted.
  Definition get {A} (arr : array A) (index : N) : ST (option A). Admitted.
  Definition delete {A} (arr : array A) : ST unit. Admitted.
End FM.

Module C : Array.
  Axiom ST : Type -> Type.
  Axiom array : Type -> Type.
  Axiom new : forall {A}, N -> A -> ST (array A).
  Axiom set : forall {A}, array A -> N -> A -> ST unit.
  Axiom get : forall {A}, array A -> N -> ST (option A).
  Axiom delete : forall {A}, array A -> ST unit.
End C.

Module Array_Proofs.
  Definition Rep_N : Rep N. Admitted.
  Axiom Modelled_array : forall {A A'}, Modelled A A' -> Modelled (C.array A) (FM.array A').
  Axiom Modelled_ST : forall {A A'}, Modelled A A' -> Modelled (C.ST A) (FM.ST A').

  Definition new_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
        @TRANSPARENT N Rep_N (Some (fun n =>
          @TRANSPARENT A Rep_A (Some (fun a =>
            @OPAQUE (C.ST (C.array A)) (FM.ST (FM.array A))
                    (Modelled_ST (Modelled_array _)) None)))))
     ; prim_fn := @C.new
     ; model_fn := @FM.new
     ; c_name := "array_new"
     |}.

  Definition set_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
        @OPAQUE (C.array A) (FM.array A) (Modelled_array _) (Some (fun arr =>
          @TRANSPARENT N Rep_N (Some (fun n =>
             @TRANSPARENT A Rep_A (Some (fun a =>
               @OPAQUE (C.ST unit) (FM.ST unit) (Modelled_ST _) None)))))))
     ; prim_fn := @C.set
     ; model_fn := @FM.set
     ; c_name := "array_set"
     |}.

  Definition get_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
        @OPAQUE (C.array A) (FM.array A) (Modelled_array _) (Some (fun arr =>
          @TRANSPARENT N Rep_N (Some (fun n =>
            @OPAQUE (C.ST (option A)) (FM.ST (option A)) (Modelled_ST _) None)))))
     ; prim_fn := @C.get
     ; model_fn := @FM.get
     ; c_name := "array_get"
     |}.

  Definition delete_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
        @OPAQUE (C.array A) (FM.array A) (Modelled_array _) (Some (fun arr =>
          @OPAQUE (C.ST unit) (FM.ST unit) (Modelled_ST _) None)))
     ; prim_fn := @C.delete
     ; model_fn := @FM.delete
     ; c_name := "array_delete"
     |}.

  Axiom new_properties : model_spec new_ep.
  Axiom set_properties : model_spec set_ep.
  Axiom get_properties : model_spec get_ep.
  Axiom delete_properties : model_spec delete_ep.

  Fail Lemma set_get :
    forall {A : Type} (arr : C.array A) (n : N) (a : A),
      bind (C.set arr n a) (fun _ => C.get arr n) = pure a.
  (* Proof. *)
  (* Abort. *)

End Array_Proofs.

End ArrayVerification.
