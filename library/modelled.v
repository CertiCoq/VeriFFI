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
  unfold id, eq_rect in *;
  clear P.

Class Modelled (prim_type model_type : Type) :=
  { model_to_prim : model_type -> prim_type
  ; prim_to_model : prim_type -> model_type
  ; prim_to_model_to_prim : forall (x : prim_type), model_to_prim (prim_to_model x) = x
  ; model_to_prim_to_model : forall (x : model_type), prim_to_model (model_to_prim x) = x
  }.

Instance Modelled_same {A : Type} : Modelled A A.
  refine (@Build_Modelled A A id id _ _); auto.
Defined.

Require Import Coq.Logic.FunctionalExtensionality.

Instance Modelled_fn {A A' B B' : Type} :
  Modelled A A' -> Modelled B B' -> Modelled (A -> B) (A' -> B').
Proof.
  intros ma mb.
  pose (f1 (f : A -> B) := fun a' : A' => prim_to_model (f (model_to_prim a'))).
  pose (f2 (f : A' -> B') := fun a : A => model_to_prim (f (prim_to_model a))).
  refine (@Build_Modelled (A -> B) (A' -> B') f2 f1 _ _);
  intros; unfold f1, f2; apply functional_extensionality;
    intro; rewrite ?prim_to_model_to_prim, ?model_to_prim_to_model; auto.
Defined.

Instance Modelled_dep_fn {A A' : Type} {B : A -> Type} {B' : A' -> Type} :
  Modelled A A' ->
  (forall (a : A) (a' : A'), Modelled A A' -> Modelled (B a) (B' a')) ->
  Modelled (forall (a : A), B a) (forall (a' : A'), B' a').
Proof.
  intros ma f.
  econstructor.
  Unshelve.
  3: {intros g a; exact (model_to_prim (g (prim_to_model a))).}
  3: {intros g a'; exact (prim_to_model (g (model_to_prim a'))).}
  * intros x.
    apply (functional_extensionality_dep _ x).
    intro a.
    rewrite !prim_to_model_to_prim.
    auto.
  * intros x.
    apply (functional_extensionality_dep _ x).
    intro a'.
    rewrite !model_to_prim_to_model.
    auto.
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

Module Type Element.
  Axiom t : Type.
End Element.

Module Type Array (E : Element).
  Axiom ST : Type -> Type -> Type.
  Axiom pure : forall {S A}, A -> ST S A.
  Axiom bind : forall {S A B}, ST S A -> (A -> ST S B) -> ST S B.
  Axiom runST : forall {A}, (forall S, ST S A) -> A.
  Axiom array : Type -> Type.
  Axiom new : forall {S}, nat -> E.t -> ST S (array S).
  Axiom set : forall {S}, array S -> nat -> E.t -> ST S unit.
  Axiom get : forall {S}, array S -> nat -> ST S (option E.t).
  Axiom delete : forall {S}, array S -> ST S unit.
End Array.

Module FM (E : Element) <: Array E.
  Definition array (S : Type) : Type := nat.
  Definition arrays := list (list E.t).
  Definition ST (S : Type) (A : Type) : Type := arrays -> A * arrays.
  Definition pure {S A} (a : A) : ST S A := fun s => (a, s).
  Definition bind {S A B} (m : ST S A) (f : A -> ST S B) : ST S B :=
    fun s => f (fst (m s)) (snd (m s)).
    (* fun s => let '(a, s') := m s in f a s'. *)
  Definition runST {A} (f : forall S, ST S A) : A :=
    fst (f unit nil).
  Definition new {S} (len : nat) (fill : E.t) : ST S (array S) :=
    let xs := repeat fill len in
    fun s => (length s, s ++ [xs]).

  (* Look at canon.replace_nth, invariants.replace_nth, sepalg_list.replace for lemmas *)
  Definition set {S} (arr : array S) (index : nat) (elt : E.t) : ST S unit :=
    let fix replace (index : nat) (l : list E.t) : list E.t :=
      match index, l with
      | _, nil => nil
      | O, cons x xs => cons elt xs
      | S n, cons x xs => cons x (replace n xs)
      end in
    let fix aux (s : arrays) (arr : array S) : arrays :=
      match arr, s with
      | _, nil => nil
      | O, cons x xs => cons (replace index x) xs
      | S n, cons x xs => cons x (aux xs n)
      end
    in fun s => (tt, aux s arr).

  Definition get {S} (arr : array S) (index : nat) : ST S (option E.t) :=
    fun s : arrays =>
      match nth_error s arr with
      | None => (None, s)
      | Some l => (nth_error l index, s)
      end.

  Definition delete {S} (arr : array S) : ST S unit :=
    let fix aux (s : arrays) (arr : array S) : arrays :=
      match arr, s with
      | _, nil => nil
      | O, cons x xs => cons nil xs
      | S n, cons x xs => cons x (aux xs n)
      end
    in fun s => (tt, aux s arr).
End FM.

Module C (E : Element) : Array E.
  Axiom ST : Type -> Type -> Type.
  Axiom pure : forall {S A}, A -> ST S A.
  Axiom bind : forall {S A B}, ST S A -> (A -> ST S B) -> ST S B.
  Axiom runST : forall {A}, (forall S, ST S A) -> A.
  Axiom array : Type -> Type.
  Axiom new : forall {S}, nat -> E.t -> ST S (array S).
  Axiom set : forall {S}, array S -> nat -> E.t -> ST S unit.
  Axiom get : forall {S}, array S -> nat -> ST S (option E.t).
  Axiom delete : forall {S}, array S -> ST S unit.
End C.

Module Array_Proofs.
  Module E.
    Definition t := bool.
  End E.
  Module FM := FM E.
  Module C := C E.

  Definition Rep_nat : Rep nat. Admitted.
  Definition Rep_t : Rep E.t. Admitted.
  Axiom Modelled_array : forall {S}, Modelled (C.array S) (FM.array S).
  Axiom Modelled_ST : forall {S A A'}, Modelled A A' -> Modelled (C.ST S A) (FM.ST S A').

  Definition pure_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @TRANSPARENT A Rep_A (Some (fun arr =>
            @OPAQUE (C.ST S A) (FM.ST S A) (Modelled_ST _) None))))
     ; prim_fn := @C.pure
     ; model_fn := @FM.pure
     ; c_name := "st_pure"
     |}.

  Definition bind_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @TYPEPARAM (fun (B : Type) `{Rep_B : Rep B} =>
            @OPAQUE (C.ST S A) (FM.ST S A) (Modelled_ST _) (Some (fun m =>
              @OPAQUE (A -> C.ST S B) (A -> FM.ST S B) (Modelled_fn _ (Modelled_ST _)) (Some (fun f =>
                @OPAQUE (C.ST S B) (FM.ST S B) (Modelled_ST _) None)))))))
     ; prim_fn := @C.bind
     ; model_fn := @FM.bind
     ; c_name := "st_bind"
     |}.

  Definition runST_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @OPAQUE (forall (S : Type), C.ST S A) (forall (S : Type), FM.ST S A)
                  (@Modelled_dep_fn Type Type (fun S => C.ST S A) (fun S => FM.ST S A) _
                                    (fun s s' m => @Modelled_ST _ A A _)) (Some (fun f =>
            @TRANSPARENT A Rep_A None)))
     ; prim_fn := @C.runST
     ; model_fn := @FM.runST
     ; c_name := "st_runST"
     |}.

  Definition new_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @TRANSPARENT nat Rep_nat (Some (fun n =>
          @TRANSPARENT E.t Rep_t (Some (fun a =>
            @OPAQUE (C.ST S (C.array S)) (FM.ST S (FM.array S))
                    (Modelled_ST Modelled_array) None)))))
     ; prim_fn := @C.new
     ; model_fn := @FM.new
     ; c_name := "array_new"
     |}.

  Definition set_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @OPAQUE (C.array S) (FM.array S) Modelled_array (Some (fun arr =>
          @TRANSPARENT nat Rep_nat (Some (fun n =>
            @TRANSPARENT E.t Rep_t (Some (fun a =>
              @OPAQUE (C.ST S unit) (FM.ST S unit) (Modelled_ST _) None)))))))
     ; prim_fn := @C.set
     ; model_fn := @FM.set
     ; c_name := "array_set"
     |}.

  Definition get_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @OPAQUE (C.array S) (FM.array S) Modelled_array (Some (fun arr =>
          @TRANSPARENT nat Rep_nat (Some (fun n =>
            @OPAQUE (C.ST S (option E.t)) (FM.ST S (option E.t)) (Modelled_ST _) None)))))
     ; prim_fn := @C.get
     ; model_fn := @FM.get
     ; c_name := "array_get"
     |}.

  Definition delete_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @OPAQUE (C.array S) (FM.array S) Modelled_array (Some (fun arr =>
          @OPAQUE (C.ST S unit) (FM.ST S unit) (Modelled_ST _) None)))
     ; prim_fn := @C.delete
     ; model_fn := @FM.delete
     ; c_name := "array_delete"
     |}.

  Axiom pure_properties : model_spec pure_ep.
  Axiom bind_properties : model_spec bind_ep.
  Axiom runST_properties : model_spec runST_ep.
  Axiom new_properties : model_spec new_ep.
  Axiom set_properties : model_spec set_ep.
  Axiom get_properties : model_spec get_ep.
  Axiom delete_properties : model_spec delete_ep.

  Ltac prim_rewrites :=
    repeat eq_refl_match;
    rewrite ?prim_to_model_to_prim, ?model_to_prim_to_model.

  Lemma set_get :
    forall {S : Type} (n len : nat) (bound : n < len) (to_set to_fill : E.t),
      C.runST (fun _ => C.bind (C.new len to_fill) (fun arr => C.bind (C.set arr n to_set) (fun _ => C.get arr n))) =
      C.runST (fun _ => C.pure (Some to_set)).
  Proof.
    intros S n len bound to_set to_fill.
    props runST_properties.
    prim_rewrites.
    unfold FM.runST.

    props bind_properties.
    props pure_properties.
    props new_properties.
    unfold FM.bind, FM.pure.
    prim_rewrites.

    props bind_properties.
    props set_properties.
    unfold FM.bind.
    prim_rewrites.

    props get_properties.
    prim_rewrites.

    (* rest of the proof is just about the functional model *)
    Set Printing All.
    Check (@FM.new unit len to_fill).
    Check ((@model_to_prim (C.ST unit (C.array unit))
                      (FM.ST unit (FM.array unit))
                      (@Modelled_ST unit (C.array unit)
                         (FM.array unit) (@Modelled_array unit))
                      (@FM.new unit len to_fill))).
    Check ((@prim_to_model (C.ST unit (C.array unit))
                   (FM.ST unit (C.array unit))
                   (@Modelled_ST unit (C.array unit)
                      (C.array unit)
                      (@Modelled_same (C.array unit)))
                   (@model_to_prim (C.ST unit (C.array unit))
                      (FM.ST unit (FM.array unit))
                      (@Modelled_ST unit (C.array unit)
                         (FM.array unit) (@Modelled_array unit))
                      (@FM.new unit len to_fill))
                   (@nil (list E.t)))).
    Check (((@prim_to_model (C.array unit) (FM.array unit)
             (@Modelled_array unit)
             (@fst (C.array unit) FM.arrays
                (@prim_to_model (C.ST unit (C.array unit))
                   (FM.ST unit (C.array unit))
                   (@Modelled_ST unit (C.array unit)
                      (C.array unit)
                      (@Modelled_same (C.array unit)))
                   (@model_to_prim (C.ST unit (C.array unit))
                      (FM.ST unit (FM.array unit))
                      (@Modelled_ST unit (C.array unit)
                         (FM.array unit) (@Modelled_array unit))
                      (@FM.new unit len to_fill))
                   (@nil (list E.t))))))).

    rewrite ?prim_to_model_to_prim, ?model_to_prim_to_model.
    Check (@model_to_prim_to_model (C.ST unit (C.array unit)) (FM.ST unit (FM.array unit)) (@Modelled_ST unit (C.array unit) (FM.array unit) (@Modelled_array unit))).
    unfold FM.new.
    rewrite ?prim_to_model_to_prim, ?model_to_prim_to_model.

    unfold model_to_prim.

    assert (forall (x : FM.ST S nat), prim_to_model (model_to_prim x) = x).
    intros. prim_rewrites. auto.


    rewrite (H (fun s : FM.arrays => (length s, s ++ [repeat to_fill len]))).
    rewrite !model_to_prim_to_model.
    unfold FM.get, FM.set, FM.new.
    simpl.
    prim_rewrites.


  Qed.

End Array_Proofs.

End ArrayVerification.
