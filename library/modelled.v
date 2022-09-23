Require Import String.

Require Import ZArith.
Require Import Psatz.
Require Import List.
Import ListNotations.

Class Isomorphism (A B : Type) :=
  { from : A -> B
  ; to : B -> A
  ; from_to : forall (x : A), to (from x) = x
  ; to_from : forall (x : B), from (to x) = x
  }.

Instance Isomorphism_refl {A : Type} : Isomorphism A A.
Proof.
  refine {| from := id ; to := id ; from_to := _ ; to_from := _ |}; auto.
Defined.

Lemma Isomorphism_sym {A B : Type} : Isomorphism A B -> Isomorphism B A.
Proof.
  intro i.
  exact {| from := to
         ; to := from
         ; from_to := to_from
         ; to_from := from_to |}.
Defined.

Lemma Isomorphism_trans {A B C : Type} : Isomorphism A B -> Isomorphism B C -> Isomorphism A C.
Proof.
  intros [f1 t1 pf1 pt1] [f2 t2 pf2 pt2].
  refine {| from := fun x => f2 (f1 x)
          ; to := fun x => t1 (t2 x)
          ; from_to := _
          ; to_from := _ |};
  intro; [rewrite pf2, pf1 | rewrite pt1, pt2]; auto.
Defined.

Lemma from_sym : forall A B `(M : Isomorphism A B),
    @from A B M = @to B A (Isomorphism_sym M).
Proof.
  intros A B M; auto.
Defined.

Lemma to_sym : forall A B `(M : Isomorphism A B),
    @to A B M = @from B A (Isomorphism_sym M).
Proof.
  intros A B M; auto.
Defined.

Lemma from_trans : forall A B C `(M1 : Isomorphism A B) `(M2 : Isomorphism B C),
    forall (x : A), @from B C M2 (@from A B M1 x) = @from A C (Isomorphism_trans M1 M2) x .
Proof.
  intros A B C [f1 t1 pf1 pt1] [f2 t2 pf2 pt2] x; simpl; auto.
Defined.


Require Import Coq.Logic.FunctionalExtensionality.

Lemma Isomorphism_dep_fn {A A' : Type} {B : A -> Type} {B' : A' -> Type} :
  Isomorphism A A' ->
  (forall (a : A) (a' : A'), Isomorphism A A' -> Isomorphism (B a) (B' a')) ->
  Isomorphism (forall (a : A), B a) (forall (a' : A'), B' a').
Proof.
  intros.
  econstructor.
  instantiate (1 := ltac:(intros g a; exact (from (g (to a))))).
  instantiate (1 := ltac:(intros g a'; exact (to (g (from a'))))).
  all: intros; apply functional_extensionality_dep;
       intro; rewrite ?from_to, ?to_from; auto.
Defined.

Lemma Isomorphism_fn {A A' B B' : Type} :
  Isomorphism A A' -> Isomorphism B B' -> Isomorphism (A -> B) (A' -> B').
Proof.
  intros i1 i2.
  exact (@Isomorphism_dep_fn A A' (fun _ => B) (fun _ => B') i1 (fun _ _ _ => i2)).
Defined.

Lemma Isomorphism_pair {A A' B B' : Type} :
  Isomorphism A A' -> Isomorphism B B' -> Isomorphism (A * B) (A' * B').
Proof.
  intros [f1 t1 ft1 tf1] [f2 t2 ft2 tf2].
  econstructor.
  instantiate (1:= ltac:(intros [a b]; split; auto)).
  instantiate (1:= ltac:(intros [a b]; split; auto)).
  all: intros; intuition.
  rewrite ft1, ft2; auto.
  rewrite tf1, tf2; auto.
Defined.

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

Require Import VeriFFI.library.meta.

(* opaque and transparent *)
Inductive annotated : Type :=
| TYPEPARAM : (forall (A : Type) `{Rep A}, annotated) -> annotated
| OPAQUE : forall (prim_type model_type : Type)
                    `{Isomorphism prim_type model_type},
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
      | Some fp => forall (m : mt), to_model_fn_type (fp (@to pt mt M m))
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

  Lemma mod63_ok:
    forall z, (0 <= z mod (2^63) < 2^63)%Z.
  Proof.
    intro. apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
   Qed.

  Definition add (x y: t) : t :=
  let '(exist xz x_pf) := x in
  let '(exist yz y_pf) := y in
  let z := ((xz + yz) mod (2^63))%Z in
  exist _ z (mod63_ok _).

  Definition mul (x y: t) : t :=
  let '(exist xz x_pf) := x in
  let '(exist yz y_pf) := y in
  let z := ((xz * yz) mod (2^63))%Z in
  exist _ z (mod63_ok _).

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
  Axiom Isomorphism_t : Isomorphism C.t FM.t.

  Definition from_Z_ep : extern_properties :=
    {| type_desc :=
        @TRANSPARENT Z Rep_Z
           (Some (fun z => @OPAQUE _ _ Isomorphism_t None))
     ; prim_fn := C.from_Z
     ; model_fn := FM.from_Z
     ; c_name := "int63_from_Z"
     |}.

  Definition to_Z_ep : extern_properties :=
    {| type_desc :=
        @OPAQUE _ _ Isomorphism_t
           (Some (fun z => @TRANSPARENT Z Rep_Z None))
     ; prim_fn := C.to_Z
     ; model_fn := FM.to_Z
     ; c_name := "int63_to_Z"
     |}.

  Definition add_ep : extern_properties :=
    {| type_desc :=
          @OPAQUE _ _ Isomorphism_t
            (Some (fun i =>
              @OPAQUE _ _ Isomorphism_t
                (Some (fun i => @OPAQUE _ _ Isomorphism_t None))))
     ; prim_fn := C.add
     ; model_fn := FM.add
     ; c_name := "int63_add"
     |}.

  Definition mul_ep : extern_properties :=
    {| type_desc :=
          @OPAQUE _ _ Isomorphism_t
            (Some (fun i =>
              @OPAQUE _ _ Isomorphism_t
                (Some (fun i => @OPAQUE _ _ Isomorphism_t None))))
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

    Print model_spec.
    Print model_spec_aux.
    props from_Z_properties.
    props to_Z_properties.
    props add_properties.
    repeat eq_refl_match.
    rewrite !from_to, !to_from.
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
    rewrite !from_to, !to_from.
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
    rewrite !from_to, !to_from.
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
    rewrite !from_to, !to_from.
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

Module Type ArraySetup.
  Axiom t : Type.
  Axiom len: nat.
  Axiom init : t.
End ArraySetup.

Module Type Array (E : ArraySetup).
  Axiom state : Type.
  Definition M (A : Type) : Type := state -> A * state.
  Axiom pure : forall {A}, A -> M A.
  Axiom bind : forall {A B}, M A -> (A -> M B) -> M B.
  Axiom runM : forall {A}, M A -> A.
  Axiom set : nat -> E.t -> M unit.
  Axiom get : nat -> M (option E.t).
End Array.

(* Look at canon.replace_nth, invariants.replace_nth, sepalg_list.replace for lemmas *)
Module FM (E : ArraySetup) <: Array E.
  Definition state := list E.t.
  Definition M (A : Type) : Type := state -> A * state.
  Definition pure {A} (a : A) : M A := fun s => (a, s).
  Definition bind {A B} (m : M A) (f : A -> M B) : M B :=
    fun s => f (fst (m s)) (snd (m s)).
    (* fun s => let '(a, s') := m s in f a s'. *)
  Definition runM {A} (m : M A) : A :=
    fst (m (repeat E.init E.len)).

  Definition set (index : nat) (elt : E.t) : M unit :=
    fun s => (tt, canon.replace_nth index s elt).

  Definition get (index : nat) : M (option E.t) :=
    fun s => (nth_error s index, s).

End FM.

Module C (E : ArraySetup) : Array E.
  Axiom state : Type.
  Definition M (A : Type) : Type := state -> A * state.
  Axiom pure : forall {A}, A -> M A.
  Axiom bind : forall {A B}, M A -> (A -> M B) -> M B.
  Axiom runM : forall {A}, M A -> A.
  Axiom set : nat -> E.t -> M unit.
  Axiom get : nat -> M (option E.t).
End C.

Module Array_Proofs.
  Module E.
    Definition t := bool.
    Definition len := 5.
    Definition init := false.
  End E.
  Module FM := FM E.
  Module C := C E.

  Definition Rep_nat : Rep nat. Admitted.
  Definition Rep_t : Rep E.t. Admitted.

  Axiom Isomorphism_state : Isomorphism C.state FM.state.

  Definition Isomorphism_M
             {A A' : Type} (I : Isomorphism A A')
             : Isomorphism (C.M A) (FM.M A').
  Proof.
    eauto using Isomorphism_fn, Isomorphism_state, Isomorphism_pair.
  Qed.

  Definition pure_ep : extern_properties :=
    {| type_desc :=
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @TRANSPARENT A Rep_A (Some (fun arr =>
            @OPAQUE (C.M A) (FM.M A) (Isomorphism_M _) None)))
     ; prim_fn := @C.pure
     ; model_fn := @FM.pure
     ; c_name := "m_pure"
     |}.

  Definition bind_ep : extern_properties :=
    {| type_desc :=
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @TYPEPARAM (fun (B : Type) `{Rep_B : Rep B} =>
            @OPAQUE (C.M A) (FM.M A) (Isomorphism_M _) (Some (fun m =>
              @OPAQUE (A -> C.M B) (A -> FM.M B) (Isomorphism_fn _ (Isomorphism_M _)) (Some (fun f =>
                @OPAQUE (C.M B) (FM.M B) (Isomorphism_M _) None))))))
     ; prim_fn := @C.bind
     ; model_fn := @FM.bind
     ; c_name := "m_bind"
     |}.

  Definition runM_ep : extern_properties :=
    {| type_desc :=
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @OPAQUE (C.M A) (FM.M A) (Isomorphism_M _)
                  (Some (fun f => @TRANSPARENT A Rep_A None)))
     ; prim_fn := @C.runM
     ; model_fn := @FM.runM
     ; c_name := "m_runM"
     |}.

  Definition set_ep : extern_properties :=
    {| type_desc :=
        @TRANSPARENT nat Rep_nat (Some (fun n =>
          @TRANSPARENT E.t Rep_t (Some (fun a =>
            @OPAQUE (C.M unit) (FM.M unit) (Isomorphism_M _) None))))
     ; prim_fn := @C.set
     ; model_fn := @FM.set
     ; c_name := "array_set"
     |}.

  Definition get_ep : extern_properties :=
    {| type_desc :=
        @TRANSPARENT nat Rep_nat (Some (fun n =>
          @OPAQUE (C.M (option E.t)) (FM.M (option E.t)) (Isomorphism_M _) None))
     ; prim_fn := @C.get
     ; model_fn := @FM.get
     ; c_name := "array_get"
     |}.

  Axiom pure_properties : model_spec pure_ep.
  Axiom bind_properties : model_spec bind_ep.
  Axiom runM_properties : model_spec runM_ep.
  Axiom set_properties : model_spec set_ep.
  Axiom get_properties : model_spec get_ep.

  Ltac prim_rewrites :=
    repeat eq_refl_match;
    rewrite ?from_to, ?to_from.

  Arguments from A B {_}.
  Arguments to A B {_}.

  Lemma set_get :
    forall (n : nat) (bound : n < E.len) (to_set : E.t),
      (C.runM (C.bind (C.set n to_set) (fun _ => C.get n)))
        =
      (C.runM (C.pure (Some to_set))).
  Proof.
    intros n bound to_set.

    props runM_properties.
    prim_rewrites.
    unfold FM.runM.

    props bind_properties.
    props pure_properties.
    unfold FM.bind, FM.pure.
    prim_rewrites.

    props set_properties.
    props get_properties.
    prim_rewrites.

    unfold fst at 2.

    (* unfold FM.get, FM.set in *. *)
    eapply canon.nth_error_replace_nth.
    apply nth_error_repeat.
    lia.
  Qed.

End Array_Proofs.

End ArrayVerification.
