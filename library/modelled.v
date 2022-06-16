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

(* Check f_equal. *)

(* Lemma Isomorphism_f_equal {A B : Type} (F : Type -> Type) : *)
(*   Isomorphism A B -> Isomorphism (F A) (F B). *)
(* Proof. *)
(*   intros [f t ft tf]. *)
(*   refine {| from := fun (a : F A) => _; to := _; from_to := _; to_from := _ |}. *)
(*   econstructor. *)
(*   instantiate (1 := ltac:()). *)



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

  Require Import JMeq.
  (* Axiom P_pf : forall (T : Type) (P : (T -> FM.t) -> Prop) , *)
  (*     (C.t = FM.t -> JMeq C.add FM.add -> JMeq C.mul FM.mul -> JMeq C.from_Z FM.from_Z -> JMeq C.to_Z FM.to_Z -> *)
  (*      forall x x', (forall i, JMeq (x i) (x' i)) -> (P x = P x')). *)


  (* Axiom P_pf : forall (T : Type) (P : (T -> C.t) -> Prop) (P' : (T -> FM.t) -> Prop), *)
  (*     (C.t = FM.t -> JMeq C.add FM.add -> JMeq C.mul FM.mul -> JMeq C.from_Z FM.from_Z -> JMeq C.to_Z FM.to_Z -> *)
  (*      forall x x', (forall i, JMeq (x i) (x' i)) -> (P x = P' x')). *)


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

  let P := fresh in
  pose proof from_Z_properties as P;
  hnf in P;
  simpl in P;
  rewrite !P;
  unfold id, eq_rect in *.

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

Module Type Element.
  Axiom t : Type.
End Element.

Module Type Array (E : Element).
  Axiom arrays : Type.
  Definition ST (S : Type) (A : Type) : Type := arrays -> A * arrays.
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
  Axiom arrays : Type.
  Definition ST (S : Type) (A : Type) : Type := arrays -> A * arrays.
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

  Variable Isomorphism_array : forall {S}, Isomorphism (C.array S) (FM.array S).
  Variable Isomorphism_arrays : Isomorphism (C.arrays) (FM.arrays).

  Definition Isomorphism_ST
             {S A A' : Type} (I : Isomorphism A A') : Isomorphism (C.ST S A) (FM.ST S A').
    destruct I as [f t pf pt].
    destruct (@Isomorphism_array S) as [f' t' pf' pt'].
    unfold FM.ST, C.ST.
    apply Isomorphism_fn.
    apply Isomorphism_arrays.
    Admitted.





  (* Axiom Isomorphism_ST : forall {S A A'}, Isomorphism A A' -> Isomorphism (C.ST S A) (FM.ST S A'). *)
  Axiom Isomorphism_ST_inj : forall {S A A'}, Isomorphism (C.ST S A) (FM.ST S A') -> Isomorphism A A'.

  Definition pure_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @TRANSPARENT A Rep_A (Some (fun arr =>
            @OPAQUE (C.ST S A) (FM.ST S A) (Isomorphism_ST _) None))))
     ; prim_fn := @C.pure
     ; model_fn := @FM.pure
     ; c_name := "st_pure"
     |}.

  Definition bind_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @TYPEPARAM (fun (B : Type) `{Rep_B : Rep B} =>
            @OPAQUE (C.ST S A) (FM.ST S A) (Isomorphism_ST _) (Some (fun m =>
              @OPAQUE (A -> C.ST S B) (A -> FM.ST S B) (Isomorphism_fn _ (Isomorphism_ST _)) (Some (fun f =>
                @OPAQUE (C.ST S B) (FM.ST S B) (Isomorphism_ST _) None)))))))
     ; prim_fn := @C.bind
     ; model_fn := @FM.bind
     ; c_name := "st_bind"
     |}.

  Definition runST_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @OPAQUE (forall (S : Type), C.ST S A) (forall (S : Type), FM.ST S A)
                  (@Isomorphism_dep_fn Type Type (fun S => C.ST S A) (fun S => FM.ST S A) _
                                    (fun s s' m => @Isomorphism_ST _ A A _)) (Some (fun f =>
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
                    (Isomorphism_ST Isomorphism_array) None)))))
     ; prim_fn := @C.new
     ; model_fn := @FM.new
     ; c_name := "array_new"
     |}.

  Definition set_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @OPAQUE (C.array S) (FM.array S) Isomorphism_array (Some (fun arr =>
          @TRANSPARENT nat Rep_nat (Some (fun n =>
            @TRANSPARENT E.t Rep_t (Some (fun a =>
              @OPAQUE (C.ST S unit) (FM.ST S unit) (Isomorphism_ST _) None)))))))
     ; prim_fn := @C.set
     ; model_fn := @FM.set
     ; c_name := "array_set"
     |}.

  Definition get_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @OPAQUE (C.array S) (FM.array S) Isomorphism_array (Some (fun arr =>
          @TRANSPARENT nat Rep_nat (Some (fun n =>
            @OPAQUE (C.ST S (option E.t)) (FM.ST S (option E.t)) (Isomorphism_ST _) None)))))
     ; prim_fn := @C.get
     ; model_fn := @FM.get
     ; c_name := "array_get"
     |}.

  Definition delete_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @OPAQUE (C.array S) (FM.array S) Isomorphism_array (Some (fun arr =>
          @OPAQUE (C.ST S unit) (FM.ST S unit) (Isomorphism_ST _) None)))
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
    rewrite ?from_to, ?to_from.

  (* Definition actions_equiv {S A : Type} (x y : FM.ST S A) : Prop := *)
  (*   forall s, x s = y s. *)
  (* Set Printing All. *)
  (* Print actions_equiv. *)

  (* Axiom runST_equiv : forall A (x y : forall (S : Type), FM.ST S A), *)
  (*     x = y -> *)
  (*     FM.runST x = FM.runST y. *)


  Arguments from A B {_}.
  Arguments to A B {_}.

  Axiom array_eq : forall S, C.array S = FM.array S.
  (* Lemma from_eq : *)
  (*   forall A B x, *)
  (*     A = B -> *)
  (*     from A B x = x. *)

  Lemma Isomorphism_FMST {A B : Type} : Isomorphism A B -> Isomorphism (FM.ST unit A) (FM.ST unit B).
  Proof.
    intros [f t ft tf].
    econstructor.
    Unshelve.
    3: { intros a x. specialize (a x).
         exact (f (fst a), (snd a)).}
    3: { intros a x. specialize (a x).
         exact (t (fst a), (snd a)).}
    simpl. intros. apply functional_extensionality. intros. rewrite ?ft, ?tf. destruct (x x0). auto.
    simpl. intros. apply functional_extensionality. intros. rewrite ?ft, ?tf. destruct (x x0). auto.
  Defined.


  (* Lemma from_eq : *)
  (*   forall A B x, *)
  (*     A = B -> *)
  (*     forall (I1 : Isomorphism A B) (I2 : Isomorphism (FM.ST unit B) (FM.ST unit A)), *)
  (*       I2 = Isomorphism_sym (Isomorphism_FMST I1) -> *)
  (*   (@from A B I1 (fst (@from (FM.ST unit B) (FM.ST unit A) I2 x []))) = fst (x []). *)
  (* Proof. *)
  (*   intros A B X eq I1 I2 Ieq. *)
  (*   subst. *)
  (* Admitted. *)
  (*   unfold fst. *)
  (*   unfold fst. *)
  (* Abort. *)

  Require Import JMeq.

  Require Import Coq.Logic.FunctionalExtensionality.
  Require Import Coq.Logic.JMeq.

  Theorem jmeq_funext
    A (P : A -> Type) (Q : A -> Type)
    (f : forall a, P a)(g : forall a, Q a)
    (h : forall a, JMeq (f a) (g a)) : JMeq f g.
  Proof.
    assert (pq_eq : P = Q).
      apply functional_extensionality.
      exact (fun a => match (h a) with JMeq_refl => eq_refl end).
    induction pq_eq.
    assert (fg_eq : f = g).
      apply functional_extensionality_dep.
      exact (fun a => JMeq_rect (fun ga => f a = ga) eq_refl (h a)).
    induction fg_eq.
    exact JMeq_refl.
  Qed.


  Axiom runST_pf : forall {A : Type}
                          {f : forall (S : Type), C.ST S A}
                          {f' : forall (S : Type), FM.ST S A},
   (forall (eq_array : forall {S}, (C.array S) = (FM.array S))
           (eq_arrays : C.arrays = FM.arrays), JMeq f f') ->
   (C.runST f) = (FM.runST f').

  Lemma set_get :
    forall {S : Type} (n len : nat) (bound : n < len) (to_set to_fill : E.t),
      (C.runST (fun _ => C.bind (C.new len to_fill) (fun arr => C.bind (C.set arr n to_set) (fun _ => C.get arr n))))
        =
      (C.runST (fun _ => C.pure (Some to_set))).
  Proof.

    (* Set Printing Implicit. *)
    (* Unset Printing Notations. *)


    intros S n len bound to_set to_fill.

    erewrite runST_pf.
    instantiate (1 := fun _ => FM.bind (FM.new len to_fill) (fun arr => FM.bind (FM.set arr n to_set) (fun _ => FM.get arr n))).
    erewrite runST_pf.
    instantiate (1 := (fun _ => FM.pure (Some to_set))).


    admit.


    intros array_eq arrays_eq.
    apply jmeq_funext.
    intro A.
    admit.

    intros array_eq arrays_eq.
    apply jmeq_funext.
    intro A.
    admit.










    props runST_properties.
    prim_rewrites.
    unfold FM.runST.

    props bind_properties.
    props pure_properties.
    props new_properties.
    unfold FM.bind, FM.pure.
    prim_rewrites.

    props bind_properties.
    unfold FM.bind.
    prim_rewrites.

    props set_properties.
    prim_rewrites.

    props get_properties.
    prim_rewrites.

    unfold fst at 4.

    rewrite !to_sym.
    rewrite !from_trans.
    rewrite from_eq.
    3: {
      Set Printing All.
      Check (@Isomorphism_ST unit (C.array unit) (C.array unit) (@Isomorphism_refl (C.array unit))).
      unfold Isomorphism_sym.
      simpl.
      Set Printing All.
      Check (@Isomorphism_ST unit (C.array unit) (C.array unit) (@Isomorphism_refl (C.array unit))).
      Check (@Isomorphism_refl (FM.ST unit (FM.array unit))).
      replace (@Isomorphism_ST unit (C.array unit) (C.array unit) (@Isomorphism_refl (C.array unit)))
         with (@Isomorphism_refl (FM.ST unit (FM.array unit))).

    }



    Set Printing All.

    (* rewrite array_eq. *)

    (* Set Printing Implicit. *)

    unfold FM.new, FM.set, FM.get.
    unfold repeat.

    simpl.
    all: try auto.


    rewrite !to_sym.
    rewrite !from_trans.



    Unset Printing Implicit.


    (* rest of the proof is just about the functional model *)
    Set Printing All.
    Check (@FM.new unit len to_fill).
    rewrite ?from_to, ?to_from.
    unfold FM.new.
    rewrite ?from_to, ?to_from.

    unfold from.

    assert (forall (x : FM.ST S nat), to (from x) = x).
    intros. prim_rewrites. auto.


    rewrite (H (fun s : FM.arrays => (length s, s ++ [repeat to_fill len]))).
    rewrite !to_from.
    unfold FM.get, FM.set, FM.new.
    simpl.
    prim_rewrites.


  Qed.

End Array_Proofs.

End ArrayVerification.
Require Import String.

Require Import ZArith.
Require Import Psatz.
Require Import List.
Import ListNotations.


Require Import Coq.Logic.FinFun.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Setoid.


Inductive P {A : Type} : A -> Prop :=
| MkP : forall a, P a.

Class Isomorphism (A B : Type) : Type :=
  { from : A -> B
  ; to : B -> A
  ; from_to : forall (x : A), to (from x) = x
  ; to_from : forall (x : B), from (to x) = x
  }.

(* Require Import Coq.Logic.FinFun. *)
(* Require Import Coq.Relations.Relation_Definitions. *)
(* Require Import Coq.Relations.Relation_Operators. *)
(* Require Import Coq.Program.Basics. *)
(* Require Import Coq.Program.Combinators. *)
(* Require Import Setoid. *)

Instance Isomorphism_refl {A : Type} : Isomorphism A A.
Proof.
  eapply {| from := id ; to := id ; from_to := ltac:(auto) ; to_from := ltac:(auto) |}.
Defined.

Lemma Isomorphism_sym {A B : Type} `(I : Isomorphism A B) : Isomorphism B A.
Proof.
  destruct I as [f t ft tf].
  eapply {| from := t ; to := f ; from_to := tf ; to_from := ft |}.
Defined.

Lemma Isomorphism_trans {A B C : Type}
      `(I1 : Isomorphism A B)
      `(I2 : Isomorphism B C) : Isomorphism A C.
Proof.
  destruct I1 as [f1 t1 ft1 tf1].
  destruct I2 as [f2 t2 ft2 tf2].
  eapply {| from := fun x => f2 (f1 x)
          ; to := fun x => t1 (t2 x)
          ; from_to := _
          ; to_from := _|}.

  Unshelve.
  intros; simpl; rewrite ft2, ft1; auto.
  intros; simpl; rewrite tf1, tf2; auto.
Defined.

Lemma from_sym : forall A B `(M : Isomorphism A B),
    @from A B M = @to B A (Isomorphism_sym M).
Proof.
  intros A B M; destruct M; auto.
Defined.

Lemma to_sym : forall A B `(M : Isomorphism A B),
    @to A B M = @from B A (Isomorphism_sym M).
Proof.
  intros A B M; destruct M; auto.
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

Check f_equal.

(* Lemma Isomorphism_f_equal {A B : Type} (F : Type -> Type) : *)
(*   Isomorphism A B -> Isomorphism (F A) (F B). *)
(* Proof. *)
(*   intros [f t ft tf]. *)
(*   refine {| from := fun (a : F A) => _; to := _; from_to := _; to_from := _ |}. *)
(*   econstructor. *)
(*   instantiate (1 := ltac:()). *)



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
  Axiom Isomorphism_array : forall {S}, Isomorphism (C.array S) (FM.array S).
  Axiom Isomorphism_ST : forall {S A A'}, Isomorphism A A' -> Isomorphism (C.ST S A) (FM.ST S A').

  Definition pure_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @TRANSPARENT A Rep_A (Some (fun arr =>
            @OPAQUE (C.ST S A) (FM.ST S A) (Isomorphism_ST _) None))))
     ; prim_fn := @C.pure
     ; model_fn := @FM.pure
     ; c_name := "st_pure"
     |}.

  Definition bind_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @TYPEPARAM (fun (B : Type) `{Rep_B : Rep B} =>
            @OPAQUE (C.ST S A) (FM.ST S A) (Isomorphism_ST _) (Some (fun m =>
              @OPAQUE (A -> C.ST S B) (A -> FM.ST S B) (Isomorphism_fn _ (Isomorphism_ST _)) (Some (fun f =>
                @OPAQUE (C.ST S B) (FM.ST S B) (Isomorphism_ST _) None)))))))
     ; prim_fn := @C.bind
     ; model_fn := @FM.bind
     ; c_name := "st_bind"
     |}.

  Definition runST_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @OPAQUE (forall (S : Type), C.ST S A) (forall (S : Type), FM.ST S A)
                  (@Isomorphism_dep_fn Type Type (fun S => C.ST S A) (fun S => FM.ST S A) _
                                    (fun s s' m => @Isomorphism_ST _ A A _)) (Some (fun f =>
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
                    (Isomorphism_ST Isomorphism_array) None)))))
     ; prim_fn := @C.new
     ; model_fn := @FM.new
     ; c_name := "array_new"
     |}.

  Definition set_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @OPAQUE (C.array S) (FM.array S) Isomorphism_array (Some (fun arr =>
          @TRANSPARENT nat Rep_nat (Some (fun n =>
            @TRANSPARENT E.t Rep_t (Some (fun a =>
              @OPAQUE (C.ST S unit) (FM.ST S unit) (Isomorphism_ST _) None)))))))
     ; prim_fn := @C.set
     ; model_fn := @FM.set
     ; c_name := "array_set"
     |}.

  Definition get_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @OPAQUE (C.array S) (FM.array S) Isomorphism_array (Some (fun arr =>
          @TRANSPARENT nat Rep_nat (Some (fun n =>
            @OPAQUE (C.ST S (option E.t)) (FM.ST S (option E.t)) (Isomorphism_ST _) None)))))
     ; prim_fn := @C.get
     ; model_fn := @FM.get
     ; c_name := "array_get"
     |}.

  Definition delete_ep : extern_properties :=
    {| type_desc :=
      @TYPEPARAM (fun (S : Type) `{Rep_S : Rep S} =>
        @OPAQUE (C.array S) (FM.array S) Isomorphism_array (Some (fun arr =>
          @OPAQUE (C.ST S unit) (FM.ST S unit) (Isomorphism_ST _) None)))
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
    rewrite ?from_to, ?to_from.

  (* Definition actions_equiv {S A : Type} (x y : FM.ST S A) : Prop := *)
  (*   forall s, x s = y s. *)
  (* Set Printing All. *)
  (* Print actions_equiv. *)

  (* Axiom runST_equiv : forall A (x y : forall (S : Type), FM.ST S A), *)
  (*     x = y -> *)
  (*     FM.runST x = FM.runST y. *)


  Arguments from A B {_}.
  Arguments to A B {_}.

  Axiom array_eq : forall S, C.array S = FM.array S.
  (* Lemma from_eq : *)
  (*   forall A B x, *)
  (*     A = B -> *)
  (*     from A B x = x. *)

  Lemma Isomorphism_FMST {A B : Type} : Isomorphism A B -> Isomorphism (FM.ST unit A) (FM.ST unit B).
  Proof.
    intros [f t ft tf].
    econstructor.
    Unshelve.
    3: { intros a x. specialize (a x).
         exact (f (fst a), (snd a)).}
    3: { intros a x. specialize (a x).
         exact (t (fst a), (snd a)).}
    simpl. intros. apply functional_extensionality. intros. rewrite ?ft, ?tf. destruct (x x0). auto.
    simpl. intros. apply functional_extensionality. intros. rewrite ?ft, ?tf. destruct (x x0). auto.
  Defined.

  Lemma from_eq :
    forall A B x,
      A = B ->
      forall (I1 : Isomorphism A B) (I2 : Isomorphism (FM.ST unit B) (FM.ST unit A)),
        I2 = Isomorphism_sym (Isomorphism_FMST I1) ->
    (@from A B I1 (fst (@from (FM.ST unit B) (FM.ST unit A) I2 x []))) = fst (x []).
  Proof.
    intros A B X eq I1 I2 Ieq.
    subst.
  Admitted.
  (*   unfold fst. *)
  (*   unfold fst. *)
  (* Abort. *)

  Lemma set_get :
    forall {S : Type} (n len : nat) (bound : n < len) (to_set to_fill : E.t),
      (C.runST (fun _ => C.bind (C.new len to_fill) (fun arr => C.bind (C.set arr n to_set) (fun _ => C.get arr n))))
        =
      (C.runST (fun _ => C.pure (Some to_set))).
  Proof.

    (* Set Printing Implicit. *)
    (* Unset Printing Notations. *)


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
    unfold FM.bind.
    prim_rewrites.

    props set_properties.
    prim_rewrites.

    props get_properties.
    prim_rewrites.

    unfold fst at 4.

    rewrite !to_sym.
    rewrite !from_trans.

    rewrite from_eq.
    rewrite !from_sym.
    3: {
      unfold Isomorphism_sym.
      simpl.
      Set Printing All.
      Check (@Isomorphism_ST unit (C.array unit) (C.array unit) (@Isomorphism_refl (C.array unit))).
      Check (@Isomorphism_refl (FM.ST unit (FM.array unit))).
      replace (@Isomorphism_ST unit (C.array unit) (C.array unit) (@Isomorphism_refl (C.array unit)))
         with (@Isomorphism_refl (FM.ST unit (FM.array unit))).

    }



    Set Printing All.

    (* rewrite array_eq. *)

    (* Set Printing Implicit. *)

    unfold FM.new, FM.set, FM.get.
    unfold repeat.

    simpl.
    all: try auto.


    rewrite !to_sym.
    rewrite !from_trans.



    Unset Printing Implicit.


    (* rest of the proof is just about the functional model *)
    Set Printing All.
    Check (@FM.new unit len to_fill).
    rewrite ?from_to, ?to_from.
    unfold FM.new.
    rewrite ?from_to, ?to_from.

    unfold from.

    assert (forall (x : FM.ST S nat), to (from x) = x).
    intros. prim_rewrites. auto.


    rewrite (H (fun s : FM.arrays => (length s, s ++ [repeat to_fill len]))).
    rewrite !to_from.
    unfold FM.get, FM.set, FM.new.
    simpl.
    prim_rewrites.


  Qed.

End Array_Proofs.

End ArrayVerification.
