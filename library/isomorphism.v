Require Import Init.

Class Isomorphism (A B : Type) :=
  { from : A -> B
  ; to : B -> A
  ; from_to : forall (x : A), to (from x) = x
  ; to_from : forall (x : B), from (to x) = x
  }.

#[export] Instance Isomorphism_refl {A : Type} : Isomorphism A A.
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
