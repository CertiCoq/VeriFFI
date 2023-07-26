Require Import ZArith.
Require Import Psatz.
Require Import String.
Open Scope string.

Require Import VeriFFI.library.isomorphism.
Require Import VeriFFI.library.meta.
Require Import VeriFFI.library.modelled.

Require Import VeriFFI.examples.compose.prog.

Module FM <: Compose.
  Definition compose {A B C} (g : B -> C) (f : A -> B) : A -> C :=
    fun x => g (f x).
End FM.

Definition InGraph_fun {A B : Type} `{InGraph A} `{InGraph B} : InGraph (A -> B).
Admitted.

Module Compose_Proofs.
  Definition compose_ep : extern_properties :=
    {| type_desc :=
       @TYPEPARAM (fun A InGraph_A =>
         @TYPEPARAM (fun B InGraph_B =>
           @TYPEPARAM (fun C InGraph_C =>
             @TRANSPARENT (B -> C) InGraph_fun (Some (fun g =>
               @TRANSPARENT (A -> B) InGraph_fun (Some (fun f =>
                 @TRANSPARENT (A -> C) InGraph_fun None)))))))
     ; prim_fn := @C.compose
     ; model_fn := @FM.compose
     ; c_name := "compose"
     |}.

  Axiom compose_properties : model_spec compose_ep.

(* commented out to reduce chatter in build
  Eval cbn in model_spec compose_ep.
*)
  Lemma compose_pf :
    forall {A B C} (g : B -> C) (f : A -> B) (x : A),
      C.compose g f x = FM.compose g f x.
  Proof.
    intros A B C g f x.
    props compose_properties.
    auto.
  Qed.

End Compose_Proofs.
