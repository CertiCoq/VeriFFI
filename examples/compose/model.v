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

Definition Rep_fun {A B : Type} `{Rep A} `{Rep B} : Rep (A -> B).
Admitted.

Module Compose_Proofs.
  Definition compose_ep : extern_properties :=
    {| type_desc :=
       @TYPEPARAM (fun A Rep_A =>
         @TYPEPARAM (fun B Rep_B =>
           @TYPEPARAM (fun C Rep_C =>
             @TRANSPARENT (B -> C) Rep_fun (Some (fun g =>
               @TRANSPARENT (A -> B) Rep_fun (Some (fun f =>
                 @TRANSPARENT (A -> C) Rep_fun None)))))))
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