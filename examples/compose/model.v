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
       @TYPEPARAM _ (fun A R_A =>
         @TYPEPARAM _ (fun B R_B =>
           @TYPEPARAM _ (fun C R_C =>
             @ARG _ (B -> C) (@OPAQUE _ _ (@InGraph_fun _ _ (prim_in_graph R_B) (prim_in_graph R_C)) _) (fun g =>
               @ARG _ (A -> B) (@OPAQUE _ _ (@InGraph_fun _ _ (prim_in_graph R_A) (prim_in_graph R_B)) _) (fun f =>
                 @RES _ (A -> C) (@OPAQUE _ _ (@InGraph_fun _ _ (prim_in_graph R_A) (prim_in_graph R_C)) _))))))
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
