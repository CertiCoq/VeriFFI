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

Module Compose_Proofs.
  Check prim_in_graph.
  Check C.compose.
  Definition compose_ep : fn_desc :=
    {| type_desc :=
       @TYPEPARAM _ (fun A R_A =>
         @TYPEPARAM _ (fun B R_B =>
           @TYPEPARAM _ (fun C R_C =>
             @ARG _ (B -> C) (@transparent _ (@InGraph_fun _ _ (@prim_in_graph B R_B) (@prim_in_graph C R_C))) (fun g =>
               @ARG _ (A -> B) (@transparent _ (@InGraph_fun _ _ (@prim_in_graph A R_A) (@prim_in_graph B R_B))) (fun f =>
                 @RES _ (A -> C) (@transparent _ (@InGraph_fun _ _ (@prim_in_graph A R_A) (@prim_in_graph C R_C))))))))
     ; prim_fn := @C.compose
     ; model_fn := fun '(A; (_; (B; (_; (C; (_; (g; (f; tt)))))))) => @FM.compose A B C g f
     ; f_arity := 5
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
