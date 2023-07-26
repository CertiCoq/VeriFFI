Require Import ZArith.
Require Import Psatz.
Require Import List.
Require Import String.
Open Scope string.

Require Import VeriFFI.generator.Rep.
Obligation Tactic := gen.
MetaCoq Run (gen_for nat).

Require Import VeriFFI.library.meta.
Require Import VeriFFI.library.modelled.
Require Import VeriFFI.library.isomorphism.

Require Import VeriFFI.examples.array.prog.

Variable InGraph_elt : InGraph elt.

(* Look at canon.replace_nth, invariants.replace_nth, sepalg_list.replace for lemmas *)
Module FM <: Array.
  Definition state : Type :=
    (list elt * elt). (* the internal list and the default element *)
  Definition M (A : Type) : Type := state -> A * state.
  Definition pure {A} (a : A) : M A := fun s => (a, s).
  Definition bind {A B} (m : M A) (f : A -> M B) : M B :=
    fun s => f (fst (m s)) (snd (m s)).
    (* fun s => let '(a, s') := m s in f a s'. *)
  Definition runM {A} (len : nat) (init: elt) (m : M A) : A :=
    fst (m (repeat init len, init)).

  Definition set (index : nat) (x : elt) : M unit :=
    fun '(l, init) => (tt, (VST.veric.invariants.replace_nth index l x, init)).

  Definition get (index : nat) : M elt :=
    fun '(l, init) => (nth index l init, (l, init)).
End FM.

Module Array_Proofs.
  (* Axiom Isomorphism_state : Isomorphism C.state FM.state. *)
  Axiom Isomorphism_M : forall {A A' : Type} (I : Isomorphism A A'),
                        Isomorphism (C.M A) (FM.M A').

  (*
  Definition Isomorphism_M
             {A A' : Type} (I : Isomorphism A A')
             : Isomorphism (C.M A) (FM.M A').
  Proof.
    eauto using Isomorphism_fn, Isomorphism_state, Isomorphism_pair.
  Qed.
  *)

  Definition pure_ep : extern_properties :=
    {| type_desc :=
        @TYPEPARAM (fun (A : Type) `{InGraph_A : InGraph A} =>
          @TRANSPARENT A InGraph_A (Some (fun arr =>
            @OPAQUE (C.M A) (FM.M A) (Isomorphism_M _) None)))
     ; prim_fn := @C.pure
     ; model_fn := @FM.pure
     ; c_name := "m_pure"
     |}.

  Definition bind_ep : extern_properties :=
    {| type_desc :=
        @TYPEPARAM (fun (A : Type) `{InGraph_A : InGraph A} =>
          @TYPEPARAM (fun (B : Type) `{InGraph_B : InGraph B} =>
            @OPAQUE (C.M A) (FM.M A) (Isomorphism_M _) (Some (fun m =>
              @OPAQUE (A -> C.M B) (A -> FM.M B) (Isomorphism_fn _ (Isomorphism_M _)) (Some (fun f =>
                @OPAQUE (C.M B) (FM.M B) (Isomorphism_M _) None))))))
     ; prim_fn := @C.bind
     ; model_fn := @FM.bind
     ; c_name := "m_bind"
     |}.

  Definition runM_ep : extern_properties :=
    {| type_desc :=
        @TYPEPARAM (fun (A : Type) `{InGraph_A : InGraph A} =>
          @TRANSPARENT nat InGraph_nat (Some (fun len =>
            @TRANSPARENT elt InGraph_elt (Some (fun init =>
              @OPAQUE (C.M A) (FM.M A) (Isomorphism_M _)
                      (Some (fun f => @TRANSPARENT A InGraph_A None)))))))
     ; prim_fn := @C.runM
     ; model_fn := @FM.runM
     ; c_name := "m_runM"
     |}.

  Definition set_ep : extern_properties :=
    {| type_desc :=
        @TRANSPARENT nat InGraph_nat (Some (fun n =>
          @TRANSPARENT elt InGraph_elt (Some (fun a =>
            @OPAQUE (C.M unit) (FM.M unit) (Isomorphism_M _) None))))
     ; prim_fn := @C.set
     ; model_fn := @FM.set
     ; c_name := "array_set"
     |}.

  Definition get_ep : extern_properties :=
    {| type_desc :=
        @TRANSPARENT nat InGraph_nat (Some (fun n =>
          @OPAQUE (C.M elt) (FM.M elt) (Isomorphism_M _) None))
     ; prim_fn := @C.get
     ; model_fn := @FM.get
     ; c_name := "array_get"
     |}.

  Axiom pure_properties : model_spec pure_ep.
  Axiom bind_properties : model_spec bind_ep.
  Axiom runM_properties : model_spec runM_ep.
  Axiom set_properties : model_spec set_ep.
  Axiom get_properties : model_spec get_ep.

  Arguments from A B {_}.
  Arguments to A B {_}.

  Lemma set_get :
    forall (n len : nat) (bound : n < len) (init : elt) (to_set : elt),
      (C.runM len init (C.bind (C.set n to_set) (fun _ => C.get n)))
        =
      (C.runM len init (C.pure to_set)).
  Proof.
    intros n len bound init to_set.

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

    eapply invariants.nth_replace_nth.
    rewrite repeat_length.
    auto.
  Qed.

End Array_Proofs.
