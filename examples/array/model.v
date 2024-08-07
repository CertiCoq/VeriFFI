Require Import ZArith.
Require Import Psatz.
Require Import List.
Require Import String.
Open Scope string.

Require Import VeriFFI.generator.Rep.
Local Obligation Tactic := gen.
MetaCoq Run (gen_for unit).
MetaCoq Run (gen_for nat).

Require Import VeriFFI.library.meta.
Require Import VeriFFI.library.modelled.
Require Import VeriFFI.library.isomorphism.

Require Import VeriFFI.examples.array.prog.

#[export] Instance InGraph_elt : InGraph elt := InGraph_nat.

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
                        Isomorphism (FM.M A) (C.M A').
  #[local] Existing Instance Isomorphism_M.

  #[local] Instance InGraph_M : forall {A : Type} `{InGraph A}, InGraph (FM.M A).
  Admitted.

  Definition pure_desc : fn_desc :=
    {| fn_type_reified :=
        @TYPEPARAM _ (fun A (P_A : foreign_ann A) =>
          @ARG _ A P_A (fun a =>
            @RES _ (FM.M A) (@opaque _ (C.M A) (@InGraph_M A (@foreign_in_graph _ P_A)) (@Isomorphism_M A A (@Isomorphism_refl A)))))
     ; foreign_fn := @C.pure
     ; model_fn := fun '(A; (_; (a; tt))) => @FM.pure A a
     ; fn_arity := 2
     ; c_name := "m_pure"
     |}.

  Definition bind_desc : fn_desc :=
    {| fn_type_reified :=
        @TYPEPARAM _ (fun (A : Type) (P_A : foreign_ann A) =>
          @TYPEPARAM _ (fun (B : Type) (P_B : foreign_ann B) =>
            @ARG _ (FM.M A) (@opaque _ (C.M A) (@InGraph_M A (@foreign_in_graph _ P_A)) (Isomorphism_M _)) (fun m =>
              @ARG _ (A -> FM.M B) (@opaque _ (A -> C.M B) (@InGraph_fun _ _ (@foreign_in_graph _ P_A) (@InGraph_M B (@foreign_in_graph _ P_B))) (Isomorphism_fn _ (Isomorphism_M _))) (fun f =>
                                                                                                                    @RES _ (FM.M B) (@opaque _ (C.M B) (@InGraph_M B (@foreign_in_graph _ P_B)) (Isomorphism_M _))))))
     ; foreign_fn := @C.bind
     ; model_fn := fun '(A; (_; (B; (_; (m; (f; tt)))))) => @FM.bind A B m f
     ; fn_arity := 4
     ; c_name := "m_bind"
     |}.

  Definition runM_desc : fn_desc :=
    {| fn_type_reified :=
        @TYPEPARAM _ (fun (A : Type) (P_A : foreign_ann A) =>
          @ARG _ _ (@transparent nat InGraph_nat) (fun len =>
            @ARG _ _ (@transparent elt InGraph_elt) (fun init =>
              @ARG _ _ (@opaque (FM.M A) (C.M A) (@InGraph_M _ (@foreign_in_graph _ P_A)) (Isomorphism_M _)) (fun f =>
                @RES _ _ (@transparent A (@foreign_in_graph _ P_A))))))
     ; foreign_fn := @C.runM
     ; model_fn := fun '(A; (_; (len; (init; (f; tt))))) => @FM.runM A len init f
     ; fn_arity := 4
     ; c_name := "m_runM"
     |}.

  Definition set_desc : fn_desc :=
    {| fn_type_reified :=
        @ARG _ _ (@transparent nat InGraph_nat) (fun n =>
          @ARG _ _ (@transparent elt InGraph_elt) (fun a =>
            @RES _ _ (@opaque (FM.M unit) _ (InGraph_M) (Isomorphism_M _))))
     ; foreign_fn := @C.set
     ; model_fn := fun '(n; (a; tt)) => @FM.set n a
     ; fn_arity := 2
     ; c_name := "array_set"
     |}.

  Definition get_desc : fn_desc :=
    {| fn_type_reified :=
        @ARG _ _ (@transparent nat InGraph_nat) (fun n =>
          @RES _ _ (@opaque (FM.M elt) (C.M elt) (InGraph_M) (Isomorphism_M _)))
     ; foreign_fn := @C.get
     ; model_fn := fun '(n; tt) => @FM.get n
     ; fn_arity := 1
     ; c_name := "array_get"
     |}.

  Axiom pure_spec : model_spec pure_desc.
  Axiom bind_spec : model_spec bind_desc.
  Axiom runM_spec : model_spec runM_desc.
  Axiom set_spec : model_spec set_desc.
  Axiom get_spec : model_spec get_desc.

  Arguments from A B {_}.
  Arguments to A B {_}.

  Lemma set_get :
    forall (n len : nat) (bound : n < len) (init : elt) (to_set : elt),
      (C.runM len init (C.bind (C.set n to_set) (fun _ => C.get n)))
        =
      (C.runM len init (C.pure to_set)).
  Proof.
    intros n len bound init to_set.

    props runM_spec.
    foreign_rewrites.
    unfold FM.runM.

    props bind_spec.
    props pure_spec.
    foreign_rewrites.
    unfold FM.bind, FM.pure.

    props set_spec.
    props get_spec.
    foreign_rewrites.

    eapply invariants.nth_replace_nth.
    rewrite repeat_length.
    auto.
  Qed.

End Array_Proofs.
