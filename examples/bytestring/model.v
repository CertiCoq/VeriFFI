Require Import ZArith.
Require Import Psatz.
Require Import List.
Require Import String.
Open Scope string.

Require Import VeriFFI.generator.all.
Obligation Tactic := gen.
MetaCoq Run (gen_for nat).
MetaCoq Run (gen_for string).

Require Import VeriFFI.library.meta.
Require Import VeriFFI.library.modelled.
Require Import VeriFFI.library.isomorphism.

Require Import VeriFFI.examples.bytestring.prog.

Module FM <: Bytestring.
  Definition bytestring : Type := string.

  Definition append (x y : bytestring) := append x y.
  Definition pack (x : string) : bytestring := x.
  Definition unpack (x : bytestring) : string := x.

  Record world := {
    state : Type;
    initial_state : state;
    input : state -> bytestring * state -> Prop;
    output : bytestring * state -> state -> Prop;
  }.

  Definition state : Type :=
    (string * string). (* the input stream and the output stream *)
  Definition M (w : World) (A : Type) : Type := state w -> A * state w.
  Definition pure {A} (a : A) : M A := fun s => (a, s).
  Definition bind {A B} (m : M A) (f : A -> M B) : M B :=
    fun s => f (fst (m s)) (snd (m s)).
    (* fun s => let '(a, s') := m s in f a s'. *)

  Definition print (x : bytestring) : M unit :=
    fun '(input, output) => (tt, (input, append output "x")).

  Definition scan (n : nat) : M bytestring :=
    fun '(input, output) => (substring 0 n input,
        (substring n (length input) input, append output "x")).

(*   Definition stream : Type := string. *)
(*   Definition get_stdin (_ : unit) : stream := "". *)
(*   Definition get_stdout (_ : unit) : stream := "". *)

(*   Definition runM {A} (instream outstream : stream) (m : M A) : A := *)
(*     fst (m (instream, outstream)). *)

  Definition runM (w : world) (m : M unit) : unit :=
    fst (m (initial_state w)).


End FM.

Module Bytestring_Proofs.
  Axiom Isomorphism_bytestring : Isomorphism C.bytestring FM.bytestring.
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

  Definition pure_ep : fn_desc :=
    {| type_desc :=
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @TRANSPARENT A Rep_A (Some (fun arr =>
            @OPAQUE (C.M A) (FM.M A) (Isomorphism_M _) None)))
     ; prim_fn := @C.pure
     ; model_fn := @FM.pure
     ; c_name := "m_pure"
     |}.

  Definition bind_ep : fn_desc :=
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

  Definition runM_ep : fn_desc :=
    {| type_desc :=
        @TYPEPARAM (fun (A : Type) `{Rep_A : Rep A} =>
          @OPAQUE (C.M A) (FM.M A) (Isomorphism_M _)
                  (Some (fun f => @TRANSPARENT A Rep_A None)))
     ; prim_fn := @C.runM
     ; model_fn := @FM.runM
     ; c_name := "m_runM"
     |}.

  Definition print_ep : fn_desc :=
    {| type_desc :=
        @OPAQUE C.bytestring FM.bytestring Isomorphism_bytestring (Some (fun n =>
          @OPAQUE (C.M unit) (FM.M unit) (Isomorphism_M _) None))
     ; prim_fn := @C.print
     ; model_fn := @FM.print
     ; c_name := "print"
     |}.

  Definition scan_ep : fn_desc :=
    {| type_desc :=
        @TRANSPARENT nat Rep_nat (Some (fun n =>
          @OPAQUE (C.M C.bytestring) (FM.M FM.bytestring) (Isomorphism_M Isomorphism_bytestring) None))
     ; prim_fn := @C.scan
     ; model_fn := @FM.scan
     ; c_name := "scan"
     |}.

  Axiom pure_properties : model_spec pure_ep.
  Axiom bind_properties : model_spec bind_ep.
  Axiom runM_properties : model_spec runM_ep.
  Axiom print_properties : model_spec print_ep.
  Axiom scan_properties : model_spec scan_ep.

  Arguments from A B {_}.
  Arguments to A B {_}.

  Lemma print_steps :
    forall (a b : C.bytestring),
      (C.runM (C.bind (C.print a) (fun _ => C.print b)))
        =
      (C.runM (C.print (C.append a b))).
  Proof.
    intros a b.

    props runM_properties.
    prim_rewrites.
    unfold FM.runM.

    props bind_properties.
    unfold FM.bind.
    prim_rewrites.

    props print_properties.
    prim_rewrites.

    auto.
  Qed.

End Bytestring_Proofs.
