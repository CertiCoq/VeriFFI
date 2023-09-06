Require Import ZArith.
Require Import Psatz.
Require Import List.
Require Import String.
Open Scope string.

Require Import VeriFFI.generator.Rep.
Obligation Tactic := gen.
MetaCoq Run (gen_for nat).
MetaCoq Run (gen_for string).
MetaCoq Run (gen_for unit).

Require Import VeriFFI.library.meta.
Require Import VeriFFI.library.modelled.
Require Import VeriFFI.library.isomorphism.

Require Import VeriFFI.examples.bytestring.prog.

Module FM.
  Definition bytestring : Type := string.

  Definition append (x y : bytestring) := append x y.
  Definition pack (x : string) : bytestring := x.
  Definition unpack (x : bytestring) : string := x.

  Definition state : Type :=
    (string * string). (* the input stream and the output stream *)
  Definition M (A : Type) : Type := state -> A * state.
  Definition pure {A} (a : A) : M A := fun s => (a, s).
  Definition bind {A B} (m : M A) (f : A -> M B) : M B :=
    fun s => f (fst (m s)) (snd (m s)).
    (* fun s => let '(a, s') := m s in f a s'. *)

  Definition print (x : bytestring) : M unit :=
    fun '(input, output) => (tt, (input, append output "x")).

  Definition scan (n : nat) : M bytestring :=
    fun '(input, output) => (substring 0 n input,
        (substring n (length input) input, append output "x")).

  Definition stream : Type := string.
  Definition get_stdin (_ : unit) : stream := "".
  Definition get_stdout (_ : unit) : stream := "".

  Definition runM {A} (instream outstream : stream) (m : M A) : A :=
    fst (m (instream, outstream)).

  (* Joomy's note: We wrote this definition in a meeting but I'm not
  sure how it fits in the pattern we designed. I'm leaving it here in
  case anyone wants to play around with it.

  Record world := {
    state : Type;
    initial_state : state;
    input : state -> bytestring * state -> Prop;
    output : bytestring * state -> state -> Prop;
  }.
  Definition M (w : World) (A : Type) : Type := state w -> A * state w.

  Definition runM (w : world) (m : M unit) : unit :=
    fst (m (initial_state w)).
  *)
End FM.

Module Bytestring_Proofs.
  Axiom Isomorphism_bytestring : Isomorphism FM.bytestring C.bytestring.
  Axiom Isomorphism_M : forall {A A' : Type} (I : Isomorphism A A'),
                        Isomorphism (FM.M A) (C.M A').
  Axiom Isomorphism_stream : Isomorphism FM.stream C.stream.
  Existing Instance Isomorphism_bytestring.
  Existing Instance Isomorphism_M.
  Existing Instance Isomorphism_stream.

  Instance GraphPredicate_bytestring : GraphPredicate FM.bytestring.
    refine {| graph_predicate g x p := _ |}.
    (* TODO this is where we describe how an OCaml bytestring 
            is represented within the graph *)
    Admitted.
  Instance InGraph_bytestring : InGraph FM.bytestring.
    econstructor.
    (*  TODO this is where we prove lemmas about the graph predicate above *)
    * admit.
    * admit.
    Admitted.
  Instance GraphPredicate_M {A : Type} `{GP : GraphPredicate A} : GraphPredicate (FM.M A).
    refine {| graph_predicate g x p := _ |}.
    (* TODO this is where we describe how the monad type
            is represented within the graph *)
    Admitted.
  Instance InGraph_M {A : Type} `{GP : InGraph A} : InGraph (FM.M A).
    econstructor.
    (*  TODO this is where we prove lemmas about the graph predicate above *)
    * admit.
    * admit.
    Admitted.
  Instance GraphPredicate_stream : GraphPredicate FM.stream.
    refine {| graph_predicate g x p := _ |}.
    (* TODO this is where we describe how a stream is represented within the graph *)
    Admitted.
  Instance InGraph_stream : InGraph FM.stream.
    econstructor.
    (*  TODO this is where we prove lemmas about the graph predicate above *)
    * admit.
    * admit.
    Admitted.

  Definition append_desc : fn_desc :=
    {| type_desc :=
        @ARG _ FM.bytestring (opaque C.bytestring) (fun _ =>
          @ARG _ FM.bytestring (opaque C.bytestring) (fun _ =>
            @RES _ FM.bytestring (opaque C.bytestring)))
     ; prim_fn := C.append
     ; model_fn := fun '(a; (b; tt)) =>  FM.append a b
     ; f_arity := 2
     ; c_name := "append"
     |}.

  Definition pack_desc : fn_desc :=
    {| type_desc :=
        @ARG _ string transparent (fun _ =>
          @RES _ FM.bytestring (opaque C.bytestring))
     ; prim_fn := C.pack
     ; model_fn := fun '(x; tt) => FM.pack x
     ; f_arity := 1
     ; c_name := "pack"
     |}.

  Definition unpack_desc : fn_desc :=
    {| type_desc :=
        @ARG _ FM.bytestring (opaque C.bytestring) (fun _ =>
          @RES _ string transparent)
     ; prim_fn := C.unpack
     ; model_fn := fun '(x; tt) => FM.unpack x
     ; f_arity := 1
     ; c_name := "unpack"
     |}.

  Definition pure_desc : fn_desc :=
    {| type_desc :=
        @TYPEPARAM _ (fun (A : Type) (H_A : prim_ann A) =>
          @ARG _ _ (@transparent A (@prim_in_graph _ H_A)) (fun _ =>
            @RES _ _ (@opaque (FM.M A) (C.M A) (@InGraph_M A (@prim_in_graph _ H_A)) (Isomorphism_M _))))
     ; prim_fn := @C.pure
     ; model_fn := fun '(A; (_; (a; tt))) => @FM.pure A a
     ; f_arity := 2
     ; c_name := "m_pure"
     |}.

  Definition bind_desc : fn_desc :=
    {| type_desc :=
        @TYPEPARAM _ (fun (A : Type) `(H_A : prim_ann A) =>
          @TYPEPARAM _ (fun (B : Type) `(H_B : prim_ann B) =>
            @ARG _ _ (@opaque (FM.M A) (C.M A) (@InGraph_M A (@prim_in_graph _ H_A)) (Isomorphism_M _)) (fun m =>
              @ARG _ (A -> FM.M B) (@opaque _ (A -> C.M B) (@InGraph_fun _ _ (@prim_in_graph _ H_A) (@InGraph_M B (@prim_in_graph _ H_B))) (Isomorphism_fn _ (Isomorphism_M _))) (fun f =>
                @RES _ _ (@opaque (FM.M B) (C.M B) (@InGraph_M B (@prim_in_graph _ H_B)) (Isomorphism_M _))))))
     ; prim_fn := @C.bind
     ; model_fn := fun '(A; (_; (B; (_; (m; (f; tt)))))) => @FM.bind A B m f
     ; f_arity := 4
     ; c_name := "m_bind"
     |}.

  Definition runM_desc : fn_desc :=
    {| type_desc :=
        @TYPEPARAM _ (fun (A : Type) `(H_A : prim_ann A) =>
          @ARG _ _ (@opaque FM.stream C.stream InGraph_stream Isomorphism_stream) (fun _ =>
            @ARG _ _ (@opaque FM.stream C.stream InGraph_stream Isomorphism_stream) (fun _ =>
              @ARG _ _ (@opaque (FM.M A) (C.M A) (@InGraph_M A (@prim_in_graph _ H_A)) (Isomorphism_M _)) (fun _ =>
                @RES _ _ (@transparent A (@prim_in_graph _ H_A))))))
     ; prim_fn := @C.runM
     ; model_fn := fun '(A; (_; (i; (o; (m; tt))))) => @FM.runM A i o m
     ; f_arity := 4
     ; c_name := "m_runM"
     |}.

  Definition print_desc : fn_desc :=
    {| type_desc :=
        @ARG _ _ (@opaque FM.bytestring C.bytestring InGraph_bytestring Isomorphism_bytestring) (fun n =>
          @RES _ _ (@opaque (FM.M unit) (C.M unit) (@InGraph_M unit InGraph_unit) (Isomorphism_M _)))
     ; prim_fn := @C.print
     ; model_fn := fun '(x; tt) => @FM.print x
     ; f_arity := 1
     ; c_name := "print"
     |}.

  Definition scan_desc : fn_desc :=
    {| type_desc :=
        @ARG _ _ (@transparent nat InGraph_nat) (fun n =>
          @RES _ _ (@opaque (FM.M FM.bytestring) (C.M C.bytestring) _ (Isomorphism_M Isomorphism_bytestring)))
     ; prim_fn := @C.scan
     ; model_fn := fun '(x; tt) => @FM.scan x
     ; f_arity := 1
     ; c_name := "scan"
     |}.

  (* Maybe also get_stdin and get_stdout? *)

  Axiom append_spec : model_spec append_desc.
  Axiom pack_spec : model_spec pack_desc.
  Axiom unpack_spec : model_spec unpack_desc.
  Axiom pure_spec : model_spec pure_desc.
  Axiom bind_spec : model_spec bind_desc.
  Axiom runM_spec : model_spec runM_desc.
  Axiom print_spec : model_spec print_desc.
  Axiom scan_spec : model_spec scan_desc.

  Arguments from A B {_}.
  Arguments to A B {_}.

  Lemma print_steps :
    forall (a b : C.bytestring),
      (C.runM (C.get_stdin tt) (C.get_stdout tt) (C.bind (C.print a) (fun _ => C.print b)))
        =
      (C.runM (C.get_stdin tt) (C.get_stdout tt) (C.print (C.append a b))).
  Proof.
    intros a b.

    props runM_spec.
    prim_rewrites.
    unfold FM.runM.

    props bind_spec.
    unfold FM.bind.
    prim_rewrites.

    props print_spec.
    prim_rewrites.

    auto.
  Qed.

End Bytestring_Proofs.
