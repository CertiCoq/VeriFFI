From CertiCoq.Plugin Require Import CertiCoq.

Module Type Compose.
  Axiom compose : forall {A B C}, (B -> C) -> (A -> B) -> (A -> C).
End Compose.

Module C : Compose.
  Axiom compose : forall {A B C}, (B -> C) -> (A -> B) -> (A -> C).
End C.

CertiCoq Register [
    C.compose => "compose" with tinfo
  ] Include [ "prims.h" ].

(* Definition prog := C.compose (fun x => x + 1) (fun y => y + 1) 2. *)
Definition prog := C.compose S S 2.

CertiCoq Compile -build_dir "examples/compose/" -file "prog" prog.
CertiCoq Generate Glue -build_dir "examples/compose" -file "glue" [ ].
