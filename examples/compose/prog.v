Module Type Compose.
  Axiom compose : forall {A B C}, (B -> C) -> (A -> B) -> (A -> C).
End Compose.


Module C : Compose.
  Axiom compose : forall {A B C}, (B -> C) -> (A -> B) -> (A -> C).
End C.

(* Definition prog := C.compose (fun x => x + 1) (fun y => y + 1) 2. *)
Definition prog := C.compose S S 2.

From CertiCoq.Plugin Require Import CertiCoq.
CertiCoq Compile prog
  Extract Constants [
    C.compose => "compose" with tinfo
  ]
  Include [ "prims.h" ].
CertiCoq Generate Glue -file "glue" [ nat ].
