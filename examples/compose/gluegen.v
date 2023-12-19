From CertiCoq.Plugin Require Import CertiCoq.
Require Import VeriFFI.examples.compose.prog.

CertiCoq Compile -build_dir "examples/compose/" -file "prog" prog.
CertiCoq Generate Glue -build_dir "examples/compose" -file "glue" [ ].
