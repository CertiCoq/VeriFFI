From CertiCoq.Plugin Require Import CertiCoq.
Require Import VeriFFI.examples.uint63nat.prog.

CertiCoq Compile -build_dir "examples/uint63nat/" -file "prog" prog.
CertiCoq Generate Glue -build_dir "examples/uint63nat" -file "glue" [ nat ].
