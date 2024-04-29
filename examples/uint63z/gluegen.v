From CertiCoq.Plugin Require Import CertiCoq.
Require Import ZArith.
Require Import VeriFFI.examples.uint63z.prog.

CertiCoq Compile -build_dir "examples/uint63z/" -file "prog" prog.
CertiCoq Generate Glue -build_dir "examples/uint63z" -file "glue" [ Z ].
