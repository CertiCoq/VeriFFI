From CertiCoq.Plugin Require Import CertiCoq.
Require Import VeriFFI.examples.array.prog.

CertiCoq Compile -build_dir "examples/array/" -file "prog" prog.
CertiCoq Generate Glue -build_dir "examples/array" -file "glue" [ option, nat, C.MI ].
