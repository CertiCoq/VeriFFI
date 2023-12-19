From CertiCoq.Plugin Require Import CertiCoq.
Require Import String.
Require Import VeriFFI.examples.bytestring.prog.

CertiCoq Compile -build_dir "examples/bytestring/" -file "prog" prog.
CertiCoq Generate Glue -build_dir "examples/bytestring" -file "glue"
  [ unit, nat, bool, string, C.MI ].
