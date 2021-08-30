From CertiCoq.Plugin Require Import CertiCoq.
Require Import prog.

CertiCoq Generate Glue -file "glue" [mytree, console, string, unit].
CertiCoq Compile prog
         Extract Constants
         [ append => "append" with tinfo
         , pack => "pack" with tinfo
         , map => "map" with tinfo
         , to_upper => "to_upper" with tinfo
         ]
  Include [ "io.h" ].
