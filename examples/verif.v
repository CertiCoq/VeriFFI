Require Export VeriFFI.library.base_representation.
Require Export VeriFFI.library.meta.
Require Export VeriFFI.generator.InGraph.
Require Export VeriFFI.generator.Rep.
Require Export VeriFFI.generator.Desc.


Unset Strict Unquote Universe Mode.

MetaCoq Run (in_graph_gen nat).
Instance Rep_nat : Rep nat. rep_gen. Defined.
MetaCoq Run (desc_gen O).
MetaCoq Run (desc_gen S).


