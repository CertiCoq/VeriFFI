Require Import VeriFFI.examples.bytestring.prog.
Require Import ZArith.
Require Import Psatz.
Require Export VeriFFI.verification.specs_general.
Require Export VeriFFI.generator.Rep.

Import Ascii.
Import Coq.Strings.String.

#[local] Obligation Tactic := gen.
MetaCoq Run (gen_for ascii).
MetaCoq Run (gen_for string).


Require Export VST.floyd.proofauto.
Require Export CertiGraph.CertiGC.GCGraph.
Export spatial_gcgraph.
From VeriFFI Require Export library.base_representation library.meta verification.graph_add verification.specs_library.

Require Import VeriFFI.examples.bytestring.prog.
Require Export VeriFFI.examples.bytestring.model.
Require Export VeriFFI.examples.bytestring.prims. 


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

#[export] Instance CCE1: change_composite_env env_graph_gc.CompSpecs CompSpecs.
make_cs_preserve env_graph_gc.CompSpecs CompSpecs.
Defined.


MetaCoq Run (desc_gen EmptyString).
MetaCoq Run (desc_gen String).
MetaCoq Run (desc_gen Ascii).

Definition make_Coq_Strings_String_string_EmptyString_spec : ident * funspec :=
    DECLARE _make_Coq_Strings_String_string_EmptyString
          (alloc_make_spec_general (@desc _ EmptyString _) 0). 

Definition alloc_make_Coq_Strings_String_string_String_spec : ident * funspec :=
    DECLARE _alloc_make_Coq_Strings_String_string_String
          (alloc_make_spec_general (@desc _ String _) 2).     

Definition alloc_make_Coq_Strings_Ascii_ascii_Ascii_spec : ident * funspec :=
    DECLARE _alloc_make_Coq_Strings_Ascii_ascii_Ascii
          (alloc_make_spec_general (@desc _ Ascii _) 8). 


Definition pack_spec : ident * funspec :=
  fn_desc_to_funspec Bytestring_Proofs.pack_desc.

Definition unpack_spec : ident * funspec :=
  fn_desc_to_funspec Bytestring_Proofs.unpack_desc.

Definition append_spec : ident * funspec :=
  fn_desc_to_funspec Bytestring_Proofs.append_desc.


Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := [ make_Coq_Strings_String_string_EmptyString_spec;
                      alloc_make_Coq_Strings_String_string_String_spec;
                      alloc_make_Coq_Strings_Ascii_ascii_Ascii_spec;
                      gc_spec.garbage_collect_spec
                      (* _call, call_spec *)
                      ] .
