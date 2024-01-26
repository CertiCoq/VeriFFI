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

Definition string_get_desc (x : string) : ctor_desc := 
match x with 
| EmptyString => (@desc _ EmptyString _)
| String _ _ =>  (@desc _ String _)
end.
  
Inductive string_has_tag_prop : string -> ctor_desc -> Prop := 
| tagEmpty : string_has_tag_prop EmptyString (@desc _ EmptyString _)
| tagString c r : string_has_tag_prop (String c r) (@desc _ String _).
     
Definition tag_spec_string : ident * funspec := 
DECLARE _get_Coq_Strings_String_string_tag
WITH gv : globals, g : graph, p : rep_type,
x : string, roots : roots_t, sh : share,
ti : val, outlier : outlier_t, t_info : GCGraph.thread_info
PRE  [[  [int_or_ptr_type]  ]]
PROP (
  @is_in_graph string _ g x p;
  writable_share sh  )
(PARAMSx (  [rep_type_val g p] )
(GLOBALSx [gv]
(SEPx (full_gc g t_info roots outlier ti sh gv :: nil))))
POST [ tuint ]
(* EX  (xs : args (ctor_reific (nat_get_desc x))), *)
PROP ( (* 1. x has tag t and is constructed with the constructor description c. 
              a. Tag function relating to x.
              b. x = ctor_real c xs (* Doesn't type as this. *)

          TODO: Discuss - something around this should already exist for 
          generating general in_graph functions, and we want things to match.   
      *)
      (* let c := nat_get_desc x in 
      nat_has_tag_prop x c; *)
      (* let c := nat_get_desc x in 
      let r := result (ctor_reific c) xs in
      @is_in_graph (projT1 r) (@in_graph (projT1 r) (projT2 r)) g (ctor_real c xs) p   *)
      let c := string_get_desc x in 
      string_has_tag_prop x c (* Not 100% sure this is how we want it*)
    )
RETURN  ( Vint (Int.repr (Z.of_nat (ctor_tag (string_get_desc x)))) )
SEP (full_gc g t_info roots outlier ti sh gv).



Definition args_spec_String : funspec := 
  WITH gv : globals, g : graph, p : rep_type,
  chs: ascii*string, roots : roots_t, sh : share,
  ti : val, outlier : outlier_t, t_info : GCGraph.thread_info
  PRE  [[  [int_or_ptr_type] ]]
  PROP (
      writable_share sh;
          is_in_graph g (String (fst chs) (snd chs)) p  
      )
  (PARAMSx ( [rep_type_val g p])
  (GLOBALSx [gv]
  (SEPx (full_gc g t_info roots outlier ti sh gv :: nil))))
  POST [ tptr int_or_ptr_type (* tarray int_or_ptr_type 1 *)  ]
  EX  (p0 : rep_type) (p1: rep_type) (sh' : share),
  PROP (  writable_share sh';
          is_in_graph g (fst chs) p0; is_in_graph g (snd chs) p1
      )
  RETURN  ( rep_type_val g p ) 
  SEP (data_at sh' (tarray int_or_ptr_type 2) [rep_type_val g p0; rep_type_val g p1] (rep_type_val g p);
      data_at sh' (tarray int_or_ptr_type 2) [rep_type_val g p0; rep_type_val g p1] (rep_type_val g p) -* full_gc g t_info roots outlier ti sh gv). 
  

Definition ascii_to_char_spec: ident * funspec :=
 DECLARE _ascii_to_char
 WITH gv: globals, g: graph, p: rep_type, ch: ascii, roots: roots_t, 
      sh: share, ti: val, outlier: outlier_t, t_info: GCGraph.thread_info
 PRE [ int_or_ptr_type ]
   PROP (readable_share sh; is_in_graph g ch p)
   PARAMS (rep_type_val g p) GLOBALS (gv)
   SEP (full_gc g t_info roots outlier ti sh gv)
 POST [ tuchar ]
   PROP()
   RETURN ( Vint (Int.repr (Z.of_N (N_of_ascii ch))) )
   SEP (full_gc g t_info roots outlier ti sh gv).


Definition args_make_Coq_Init_Datatypes_String_String_spec : ident * funspec :=
DECLARE _get_args
        (args_spec_String).

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
Definition Gprog := [ ascii_to_char_spec;
                      tag_spec_string;
                      args_make_Coq_Init_Datatypes_String_String_spec;
                      make_Coq_Strings_String_string_EmptyString_spec;
                      alloc_make_Coq_Strings_String_string_String_spec;
                      alloc_make_Coq_Strings_Ascii_ascii_Ascii_spec;
                      gc_spec.garbage_collect_spec
                      (* _call, call_spec *)
                      ] .
