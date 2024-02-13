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
    
Remark string_desc_has_tag_prop: forall x, string_has_tag_prop x (string_get_desc x).
Proof.
destruct x; constructor.
Qed.
 
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
PROP ( (* don't need this, it's a tautology, see string_desc_has_tag_prop above 
      let c := string_get_desc x in 
      string_has_tag_prop x c 
      *)
    )
RETURN  ( Vint (Int.repr (Z.of_nat (ctor_tag (string_get_desc x)))) )
SEP (full_gc g t_info roots outlier ti sh gv).

Definition tag_spec_string2 : ident * funspec := 
DECLARE _get_Coq_Strings_String_string_tag
WITH g : graph, p : rep_type, x : string
PRE  [int_or_ptr_type]
  PROP (@is_in_graph string _ g x p )
  PARAMS (rep_type_val g p)
  SEP (graph_rep g)
POST [ tuint ]
  PROP (string_has_tag_prop x (string_get_desc x))
  RETURN  ( Vint (Int.repr (Z.of_nat (ctor_tag (string_get_desc x)))) )
SEP (graph_rep g).

Record alloc_prepackage : Type := {
   AP_g: graph;
   AP_ti: GCGraph.thread_info;
   AP_outlier: outlier_t; 
   AP_n: Z;
   AP_enough: 0 <= AP_n <= headroom AP_ti
 }.
   

Lemma AP_raw_color_range: 0 <= 0 < 4.
Proof. lia. Qed.


Record alloc_package (pp: alloc_prepackage) : Type := {
   AP_raw_fields: list raw_field;
   AP_tag: Z;
   AP_tag_range: 0 <= AP_tag < 256;
   AP_raw_fields_range: 0 < Zlength AP_raw_fields < two_p (WORD_SIZE * 8 - 10);
   AP_tag_no_scan: NO_SCAN_TAG <= AP_tag -> ~In None AP_raw_fields;
   AP_fields: list (EType * (VType * VType));
   AP_len: AP_n pp = (1 + Zlength AP_raw_fields)%Z;
   AP_vertex := new_copied_v (AP_g pp) O;
   AP_rvb := Build_raw_vertex_block false AP_vertex AP_raw_fields
       0 AP_tag AP_tag_range AP_raw_color_range AP_raw_fields_range AP_tag_no_scan;
   AP_compat: add_node_compatible (AP_g pp) AP_vertex AP_fields;
   AP_edge_compat: edge_compatible (AP_g pp) 0 AP_raw_fields AP_fields;
   AP_incl_outlier: incl (List_ext.filter_sum_right (List_ext.filter_option 
                              (raw_fields AP_rvb))) (AP_outlier pp)
}.

Definition AP_newg pp ap := add_node (AP_g pp) O (AP_rvb pp ap) (AP_fields pp ap).

Lemma allocate_in_nursery_pf {n: Z} {nursery : space}
   (H: 0 <= n <= nursery.(total_space)-nursery.(used_space)) :
  0 <= nursery.(used_space)+n <= nursery.(total_space).
Proof.
intros.
pose proof space_order nursery.
lia.
Qed.

Definition allocate_in_nursery (n: Z) (nursery : space)
   (H: 0 <= n <= nursery.(total_space)-nursery.(used_space)) :=
  {| space_start := nursery.(space_start);
     used_space := nursery.(used_space) + n;
     total_space := nursery.(total_space);
     space_sh := nursery.(space_sh);
     space_order := allocate_in_nursery_pf H;
     space_upper_bound := nursery.(space_upper_bound) |}.

Lemma allocate_in_full_gc_aux:
  forall n nursery H h,
Zlength (allocate_in_nursery n nursery H :: tl (spaces h)) = MAX_SPACES.
Proof.
intros.
pose proof spaces_size h.
destruct (spaces h).
inversion H0.
simpl.
rewrite Zlength_cons in *.
auto.
Qed.

Definition bump_alloc (pp: alloc_prepackage) : GCGraph.thread_info :=
  let tinfo := AP_ti pp in
  let nursery := heap_head (ti_heap tinfo) in
   {| ti_heap_p := tinfo.(ti_heap_p);
      ti_heap := {| spaces := allocate_in_nursery (AP_n pp) nursery (AP_enough pp) ::
                                      tl (spaces (ti_heap tinfo));
                                  spaces_size := allocate_in_full_gc_aux _ nursery (AP_enough pp) _ |};
      ti_args := tinfo.(ti_args);
      arg_size := tinfo.(arg_size);
      ti_frames := tinfo.(ti_frames);
      ti_nalloc := tinfo.(ti_nalloc) |}.

Definition alloc_at (tinfo: GCGraph.thread_info) : val :=
  let nursery := heap_head (ti_heap tinfo) in
   offset_val (WORD_SIZE * (used_space nursery)) (space_start nursery).

Definition bump_allocptr_spec: ident * funspec :=
 DECLARE _bump_allocptr
 WITH gv: globals, roots: roots_t, 
      sh: share, ti: val,
      pp: alloc_prepackage
 PRE [ thread_info, size_t ]
  PROP( writable_share sh )
  PARAMS (ti; Vptrofs (Ptrofs.repr (AP_n pp))) GLOBALS (gv)
  SEP (full_gc (AP_g pp) (AP_ti pp) roots (AP_outlier pp) ti sh gv)
 POST [ tptr int_or_ptr_type ]
  PROP( )
  RETURN ( alloc_at (AP_ti pp))
  SEP (graph_rep (AP_g pp);
       @data_at_ env_graph_gc.CompSpecs (nth_sh (AP_g pp) 0)
        (tarray int_or_ptr_type (AP_n pp)) (alloc_at (AP_ti pp));
       ALL pk: alloc_package pp,
       (graph_rep (AP_g pp)*
        vertex_at (nth_sh (AP_g pp) O) (vertex_address (AP_newg _ pk) (new_copied_v (AP_g pp) O)) 
              (header_new (AP_rvb _ pk)) 
              (fields_new (AP_newg _ pk) (AP_rvb _ pk) (new_copied_v (AP_g pp) O))) -*
       full_gc (AP_newg _ pk) (bump_alloc pp) roots (AP_outlier pp)  ti sh gv ).

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
  
Definition args_spec_String2 : funspec := 
  WITH g : graph, p : rep_type, chs: ascii*string
  PRE [int_or_ptr_type]
   PROP (is_in_graph g (String (fst chs) (snd chs)) p)
   PARAMS (rep_type_val g p)
   SEP (graph_rep g)
  POST [ tptr int_or_ptr_type ]
  EX  (p0 : rep_type) (p1: rep_type) (sh' : share),
  PROP (  writable_share sh';
          is_in_graph g (fst chs) p0; is_in_graph g (snd chs) p1
      )
  RETURN  ( rep_type_val g p ) 
  SEP (data_at sh' (tarray int_or_ptr_type 2) [rep_type_val g p0; rep_type_val g p1] (rep_type_val g p);
      data_at sh' (tarray int_or_ptr_type 2) [rep_type_val g p0; rep_type_val g p1] (rep_type_val g p) -* graph_rep g). 
  

Definition ascii_to_char_spec: ident * funspec :=
 DECLARE _ascii_to_char
 WITH g: graph, p: rep_type, ch: ascii
 PRE [ int_or_ptr_type ]
   PROP (is_in_graph g ch p)
   PARAMS (rep_type_val g p)
   SEP (graph_rep g)
 POST [ tuchar ]
   PROP()
   RETURN ( Vint (Int.repr (Z.of_N (N_of_ascii ch))) )
   SEP (graph_rep g).


Definition args_make_Coq_Init_Datatypes_String_String_spec : ident * funspec :=
DECLARE _get_args
        (args_spec_String2).

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
                      tag_spec_string2;
                      bump_allocptr_spec;
                      args_make_Coq_Init_Datatypes_String_String_spec;
                      make_Coq_Strings_String_string_EmptyString_spec;
                      alloc_make_Coq_Strings_String_string_String_spec;
                      alloc_make_Coq_Strings_Ascii_ascii_Ascii_spec;
                      gc_spec.garbage_collect_spec
                      (* _call, call_spec *)
                      ] .
