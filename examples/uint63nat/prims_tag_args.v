Require Import VeriFFI.examples.uint63nat.prog.

Require Import ZArith.
Require Import Psatz.

Require Import VeriFFI.verification.specs_general.

Require Import VeriFFI.generator.Rep.

Obligation Tactic := gen.
MetaCoq Run (gen_for nat).
MetaCoq Run (gen_for bool).

MetaCoq Run (desc_gen S).
MetaCoq Run (desc_gen O).

Require Import VST.floyd.proofauto.
Require Import CertiGraph.CertiGC.GCGraph.

From VeriFFI Require Import library.base_representation.
From VeriFFI Require Import library.meta.
From VeriFFI Require Import verification.graph_add.
From VeriFFI Require Import verification.specs_library.

Require Import VeriFFI.examples.uint63nat.Verif_prog_general.
Require Import VeriFFI.examples.uint63nat.glue. 

(* #[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined. *)

(* Specfication of alloc - would be generalized otherwise. *)
Definition alloc_make_Coq_Init_Datatypes_nat_S_spec : ident * funspec :=
  DECLARE _alloc_make_Coq_Init_Datatypes_nat_S
          (alloc_make_spec_general (@desc _ S _) 1).

Definition alloc_make_Coq_Init_Datatypes_nat_O_spec : ident * funspec :=
    DECLARE _make_Coq_Init_Datatypes_nat_O
      WITH gv : globals, g : graph
      PRE  [ ] 
          PROP ()
          PARAMS ()
          GLOBALS ()
          SEP (spatial_gcgraph.graph_rep g)
      POST [ (talignas 3%N (tptr tvoid)) ]  
        EX (x : rep_type), 
        PROP (@is_in_graph nat _ g O x) 
        LOCAL (temp ret_temp (rep_type_val g x)) 
        SEP (spatial_gcgraph.graph_rep g).

(* Same as in UVRooster - TODO: encode_Z as relation to fit our general scheme *)
Definition encode_Z (x: Z): Z := x * 2 + 1.
Definition min_signed: Z := - 2^62.
Definition max_signed: Z := 2^62 - 1.

Definition nat_get_desc (x : nat) : constructor_description := 
match x with 
| O => (@desc _ O _)
| S n =>  (@desc _ S _)
end.
 
Inductive nat_has_tag_prop : nat -> constructor_description -> Prop := 
| tagO : nat_has_tag_prop O (@desc _ O _)
| tagS n : nat_has_tag_prop (S n) (@desc _ S _).


Variable X_get_desc : forall (X_ : Type) (R_: Rep X_) (x : X_), constructor_description. 
Variable X_has_tag_prop : forall (X_ : Type) (R_: Rep X_) (x : X_), constructor_description -> Prop.

Definition tag_spec_S : ident * funspec := 
    DECLARE _get_Coq_Init_Datatypes_nat_tag
    WITH gv : globals, g : graph, p : rep_type,
    x : nat, roots : roots_t, sh : share,
    ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
    PRE  [[  [int_or_ptr_type] ]]
    PROP (
      @is_in_graph nat _ g x p;
      writable_share sh)
    (PARAMSx ( [rep_type_val g p])
    (GLOBALSx nil
    (SEPx (full_gc g t_info roots outlier ti sh :: nil))))
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
          let c := nat_get_desc x in 
          nat_has_tag_prop x c (* Not 100% sure this is how we want it*)
        )
    RETURN  ( Vint (Int.repr (Z.of_nat (ctor_tag (nat_get_desc x)))) )
    SEP (full_gc g t_info roots outlier ti sh).

Definition tag_spec_general (X: Type) (R_ : Rep X) :  funspec := 
    WITH gv : globals, g : graph, p : rep_type,
    x : X, roots : roots_t, sh : share,
    ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
    PRE  [[  [int_or_ptr_type] ]]
    PROP (
        @is_in_graph X (@in_graph X R_) g x p;
        writable_share sh)
    (PARAMSx ( [rep_type_val g p])
    (GLOBALSx nil
    (SEPx (full_gc g t_info roots outlier ti sh :: nil))))
    POST [ tuint ]
    PROP ( let c := X_get_desc X R_ x in 
            X_has_tag_prop X R_ x c 
        )
    RETURN  ( Vint (Int.repr (Z.of_nat (ctor_tag (X_get_desc X R_ x)))) )
    SEP (full_gc g t_info roots outlier ti sh).

(* KS Plan:
1. Ensure this is the correct specification by instantiating/doing the proof for nat. 
2. Do the general proof.
*)    

(* General args function

struct Coq_Init_Datatypes_S_args {
  int_or_ptr64 Coq_Init_Datatypes_S_arg_0;
};

struct prog_eif_args {
  int_or_ptr64 prog_eif_arg_0;
  int_or_ptr64 prog_eif_arg_1;
  int_or_ptr64 prog_eif_arg_2;
};

struct Coq_Init_Datatypes_S_args *get_Coq_Init_Datatypes_S_args(int_or_ptr64 $v)
{
  return (struct Coq_Init_Datatypes_S_args * ) $v;
  }

  struct prog_eif_args *get_prog_eif_args(int_or_ptr64 $v)
{
  return (struct prog_eif_args * ) $v;
  }

*)

(* Definition args_spec_S (c : constructor_description) (n : nat) : funspec := 
    WITH gv : globals, g : graph, p : rep_type,
    xs : args (ctor_reific c), roots : roots_t, sh : share,
    ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
    PRE  [[  [int_or_ptr_type] ]]
    PROP (
      c = (@desc _ S _); 
      n = 1%nat;
      writable_share sh;
      let r := result (ctor_reific c) xs in
          @is_in_graph (projT1 r) (@in_graph (projT1 r) (projT2 r)) g (ctor_real c xs) p  
      )
    (PARAMSx ( [rep_type_val g p])
    (GLOBALSx nil
    (SEPx (full_gc g t_info roots outlier ti sh :: nil))))
    POST [ tptr (Tstruct _Coq_Init_Datatypes_S_args noattr) ]
    EX  (p' : rep_type),
    PROP (  
            ctor_in_graphs g (ctor_reific c) xs [p']
        )
    RETURN  ( rep_type_val g p ) 
    SEP (data_at sh (Tstruct _Coq_Init_Datatypes_S_args noattr) (rep_type_val g p') (rep_type_val g p);
     data_at sh (Tstruct _Coq_Init_Datatypes_S_args noattr) (rep_type_val g p') (rep_type_val g p) -* full_gc g t_info roots outlier ti sh). 
*) 

Goal     (@desc _ S _)  = (@desc _ S _) . 
Proof. 
    unfold desc. unfold S_desc. simpl.
Admitted.


(* Definition args_spec_S' (c : constructor_description) (n : nat) : funspec := 
WITH gv : globals, g : graph, p : rep_type,
x: nat, roots : roots_t, sh : share,
ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
PRE  [[  [int_or_ptr_type] ]]
PROP (
    writable_share sh;
        is_in_graph g (S x) p  
    )
(PARAMSx ( [rep_type_val g p])
(GLOBALSx nil
(SEPx (full_gc g t_info roots outlier ti sh :: nil))))
POST [ tptr ((Tstruct _Coq_Init_Datatypes_S_args noattr)) (* tarray int_or_ptr_type 1 *)  ]
EX  (p' : rep_type) (sh' : share),
PROP (  
        is_in_graph g x p'
    )
RETURN  ( rep_type_val g p ) 
SEP (data_at sh' (tarray int_or_ptr_type 1) [rep_type_val g p'] (rep_type_val g p);
    data_at sh' (tarray int_or_ptr_type 1) [rep_type_val g p'] (rep_type_val g p) -* full_gc g t_info roots outlier ti sh). 
*) 

(*
Definition test_int_or_ptr_spec :=
 DECLARE _test_int_or_ptr
 WITH x : val
 PRE [int_or_ptr_type]
   PROP (valid_int_or_ptr x)
   PARAMS (x)
   GLOBALS ()
   SEP ()
 POST [ tint ]
   PROP()
   LOCAL(temp ret_temp
          (Vint (Int.repr (match x with
                           | Vint _ => if Archi.ptr64 then 0 else 1
                           | Vlong _ => if Archi.ptr64 then 1 else 0
                           | _ => 0
                           end))))
   SEP().

   Possibly change to size_or_ptr? - In C code call it value?
 *)    

(* 1/1
data_at (nth_sh g (vgeneration v)) tulong (Z2val (make_header g v))
  (offset_val (-8) (vertex_address g v))
  * data_at (nth_sh g (vgeneration v))
      (tarray int_or_ptr_type (Zlength (make_fields_vals g v)))
      (make_fields_vals g v) (vertex_address g v)
  * (data_at (nth_sh g (vgeneration v)) tulong (Z2val (make_header g v))
       (offset_val (-8) (vertex_address g v))
       * data_at (nth_sh g (vgeneration v))
           (tarray int_or_ptr_type (Zlength (make_fields_vals g v)))
           (make_fields_vals g v) (vertex_address g v) -*
     spatial_gcgraph.graph_rep g)
  * spatial_gcgraph.outlier_rep outlier
  * before_gc_thread_info_rep sh t_info ti
  * spatial_gcgraph.ti_token_rep t_info
|-- data_at sh (Tstruct _Coq_Init_Datatypes_S_args noattr)
      (rep_type_val g p') (vertex_address g v)
      * (data_at sh (Tstruct _Coq_Init_Datatypes_S_args noattr)
           (rep_type_val g p') (vertex_address g v) -*
         spatial_gcgraph.outlier_rep outlier
           * before_gc_thread_info_rep sh t_info ti
           * spatial_gcgraph.ti_token_rep t_info
           * spatial_gcgraph.graph_rep g) *)

     (* Have an array at this position. *)

     (* KS: Name for Pattern for the focussing. *)

     Print full_gc.


Print InGraph_nat.

Print graph_cRep.
Print enum.
Print Rep.
(* Have this as an entailment? - E.g., benefits: no function call *)     

Print constructor_description.
(* 
Definition args_spec_general : funspec := 
WITH c : constructor_description, g : graph, p : rep_type,
xs : args (ctor_reific c), roots : roots_t, sh : share,
ti : val, outlier : outlier_t, t_info : GCGraph.thread_info
PRE   [int_or_ptr_type]
PROP (
    writable_share sh;
    let r := result (ctor_reific c) xs in
        @is_in_graph (projT1 r) (@in_graph (projT1 r) (projT2 r)) g (ctor_real c xs) p  
    )
PARAMS ( rep_type_val g p)
SEP (full_gc g t_info roots outlier ti sh)
POST [ tptr int_or_ptr_type ]
EX  (ps' : list rep_type),
PROP (  
        let r := result (ctor_reific c) xs in 
        ctor_in_graphs g (ctor_reific c) xs ps'
    )
RETURN  ( rep_type_val g p ) 
SEP (data_at sh (Tarray int_or_ptr_type (Zlength ps')) (map (rep_type_val g) ps') (rep_type_val g p);
    data_at sh (Tarray int_or_ptr_type (Zlength ps')) (map (rep_type_val g) ps') (rep_type_val g p) -* full_gc g t_info roots outlier ti sh). 
        *) 


(* TODO: Discuss. *)    
(* 
Definition args_spec_general (c : constructor_description) (n : nat) (args_type : ident) : funspec := 
WITH gv : globals, g : graph, p : rep_type,
xs : args (ctor_reific c), roots : roots_t, sh : share,
ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
PRE  [[  [int_or_ptr_type] ]]
PROP (
    writable_share sh;
    let r := result (ctor_reific c) xs in
        @is_in_graph (projT1 r) (@in_graph (projT1 r) (projT2 r)) g (ctor_real c xs) p  
    )
(PARAMSx ( [rep_type_val g p])
(GLOBALSx nil
(SEPx (full_gc g t_info roots outlier ti sh :: nil))))
POST [ tptr (Tstruct args_type noattr) ]
EX  (ps' : list rep_type),
PROP (  
        let r := result (ctor_reific c) xs in 
        ctor_in_graphs g (ctor_reific c) xs ps'
    )
RETURN  ( rep_type_val g p ) 
SEP (data_at sh (Tstruct args_type noattr) (map (rep_type_val g) ps') (rep_type_val g p)
    * (data_at sh (Tstruct args_type noattr) (map (rep_type_val g) ps') (rep_type_val g p) -* full_gc g t_info roots outlier ti sh)). 
*) 

(* Definition args_make_Coq_Init_Datatypes_nat_S_spec : ident * funspec :=
DECLARE _get_Coq_Init_Datatypes_S_args
        (args_spec_S' (@desc _ S _) 1).
   *) 
 


    (* 
    Definition args_spec_general (c : constructor_description) (n : nat) : funspec := 
    WITH gv : globals, g : graph, p : rep_type,
    xs : args (ctor_reific c), roots : roots_t, sh : share,
    ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
    PRE  [[  [int_or_ptr_type] ]]
    PROP (
      writable_share sh;
      let r := result (ctor_reific c) xs in
          @is_in_graph (projT1 r) (@in_graph (projT1 r) (projT2 r)) g (ctor_real c xs) p  
      )
    (PARAMSx ( [rep_type_val g p])
    (GLOBALSx nil
    (SEPx (full_gc g t_info roots outlier ti sh :: nil))))
    POST [ Tstruct _Coq_Init_Datatypes_S_args (* TODO *) noattr ]
    EX (ps : list rep_type),
    PROP (  
        )
    RETURN  ( Vundef ) (* TODO: Basically returning elements corresponding to ps. *)
    SEP (full_gc g t_info roots outlier ti sh).
    *)

Search type.
Print tbool.

Definition is_ptr_spec : ident * funspec := 
    DECLARE _is_ptr 
    WITH x : val
    PRE [int_or_ptr_type]
      PROP ()
      PARAMS (x)
      GLOBALS ()
      SEP ()
    POST [ tbool ]
      PROP()
      LOCAL(temp ret_temp
             (Vint (Int.repr (match x with
                              | Vint _ => if Archi.ptr64 then 1 else 0
                              | Vlong _ => if Archi.ptr64 then 0 else 1
                              | _ => 1
                              end))))
      SEP().

(* 
 Inductive header_of_rep: ctor_rep -> Z -> Prop :=
 | header_enum: forall t, header_of_rep (enum t) (Z.of_N ((N.shiftl t 1) + 1))
 | header_boxed: forall t a, header_of_rep (boxed t a) (Z.of_N ((N.shiftl a 10) + t)).  
 *)

 Definition get_unboxed_ordinal_spec : ident * funspec := 
    DECLARE _get_unboxed_ordinal 
    WITH  z : Z
    PRE [ int_or_ptr_type ]
       PROP () 
       PARAMS (Vlong (Int64.repr z))
       SEP (emp) 
   POST [ tuint ] 
       PROP () 
       RETURN (Vint (Int.repr (Z.shiftr z 1))) 
       SEP (emp).

(* TODO: FIX 

   LOCAL (temp __b b; temp __v (vertex_address g v))
   SEP (full_gc g t_info roots outlier ti sh))
  ((_t'2 = _get_boxed_ordinal(__v);
    __t = _t'2;)
   MORE_COMMANDS) POSTCONDITION

*)
 Definition get_boxed_ordinal_spec : ident * funspec := 
     DECLARE _get_boxed_ordinal 
     WITH g : graph, v : VType, roots : roots_t, sh : share,
     ti : val, outlier : outlier_t, t_info : GCGraph.thread_info
     PRE [ int_or_ptr_type ]
        PROP (graph_has_v g v)  
        PARAMS (vertex_address g v)
        SEP (full_gc g t_info roots outlier ti sh) 
    POST [ tuint ] 
        PROP () 
        RETURN (Vint (Int.repr (raw_tag (graph_model.vlabel g v))))
        SEP (full_gc g t_info roots outlier ti sh).



Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := [is_ptr_spec; get_boxed_ordinal_spec; get_unboxed_ordinal_spec;
                    tag_spec_S; alloc_make_Coq_Init_Datatypes_nat_O_spec; alloc_make_Coq_Init_Datatypes_nat_S_spec
                    (* ; args_make_Coq_Init_Datatypes_nat_S_spec *) ] .

Definition description_S := @desc _ S _. 

(* Lemma data_at_isptr_Struct:
forall sh ( v p : val) ,
 data_at sh (Tstruct _Coq_Init_Datatypes_S_args noattr) v p |-- !! isptr p.
Admitted. 

#[export] Hint Resolve data_at_isptr_Struct : saturate_local.

Lemma valid_pointer_ex:
forall sh ( v p : val) ,
 data_at sh (Tstruct _Coq_Init_Datatypes_S_args noattr) v p |-- valid_pointer p.
 Admitted.

#[export] Hint Resolve valid_pointer_ex : valid_pointer. *)


(* 

value uint63_to_nat(struct thread_info *tinfo, value t) {
  value i = t >> 1;
  value temp = make_Coq_Init_Datatypes_nat_O();
  while (i) {
    temp = alloc_make_Coq_Init_Datatypes_nat_S(tinfo, temp);
    i--;
  }
  return temp;
}

*)

(*  Lemma is_in_graphs_nat g n p : 
    is_in_graph g (S n) p -> exists p', in_graphs g (n; tt) [p']. *)

(* TODO: Is there a description of what is generated by InGraph? 
   Otherwise, I'd start with this.
*)
(* Lemma body_args :
  semax_body Vprog Gprog
             f_get_Coq_Init_Datatypes_S_args
             args_make_Coq_Init_Datatypes_nat_S_spec.
Proof. 
    start_function. 
    forward. 
    { unfold full_gc. entailer!. admit.  }
    destruct H as (p'&(H1&H2)).
    Exists p'. 
    entailer!. 
    simpl in H2. destruct p; try inversion H2.
    destruct H3 as (H3&H4).
    unfold full_gc. Intros. 
    sep_apply (spatial_gcgraph.graph_vertex_ramif_stable _ _ H3).
    entailer!. 
    unfold spatial_gcgraph.vertex_rep. 
    unfold spatial_gcgraph.vertex_at. 
    simpl. Exists (nth_sh g (vgeneration v)).
    entailer!. 

    assert (data_at (nth_sh g (vgeneration v))
    (tarray int_or_ptr_type (Zlength (make_fields_vals g v)))
    (make_fields_vals g v) (vertex_address g v) = data_at (nth_sh g (vgeneration v)) (tarray int_or_ptr_type 1)
    [rep_type_val g p'] (vertex_address g v)) as eq.
    { unfold make_fields_vals.     unfold make_fields. simpl.     
    destruct (graph_model.vlabel g v); simpl in *.
      simple_if_tac; try contradiction. 
    simpl. destruct raw_color; try contradiction. 
    destruct H4. destruct H11. 
    inversion H12; subst. inversion H16. subst. 
    rewrite Zlength_map.
    rewrite !make_fields'_eq . 
    simpl.  f_equal. 
    destruct x0; try (destruct s); try reflexivity. 
    } 
    rewrite <- eq. 
    entailer!. 
    rewrite <- wand_sepcon_adjoint. entailer!.
    rewrite wand_sepcon_adjoint. 
    rewrite <- wand_twice.
    sep_apply modus_ponens_wand. 
    change_compspecs CompSpecs. 
    entailer!. 

    (* 
    (* 
    (* Massive unfolding problem! *)
    cbn in H1. *) 
    assert (exists n, ctor_real desc xs = S n ).

    assert (exists a, in_graphs g (ctor_reific desc) xs [a]).
    { clear - H1. admit. } 
    destruct H2 as (a&H2).
    Exists a. entailer!. 
    unfold full_gc. 
    (* Some generation_rep_eq... *)

(*     dependent inversion xs. 
    destruct (ctor_reific desc). 
     dependent induction xs. 
    
    destruct xs.  }    

    (* Joomy: 
       Is there a way for a sensible unfolding of specification in H1? *)
    simpl in H1. 
    Search wand. 
    (* I need the information on is_in_graph. *)
    assert (p' : rep_type). admit. 
    Exists p. (* This is not true. *) *) *)
Admitted.
*) 

Lemma body_get_unboxed_ordinal :
  semax_body Vprog Gprog
    f_get_unboxed_ordinal
            get_unboxed_ordinal_spec.
Proof. 
    (* TODO: Is this an error? *)
    start_function.
    forward. 
    { entailer!. }
    entailer!.
    rewrite Z.shiftr_div_pow2; try lia. 
    rewrite Int64.shru_div_two_p. 
    simpl. unfold two_p.  simpl. normalize. f_equal. f_equal.
    rewrite (Int64.unsigned_repr_eq 1). simpl. 
    unfold two_power_pos. simpl. unfold Z.pow_pos. simpl.
    (* TODO: Size conditions on z. *)
    Admitted.


 Require Import CertiGraph.CertiGC.forward_lemmas.


(* eval_unop Oneg tint (vint 1) *)



 Lemma data_at_minus1_address_long: forall sh v p,
 data_at sh (if Archi.ptr64 then tulong else tuint)
         v (offset_val (- WORD_SIZE) p) |--
         !! (force_val (sem_add_ptr_long (if Archi.ptr64 then tulong else tuint)
                                         p (eval_unop Oneg tlong (Vlong (Int64.repr 1)))) =
             field_address (if Archi.ptr64 then tulong else tuint) []
                           (offset_val (- WORD_SIZE) p)).
Proof.
intros. unfold eval_unop. simpl. entailer!.
unfold field_address. rewrite if_true by assumption. rewrite offset_offset_val.
simpl. reflexivity.
Qed.

(* replace (Eunop Oneg (Econst_long (Int64.repr (Zpos xH)) tlong) tlong)
  with (Eunop Oneg (Econst_int (Int.repr (Zpos xH)) tint) tint) by admit. *)

Lemma body_get_boxed_ordinal :
  semax_body Vprog Gprog
    f_get_boxed_ordinal
            get_boxed_ordinal_spec.
Proof. 
    start_function.
    unfold full_gc. 
    Intros. 
    sep_apply (spatial_gcgraph.graph_vertex_ramif_stable g v H).
    Intros.
    unfold spatial_gcgraph.vertex_rep. unfold spatial_gcgraph.vertex_at.
    simpl. Intros.
    (* KS: What is the precondition to access at position -1? *)
    Search data_at (tarray _ 1).
    (* sep_apply (data_at_singleton_array (nth_sh g (vgeneration v)) tulong [Z2val (make_header g v)] (Z2val (make_header g v)) (offset_val (-8) (vertex_address g v)) ). *) 
    pose proof (data_at_minus1_address_long (nth_sh g (vgeneration v)) (Z2val (make_header g v)) (vertex_address g v)).
    simpl in H1. 
    sep_apply H1.
    change_compspecs CompSpecs. 
    Intros. 
    assert (writable_share (nth_sh g (vgeneration v))) by admit.
    replace (env_graph_gc.CompSpecs) with CompSpecs in H2 by admit. 
    (* forward. 


    forward. 
    forward. 
    { entailer!. }
    entailer!. *) 
    admit.
    - unfold raw_tag. 
      unfold make_header. 
      destruct (graph_model.vlabel g v). simpl.
      simpl. 
      simple_if_tac. 
      { admit. }
      Search Z.land. 
      f_equal. f_equal.
      assert (255 = Z.ones 8) by reflexivity.
      rewrite H10.
      Search Z.land Z.ones.
      rewrite Z.land_ones; try lia. 
      Search "+" "mod".
      replace (2 ^ 8) with 256 by reflexivity.
      replace (2
      * (2
           * (2
                * (2
                     * (2
                          * (2
                               * (2
                                    * (2
                                         * 
                                         (2 * (2 * Zlength raw_fields))))))))))
      with ( (4 * Zlength raw_fields) * 256) by lia. 
      rewrite Z_mod_plus_full.
    replace ( 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * raw_color)))))))) with (raw_color * 256) by lia.
    rewrite Z_mod_plus_full.
    rewrite Z.mod_small; try rep_lia.
    rewrite Int64.unsigned_repr_eq. rewrite Z.mod_small; try rep_lia. 
    - unfold full_gc. entailer!. 
      Search wand sepcon.
      rewrite <- wand_twice. 
      sep_apply modus_ponens_wand.
      rewrite sepcon_comm.
      sep_apply modus_ponens_wand.
      entailer. 
Admitted.


Lemma body_tag :
  semax_body Vprog Gprog
    f_get_Coq_Init_Datatypes_nat_tag
            tag_spec_S.
Proof. 
    start_function.
    rename H into x_in_graph.
   
    forward_call (rep_type_val g p). 
    cbn in x_in_graph. 
    forward_if. 
    - (* Should be the x <> 0 case. *)
      destruct x. 
      { destruct p; try contradiction.  }

     (* Destruct x_in_graph *)
     destruct x_in_graph as (p'&H1&H2). 
     destruct p; try (now inversion H2).
     simpl.  destruct H2. destruct H2. 
     (* Using get_boxed_ordinal  *)
     forward_call (g, v, roots, sh, ti, outlier, t_info).
     (* Destruct x_in_graph *)
     destruct (graph_model.vlabel g v).
     destruct raw_mark; try (now inversion H3).
     destruct raw_color; try (now inversion H3).
     destruct H3. destruct H4. subst.   
     simpl.
     forward_if (PROP () LOCAL () SEP ()).
     + forward; entailer!. 
       constructor. 
     + contradiction. 
    - destruct x. 
      2 : { destruct x_in_graph. destruct H0. destruct p; try contradiction. simpl in H.
        unfold vertex_address in H. unfold offset_val in H. simpl in H. 
        destruct (gen_start g (vgeneration v)); try inversion H. 
      }
      destruct p; try inversion x_in_graph.
      simpl.
      unfold odd_Z2val.
      assert (z = 0).
      { (* TODO: In our specification has to be the other way around. *) admit. }
      subst. autorewrite with norm.

      forward_call (1).
      + entailer!. 
      + unfold Z.shiftr. simpl.
      forward_if (PROP () LOCAL () SEP ()). 
      * forward; entailer!. 
        constructor. 
      * contradiction. 
Admitted.

