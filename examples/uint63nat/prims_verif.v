Require Import VeriFFI.examples.uint63nat.prog.

Require Import ZArith.
Require Import Psatz.

Require Import VeriFFI.verification.specs_general.

Require Import VeriFFI.generator.all.

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
Require Import VeriFFI.examples.uint63nat.prims. 

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

Print GCGraph.thread_info.
Print outlier_t.
Print full_gc.
Print gc_condition_prop.

(* Same as in UVRooster - TODO: encode_Z as relation to fit our general scheme *)
Definition encode_Z (x: Z): Z := x * 2 + 1.
Definition min_signed: Z := - 2^62.
Definition max_signed: Z := 2^62 - 1.


(* Delete fun_info everywhere. *)        
Definition  uint63_to_nat_spec :  ident *  funspec := 
   DECLARE _uint63_to_nat  
   WITH gv : globals, g : graph, roots : roots_t, sh : share, n: nat,
        ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
   PRE  [ tptr (Tstruct _thread_info noattr ),  (talignas 3%N (tptr tvoid)) ]
      PROP ( (Z.of_nat n) < headroom t_info ; (* KS: 2 times this *)
            writable_share sh; 
            min_signed <= encode_Z (Z.of_nat n) <= max_signed
            )
      (PARAMSx [ti; Vlong (Int64.repr (encode_Z (Z.of_nat n)))]
      (GLOBALSx nil
      (SEPx (full_gc g t_info roots outlier ti sh :: nil))))
   POST [ (talignas 3%N (tptr tvoid)) ]
     EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info),
       PROP (@is_in_graph nat (@in_graph nat _) g' n p' ;
             gc_graph_iso g roots g' roots)
       RETURN  (rep_type_val g' p')
       SEP (full_gc g' t_info' roots outlier ti sh) . 


Definition  uint63_from_nat_spec :  ident *  funspec := 
DECLARE _uint63_from_nat  
WITH gv : globals, g : graph, roots : roots_t, sh : share, n: nat, p : rep_type,
        ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
PRE  [ (talignas 3%N (tptr tvoid)) 
]
    PROP ( encode_Z (Z.of_nat n) <= max_signed; 
            @is_in_graph nat (@in_graph nat _) g n p ;
            writable_share sh)
    (PARAMSx [ rep_type_val g p]
    (GLOBALSx nil
    (SEPx (full_gc g t_info roots outlier ti sh :: nil))))
POST [ (talignas 3%N (tptr tvoid)) ]
    PROP ()
    RETURN  (Vlong (Int64.repr (encode_Z (Z.of_nat n))))
    SEP (full_gc g t_info roots outlier ti sh). 


Definition nat_get_desc (x : nat) : constructor_description := 
match x with 
| O => (@desc _ O _)
| S n =>  (@desc _ S _)
end.
 
Inductive nat_has_tag_prop : nat -> constructor_description -> Prop := 
| tagO : nat_has_tag_prop O (@desc _ O _)
| tagS n : nat_has_tag_prop (S n) (@desc _ S _).

Check @in_graph.

Variable X_get_desc : forall (X_ : Type) (R_: Rep X_) (x : X_), constructor_description. 

Variable X_has_tag_prop : forall (X_ : Type) (R_: Rep X_) (x : X_), constructor_description -> Prop.


Print full_gc.
Print gc_condition_prop.

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

Print rep_type_val.

 Definition args_spec_S (c : constructor_description) (n : nat) : funspec := 
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
            in_graphs g (ctor_reific c) xs [p']
        )
    RETURN  ( rep_type_val g p ) 
    SEP (data_at sh (Tstruct _Coq_Init_Datatypes_S_args noattr) (rep_type_val g p') (rep_type_val g p);
     data_at sh (Tstruct _Coq_Init_Datatypes_S_args noattr) (rep_type_val g p') (rep_type_val g p) -* full_gc g t_info roots outlier ti sh). 

     (* Have an array at this position. *)

     (* KS: Name for Pattern for the focussing. *)


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
        in_graphs g (ctor_reific c) xs ps'
    )
RETURN  ( rep_type_val g p ) 
SEP (data_at sh (Tstruct args_type noattr) (map (rep_type_val g) ps') (rep_type_val g p)
    * (data_at sh (Tstruct args_type noattr) (map (rep_type_val g) ps') (rep_type_val g p) -* full_gc g t_info roots outlier ti sh)). 
*) 

Definition args_make_Coq_Init_Datatypes_nat_S_spec : ident * funspec :=
DECLARE _get_Coq_Init_Datatypes_S_args
        (args_spec_S (@desc _ S _) 1).
    

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


Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := [uint63_from_nat_spec; 
                    uint63_to_nat_spec; 
                    tag_spec_S; alloc_make_Coq_Init_Datatypes_nat_O_spec; alloc_make_Coq_Init_Datatypes_nat_S_spec; args_make_Coq_Init_Datatypes_nat_S_spec ] .

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



Lemma body_uint63_from_nat_spec :
  semax_body Vprog Gprog
             f_uint63_from_nat
             uint63_from_nat_spec.
Proof.
    start_function. 
    forward. replace (match p with
    | repZ y => odd_Z2val y
    | repOut p0 => GC_Pointer2val p0
    | repNode v => vertex_address g v
    end) with (rep_type_val g p) by reflexivity. 
    forward.
    (* Issue report.
    TODO: What does this error tell me? Where should I look? *)
    forward_call (gv, g, p, n, roots, sh, ti, outlier, f_info, t_info). 
    forward_while ( EX   (m : nat) p',
        PROP ( is_in_graph g (n - m)%nat p';        
              nat_has_tag_prop (n - m)%nat (nat_get_desc (n-m)%nat))
        LOCAL (temp _t (Vint (Int.repr (Z.of_nat (ctor_tag (nat_get_desc (n - m))))));
        temp _i (Vlong (Int64.repr (Int.signed (Int.repr (Z.of_nat m))))); temp _temp (rep_type_val g p');
        temp _n (rep_type_val g p))  SEP (full_gc g t_info roots outlier ti sh)
    ). 
    - (* Before the loop. *)
      Exists 0%nat.  Exists p. 
      assert ((n -0)%nat = n)  as -> by lia; eauto. 
      entailer!. 
    - (* Condition *)
      entailer!. 
    - (* During the loop. *)
      forward.  autorewrite with norm.
      (* Todo: With HRE. *)
      assert (exists nm', S nm' = (n - m)%nat) as (nm'&eq_nm') by admit. 
      forward_call (gv, g, p', (nm'; tt), roots, sh, ti, outlier, f_info, t_info). 
      { rewrite <- eq_nm' in H1. apply H1. }
      Intros p_nm'.
      autorewrite with norm in *. 
      forward.
      { entailer!. admit. } (* structural stuff, should be easy *)
      forward_call (gv, g, p_nm', nm', roots, sh, ti, outlier, f_info, t_info).
         + sep_apply wand_frame_elim'; entailer!.
         +  admit. (* with H2 - same unfolding problem... *)
         + forward.
           autorewrite with norm. 
           Exists (S m, p_nm').
           entailer!. 
           split3. 
           * (* with H2 - same unfolding problem... *)
             admit. 
           * assert (nm' = n - S m)%nat as -> by lia. eauto.
           * split. 
            --  repeat f_equal. lia.
            -- f_equal. f_equal. admit. (*  autorewrite with norm.  lia.  *)
    - (* After the loop. *)
      assert (n = m)%nat by admit. subst.
      forward.
      { entailer!. }
      entailer!.  
      Search Int64.shl.
      autorewrite with norm.
      f_equal. unfold encode_Z. 
      Search Int64.shl Int64.one. unfold encode_Z in H. unfold Int64.max_signed in H. 
      autorewrite with norm. 
      Search Int64.shl. 
      rewrite Int64.shl_mul_two_p. autorewrite with norm. unfold two_p. 
      unfold two_power_pos. 
      rewrite !Int.signed_repr; try rep_lia. 
      f_equal. 
      split; try rep_lia. unfold max_signed in *. unfold Int.max_signed. clear - H. simpl in *.
      Locate "*".
      Search Z.mul.
      rewrite Z.mul_comm in H. 
      Search Z.le Z.mul.

      (* Todo: Work on postcondition. *)
     admit.
Admitted.


Lemma body_uint63_to_nat_spec :
  semax_body Vprog Gprog
             f_uint63_to_nat
             uint63_to_nat_spec.
Proof. 
  start_function.
  forward. unfold full_gc. Intros. 
  forward_call (gv, g). 
   assert ( Vlong (Int64.shru (Int64.repr (encode_Z (Z.of_nat n))) (Int64.repr (Int.unsigned (Int.repr 1)))) = Vlong (Int64.repr  (Z.of_nat n)))  as ->.
    { unfold encode_Z. 
    autorewrite with norm. Search Int64.shru . rewrite Int64.shru_div_two_p. 
    unfold two_p.  Search Int64.unsigned Int64.repr. simpl. 
    
    admit. (* TODO *)  } 
  (*   Print bool_type. *)

  forward_while 
  (EX v : rep_type, EX m : nat, EX g' : graph, EX (t_info : GCGraph.thread_info),
  PROP (is_in_graph g' m v; (m <= n)%nat; Z.of_nat (n - m) < headroom t_info; 
  gc_graph_iso g roots g' roots)
   LOCAL (temp _temp (rep_type_val g' v);
   temp _i (Vlong (Int64.repr (Z.of_nat (n - m))));
   temp _tinfo ti; temp _t (Vlong (Int64.repr (Z.of_nat n))))
   SEP (full_gc g' t_info roots outlier ti sh)
  ). 

  - (* Before the while *)
    Intros v. Exists v. Exists 0%nat. Exists g. Exists t_info. entailer!. 
    + split.
      * apply gc_graph_iso_refl.
      * repeat f_equal. lia.
    +  unfold full_gc. entailer!. 
  - (* Valid condition  *)
    entailer!. 
  - (* During the loop *)
    assert (n - m <> 0)%nat.
    {  destruct (n-m)%nat eqn:EQ_mn; eauto. 
      simpl in HRE. normalize in HRE. 
      Print typed_true. unfold typed_true in HRE. simpl in HRE. 
      unfold Int64.zero in HRE. unfold Int64.eq in HRE. 
      if_tac in HRE; eauto. simpl in HRE. congruence.
    }
    forward_call (gv, g', [v], (m%nat; tt) , roots, sh, ti, outlier, f_info, t_info0). 
    { (* Requiring to unfold - TODO: Generate example file for Joomy. *)
       admit. }
    Intros v'.  destruct v' as ((v'&g'')&ti').
    unfold fst, snd in *. 
     forward. 
     Exists (v', S m, g'', ti').
     entailer!. 
    split; eauto. 
     + eapply gc_graph_iso_trans; eauto.  
     + repeat f_equal.  lia.  
  - forward. 
    { unfold full_gc. entailer!.  }
  
    Exists v. Exists g'. Exists t_info0.
    entailer!. 

    enough (n- m = 0)%nat. 
    { assert (n = m) by lia. subst. eauto. }
    red in HRE.  
    unfold strict_bool_val in HRE. simpl in HRE. 
unfold Int64.zero in HRE. 
    Search (Int64.eq (Int64.repr _) (Int64.repr _)).
    clear -HRE.

    destruct (n-m)%nat eqn:EQ_mn; eauto. 
    simpl in HRE. normalize in HRE. 
    unfold typed_false in HRE. simpl in HRE. 
    unfold Int64.eq in HRE. if_tac in HRE; simpl in *; try congruence. 
    revert H6. Search Int64.unsigned Int64.zero. 
    rewrite Int64.unsigned_zero. 
  admit. 
Admitted.




Lemma body_alloc_make_Coq_Init_Datatypes_nat_S' :
  semax_body Vprog Gprog
             f_alloc_make_Coq_Init_Datatypes_nat_S
             alloc_make_Coq_Init_Datatypes_nat_S_spec.
Proof. 
  unfold alloc_make_Coq_Init_Datatypes_nat_S_spec.
  assert (H := body_alloc_make_Coq_Init_Datatypes_nat_S ).
  assert (H' := general_subsumption).
  apply (@semax_body_funspec_sub) with (phi := n_arguments 1024 1).
  - apply H. 
  - Print constructor_description.
  
  specialize (H' (0% nat) (1%nat) description_S).
  apply H'; try lia. 



  unfold X_in_graph_cons. destruct description_S. 
  cbn. 
  intros. 
  cbn. 



  admit.  
  (* Ask Joomy. *)

  - simpl. repeat constructor; simpl.  all: intuition eauto; try congruence.
  all: try inversion H1; try inversion H0. 
Admitted.



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

Lemma body_args :
  semax_body Vprog Gprog
             f_get_Coq_Init_Datatypes_S_args
             args_make_Coq_Init_Datatypes_nat_S_spec .
Proof. 
    start_function. 
    forward. 
    { unfold full_gc. entailer!. admit.  }
    Search wand. 
Admitted.


Lemma body_alloc_make_Coq_Init_Datatypes_nat_S' :
  semax_body Vprog Gprog
             f_alloc_make_Coq_Init_Datatypes_nat_S
             alloc_make_Coq_Init_Datatypes_nat_S_spec.
Proof. 
  unfold alloc_make_Coq_Init_Datatypes_nat_S_spec.
  assert (H := body_alloc_make_Coq_Init_Datatypes_nat_S ).
  assert (H' := geneeral_subsumption).
  apply (@semax_body_funspec_sub) with (phi := n_arguments 1024 1).
  - apply H. 
  - Search constructor_description.
   
  specialize (H' (0% nat) (1%nat) (@desc _ S _)).
  apply H'; try lia.  
  unfold X_in_graph_cons.
  
  2 : { eapply H'.  }