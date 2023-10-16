Require Import VeriFFI.examples.uint63nat.prog.
Require Import ZArith.
Require Import Psatz.
Require Export VeriFFI.verification.specs_general.
Require Export VeriFFI.generator.Rep.

Obligation Tactic := gen.
MetaCoq Run (gen_for nat).
MetaCoq Run (gen_for bool).

MetaCoq Run (desc_gen S).
MetaCoq Run (desc_gen O).

Require Export VST.floyd.proofauto.
Require Export CertiGraph.CertiGC.GCGraph.
From VeriFFI Require Export library.base_representation library.meta verification.graph_add verification.specs_library.

Require Export VeriFFI.examples.uint63nat.Verif_prog_general.
Require Export VeriFFI.examples.uint63nat.prims. 

(* Specific alloc*)

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

(* General specifications for uint63/nat *)

Definition alloc_make_Coq_Init_Datatypes_nat_S_spec : ident * funspec :=
  DECLARE _alloc_make_Coq_Init_Datatypes_nat_S
          (alloc_make_spec_general (@desc _ S _) 1).        

(* KS: Use *)          
Definition nat_get_desc (x : nat) : ctor_desc := 
match x with 
| O => (@desc _ O _)
| S n =>  (@desc _ S _)
end.
  
Inductive nat_has_tag_prop : nat -> ctor_desc -> Prop := 
| tagO : nat_has_tag_prop O (@desc _ O _)
| tagS n : nat_has_tag_prop (S n) (@desc _ S _).
            
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

Definition args_spec_S' (c : ctor_desc) (n : nat) : funspec := 
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
  POST [ tptr ((tarray int_or_ptr_type 1)) (* tarray int_or_ptr_type 1 *)  ]
  EX  (p' : rep_type) (sh' : share),
  PROP (  
          is_in_graph g x p'
      )
  RETURN  ( rep_type_val g p ) 
  SEP (data_at sh' (tarray int_or_ptr_type 1) [rep_type_val g p'] (rep_type_val g p);
      data_at sh' (tarray int_or_ptr_type 1) [rep_type_val g p'] (rep_type_val g p) -* full_gc g t_info roots outlier ti sh). 
  

Definition args_make_Coq_Init_Datatypes_nat_S_spec : ident * funspec :=
DECLARE _get_args
        (args_spec_S' (@desc _ S _) 1).

(* Same as in UVRooster - TODO: encode_Z as relation to fit our general scheme *)
Definition encode_Z (x: Z): Z := x * 2 + 1.
Definition min_signed: Z := - 2^62.
Definition max_signed: Z := 2^62 - 1.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.


Instance Discrimination_nat : Discrimination nat. 
Admitted.

Instance Rep_conditional  (A : Type) `(InGraph_A : InGraph A) 
`(Discrimination_A : Discrimination A) : Rep A := 
{| in_graph := InGraph_A ; discrimination := Discrimination_A |}.

Definition uint63_to_nat_spec :  ident *  funspec := 
   DECLARE _uint63_to_nat  
   WITH gv : globals, g : graph, roots : roots_t, sh : share, n: nat,
        ti : val, outlier : outlier_t, t_info : GCGraph.thread_info
   PRE  [ tptr (Tstruct _thread_info noattr ),  (talignas 3%N (tptr tvoid)) ]
      PROP ( 2 * (Z.of_nat n) < headroom t_info ; 
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
       SEP (full_gc g' t_info' roots outlier ti sh). 

Definition uint63_from_nat_spec :  ident *  funspec := 
DECLARE _uint63_from_nat  
WITH gv : globals, g : graph, roots : roots_t, sh : share, n: nat, p : rep_type,
        ti : val, outlier : outlier_t, t_info : GCGraph.thread_info
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
    (* KS: Existential *)

(* Function Spec

- This is the definition of a Coq function from X to Y/the specification that hopefully CertiCoq
should be able to guarantee. 
- The function specification is dependent on (representable) input and output types and a representable 
environment type. 
- The function yields the right result if given an environment. 
    - TODO: Don't we rather want that this is...

- What I changed: changed it to iso.
*)

Definition fun_spec X Y (In_Graph_X : InGraph X) (In_Graph_Y : InGraph Y) 
	   A (In_Graph_A : InGraph A) (env : A) (f : A -> X -> Y) :  funspec := 
  WITH
	 (* general info on the garbage collector graph *) 
	 g : graph, roots : roots_t, sh : share, ti : val,
     outlier : outlier_t, t_info : GCGraph.thread_info,
	 (* function-specific *)
    x: X, p_x : rep_type, p_env : rep_type
PRE [thread_info, int_or_ptr_type, int_or_ptr_type]
  PROP (@is_in_graph X In_Graph_X g x p_x; 
				is_in_graph g env p_env
				)
  PARAMS (ti; rep_type_val g p_env; rep_type_val g p_x)
  GLOBALS ()
  SEP (full_gc g t_info roots outlier ti sh)
POST [ int_or_ptr_type ]
  EX (g' : graph) (t_info' : GCGraph.thread_info) (res' : rep_type) (roots' : roots_t),
  PROP (@is_in_graph Y In_Graph_Y g' (f env x) res'; 
		gc_graph_iso g roots g' roots'
		 )
  RETURN (rep_type_val g' res')
  SEP (full_gc g' t_info' roots' outlier ti sh).

(* This means that for any Coq function f : X -> Y, 
   CertiCoq has to provide the above lemma for an arbitrary A, InGraph_A, env : A. 
*)

    Record closure  := { 
            src_type : Type;
            src_repr : InGraph src_type;
            trg_type : Type;
            trg_repr: InGraph trg_type;
            env_type : Type;
            env_repr : InGraph env_type; 
            env : env_type; 
            fct : env_type -> src_type -> trg_type; 
            x : src_type (* TODO: NOT IN HERE *) 
    }.


 (*  Record closure X Y In_Graph_X In_Graph_Y := 
      {A | env : A, In_Graph_A : InGraph A; 
            f : A -> X -> Y; 
  fun_spec X Y In_Graph_X In_Graph_Y A In_Graph_A env f}. *)


  (* TODO: This would mean that I have to give on the closure... *)
  Definition call_spec : funspec := 
	WITH (* General graph content *)
	    g : graph, roots : roots_t, sh : share, outlier : outlier_t,t_info : GCGraph.thread_info, ti : val,
	    (* Specific to this function *)
        (* X_ : {X : Type | InGraph X}, (* Y : Type, InGraph_Y : InGraph Y,
		c: closure X Y In_Graph_X In_Graph_Y, *)
		x : X, *) 
        c : closure, 
        p_c : val,
        p_env : rep_type, 
        p_x : rep_type,
		code_p : rep_type
PRE [ thread_info, int_or_ptr_type, int_or_ptr_type ]
	PROP (@is_in_graph _ (src_repr c) g (x c) p_x; 	
				(* is_in_graph g closure code_p; *) 
				@is_in_graph _ (env_repr c) g (env c) p_env )
	PARAMS (ti; p_c; rep_type_val g p_x) 
	GLOBALS ()
	SEP (full_gc g t_info roots outlier ti sh; 
	func_ptr' (fun_spec _ _ (src_repr c) (trg_repr c) _ (env_repr c) (env c) (fct c)) (rep_type_val g code_p)
) 
POST [ int_or_ptr_type ]
	EX (g' : graph)(t_info' : GCGraph.thread_info) (p: rep_type) (roots': roots_t),
	PROP ( @is_in_graph _ (trg_repr c) g' (fct c (env c) (x c)) p;
				gc_graph_iso g roots g' roots' )
	RETURN (rep_type_val g p)
	SEP (full_gc g' t_info' roots outlier ti sh).


Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog := [ tag_spec_S; alloc_make_Coq_Init_Datatypes_nat_O_spec; alloc_make_Coq_Init_Datatypes_nat_S_spec
                      ; args_make_Coq_Init_Datatypes_nat_S_spec ;  uint63_to_nat_spec ; uint63_from_nat_spec; 
                      call_spec
                      ] .
