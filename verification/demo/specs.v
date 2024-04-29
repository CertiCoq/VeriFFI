(** * Specification of alloc functions

Kathrin Stark, 2020. 

This file contains the specification for the alloc functions. It consists of: 
- Library Definitions 
- Function specifications for bool 
- Function specifications for nat 
 *)

From VC Require Export graphCRep. 
From VC Require Export graph_add.
From VC Require Export glue.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.


Inductive arg_description :=
(* the type parameters in parametric polymorphism which 
doesn't have an intermediate representation in the C code, but is needed later, 
e.g. A in [list A] *)
 | TYPEPARAM  : (representable_X -> arg_description) -> arg_description
(* non-type parameters of a type, n in [n < m] *)
 | PARAM  : forall X : Type, (X -> arg_description) -> arg_description
(* index, represented in memory, e.g. the index of a vector *) 
 | INDEX  : (representable_X -> arg_description) -> arg_description
 (* non-dependent version of arguments, e.g. for X/list X of cons *)
 | ARG : representable_X -> arg_description -> arg_description
 (* dependent version, see positive_nat_list *)
 | DEPARG : (representable_X -> arg_description) -> arg_description
(* the end type, e.g. list X for cons : forall X, X -> list X -> **list X** *)
 | RES  : representable_X -> arg_description.



(** ** 1. Library definitions *)

(** Custom types *)
Definition thread_info_type := Tstruct _thread_info noattr.
Definition thread_info := tptr thread_info_type. 

Fixpoint rep_type_val (g : graph) (x : rep_type) : val :=
match x with 
| repZ y => odd_Z2val y
| repOut p => GC_Pointer2val p
| repNode v => vertex_address g v
end. 

Check list_in_graph.

(** *** 1b. Shadow Stack *) 

(** Assumptions on the shadow stack - TODO: REMOVE?

 Connection between the old and new graph.
In principal, I could also directly give the graph we are talking about.
Not sure which is the better specification. 
*)
Variable shadow_stack_type : Type. 

(** This might be some isomorphism property.
Variable rep_shadow_stack : graph -> shadow_stack_type -> Prop.

Lemma add_node_rep_shadow_stack g v r e args : 
  rep_shadow_stack g args -> rep_shadow_stack (add_node g v r e) args. 
Admitted. *)

(** ** 1c. Graph Conditions *)

(** Specification for the alloc_S function. *)

Definition array_type := int_or_ptr_type. 

(** Propositional conditions from the garbage collector specification and getting the isomorphism property for the garbage collector: 
The thread_info has to be a new one, roots and outlier stay preserved *)
Definition gc_condition_prop g t_info roots outlier := 
graph_unmarked g /\ no_backward_edge g /\ no_dangling_dst g /\ ti_size_spec t_info (** From garbage_collect_condition, removed that roots and finfo are compatible. *)
/\ safe_to_copy g 
/\ graph_thread_info_compatible g t_info /\ outlier_compatible g outlier /\ roots_compatible g outlier roots
/\ gc_correct.sound_gc_graph g /\ copy_compatible g.

Definition space_rest_rep (sp: space): mpred :=
  if (Val.eq sp.(space_start) nullval)
  then emp
  else data_at_ (space_sh sp)
                (tarray int_or_ptr_type (sp.(total_space) - sp.(used_space)))
                (offset_val (WORD_SIZE * used_space sp) sp.(space_start)).

Definition heap_rest_rep (hp: heap): mpred :=
  iter_sepcon  space_rest_rep hp.(spaces).

(* Taken from Shengyi to get the right GC *) 
Definition before_gc_thread_info_rep (sh: share) (ti: CertiGraph.CertiGC.GCGraph.thread_info) (t: val) :=
  let nursery := heap_head ti.(ti_heap) in
  let p := nursery.(space_start) in
  let n_lim := offset_val (WORD_SIZE * nursery.(total_space)) p in
  (data_at sh thread_info_type
          (offset_val (WORD_SIZE * nursery.(used_space)) p,
           (n_lim, (ti.(ti_heap_p), ti.(ti_args)))) t *
  heap_struct_rep
    sh ((p, (Vundef, n_lim))
          :: map space_tri (tl ti.(ti_heap).(spaces))) ti.(ti_heap_p) *
  heap_rest_rep ti.(ti_heap))%logic.

Definition full_gc g t_info roots outlier ti sh := 
  (outlier_rep outlier * before_gc_thread_info_rep sh t_info ti * ti_token_rep t_info * graph_rep g && !!gc_condition_prop g t_info roots outlier)%logic. 

(** ** 2. Function specifications Bool  *)

Definition make_bool_true_spec : ident * funspec :=
 DECLARE _make_Coq_Init_Datatypes_bool_true
  WITH gv : globals, g : graph
  PRE  [ ] 
       PROP ()
       PARAMS ()
       GLOBALS ()
       SEP (graph_rep g)
  POST [ tulong ]  
     EX (x : rep_type),
     PROP(bool_in_graph g true x) (* TODO: Would be better if I can compute x? And I think I should be able to do so from true. In this case, x is 1.
 In the case of a pointer, it could be both sth in or outside the graph.                        
Abstraction or not abstraction?
    *)
     LOCAL (temp ret_temp (rep_type_val g x)) 
     SEP (graph_rep g).

(** ** 3. Function specifications Nat *)

Definition make_nat_0_spec : ident * funspec :=
 DECLARE _make_Coq_Init_Datatypes_nat_O
  WITH gv : globals, g : graph
  PRE  [ ] 
       PROP ()
       PARAMS ()
       GLOBALS ()
       SEP (graph_rep g)
  POST [ tulong ]  
     EX (x : rep_type), 
     PROP (nat_in_graph g O x) 
     LOCAL (temp ret_temp (rep_type_val g x)) 
     SEP (graph_rep g).


Definition alloc_make_nat_S_spec : ident * funspec :=
 DECLARE _alloc_make_Coq_Init_Datatypes_nat_S
  WITH gv : globals, g : graph, p : rep_type, n : nat, roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
  PRE  [thread_info, tulong] 
       PROP (nat_in_graph g n p;
             writable_share sh
             )
       PARAMS (ti;
              rep_type_val g p)
       GLOBALS ()
       SEP ( full_gc g t_info roots outlier ti sh ) 
  POST [ tptr tulong ]  
     EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info), 
     PROP (nat_in_graph g' (S n) p';
           gc_graph_iso g roots g' roots
         ) 
   RETURNS  (rep_type_val g' p')
     LOCAL (temp ret_temp (rep_type_val g' p'))
     SEP (full_gc g' t_info' roots outlier ti sh). 


(** ** Representable Type Class *)

Record representable_X  := 
  { X_type : Type; 
    X_in_graph : graph -> X_type -> rep_type -> Prop;
    X_has_v : forall g n v, X_in_graph g n (repNode v) -> graph_has_v g v;
    X_monotone : forall g to lb e n p, add_node_compatible g (new_copied_v g to) e -> graph_has_gen g to -> X_in_graph g n p -> X_in_graph (add_node g to lb e) n p
    }.

Existing Class representable_X.


(** ** 4. Function Specifications Lists *)

Require Export VST.progs.conclib.

 Definition alloc_make_list_nil_spec  : ident * funspec :=
 DECLARE _make_Coq_Init_Datatypes_list_nil 
  WITH graph_X_var : representable_X, gv : globals, g : graph
  PRE  [ tulong ] 
       PROP ()
       PARAMS ()
       GLOBALS ()
       SEP (graph_rep g)
  POST [ tulong ]  
     EX (x : rep_type), 
     PROP (list_in_graph (X_in_graph graph_X_var) g nil x) 
     LOCAL (temp ret_temp (rep_type_val g x)) 
     SEP (graph_rep g).

(* 
 Definition make_list_nil_spec (* CHANGED *) (*  (X : Type) (X_in_graph : graph -> X -> rep_type -> Prop) *)  (* CHANGED *) : ident * funspec :=
(* ALL X: Type, (* TODO: NatDed (ident * funspec *) *) 
 DECLARE _make_Coq_Init_Datatypes_list_nil (* CHANGED *) 
  WITH gv : globals, g : graph
  PRE  [ ] 
       PROP ()
       PARAMS ()
       GLOBALS ()
       SEP (graph_rep g)
  POST [ tulong ]  
     EX (x : rep_type), 
     PROP (list_in_graph (X_in_graph graph_X_var) g nil x) (* CHANGED *) 
     LOCAL (temp ret_temp (rep_type_val g x)) 
     SEP (graph_rep g). *)



Locate "WITH".
(* "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" := 
 NDmk_funspec (pair (cons u .. (cons v nil) ..) tz) cc_default (prod t1 t2)
  (fun x => match x with
            | pair x1 x2 => P
            end) (fun x => match x with
                           | pair x1 x2 => Q
                           end) : funspec_scope (default interpretation) *) 

Check NDmk_funspec.
(* NDmk_funspec
     : compcert_rmaps.typesig ->
       calling_convention ->
       forall A : Type, (A -> argsEnviron -> mpred) -> (A -> environ -> mpred) -> funspec *) 


Locate "DECLARE".
(* Notation
"'DECLARE' x s" := pair (x : ident) (s : funspec) (default interpretation) *) 

Check mk_funspec.

(* Definition pre := 
fun x => match x with 
    | pair (    
PROP (X_in_graph graph_X_var g x p_x;
            list_in_graph (X_in_graph graph_X_var) g xs p_xs; (* CHANGED *) 
             writable_share sh
             )
       PARAMS (ti; (* CHANGED *) 
              rep_type_val g p_x;
              rep_type_val g p_xs)
       GLOBALS ()
       SEP ( full_gc g t_info roots outlier ti sh ) 

Definition test_funspec : funspec := 
NDmk_funspec cc_default (

Definition alloc_make_list_cons_spec : ident * funspec :=
DECLARE _alloc_make_Coq_Init_Datatypes_list_cons test_funspec. 


  WITH gv : globals, g : graph, p_x : rep_type, x : X, p_xs : rep_type, xs : list X, (* CHANGED *)  roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
  PRE  [thread_info, tulong, tulong]  (* CHANGED *)
       PROP (X_in_graph graph_X_var g x p_x;
            list_in_graph (X_in_graph graph_X_var) g xs p_xs; (* CHANGED *) 
             writable_share sh
             )
       PARAMS (ti; (* CHANGED *) 
              rep_type_val g p_x;
              rep_type_val g p_xs)
       GLOBALS ()
       SEP ( full_gc g t_info roots outlier ti sh ) 
  POST [ tptr tulong ]  
     EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info), 
     PROP (list_in_graph (X_in_graph graph_X_var) g' (x :: xs) p'; (* CHANGED *)
           gc_graph_iso g roots g' roots
         ) 
(*     RETURNS  (rep_type_val g' p'), TOOD: Update to newest version. *)
     LOCAL (temp ret_temp (rep_type_val g' p'))
     SEP (full_gc g' t_info' roots outlier ti sh). 
 *)



(*  Q : {t : type & ((reptype t -> Prop) * hist (reptype t) * reptype t)%type} *) 

Definition graph_X_var  (args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type })  := let (graph_X_var, args') := args in graph_X_var. 

Definition x (args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type }) : X_type (graph_X_var args). 
Proof.
  destruct args, p. exact x0.
Defined.

Definition xs (args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type }) : list (X_type (graph_X_var args)). 
Proof.
  destruct args, p. exact l.
Defined.

(* TODO: let...in didn't work... not sure there is a more elegant solution *) 
 Definition alloc_make_list_cons_spec : ident * funspec :=
DECLARE _alloc_make_Coq_Init_Datatypes_list_cons 
  WITH args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type },  gv : globals, g : graph, p_x : rep_type, p_xs : rep_type, roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
  PRE  [thread_info, tulong, tulong] 
       PROP (X_in_graph (graph_X_var args) g (x args) p_x;
            list_in_graph (X_in_graph (graph_X_var args)) g (xs args) p_xs;
             writable_share sh
             )
       PARAMS (ti; 
              rep_type_val g p_x;
              rep_type_val g p_xs)
       GLOBALS ()
       SEP ( full_gc g t_info roots outlier ti sh ) 
  POST [ tptr tulong ]  
     EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info), 
     PROP (list_in_graph (X_in_graph (graph_X_var args)) g' ((x args) :: (xs args)) p'; 
           gc_graph_iso g roots g' roots
         ) 
(*     RETURNS  (rep_type_val g' p'), TOOD: Update to newest version. *)
     LOCAL (temp ret_temp (rep_type_val g' p'))
     SEP (full_gc g' t_info' roots outlier ti sh). 


 Definition alloc_make_record_general_spec  :  funspec :=
  WITH args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type },  gv : globals, g : graph, p_x : rep_type, p_xs : rep_type, roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
  PRE  [thread_info, tulong, tulong] 
       PROP (X_in_graph (graph_X_var args) g (x args) p_x;
            list_in_graph (X_in_graph (graph_X_var args)) g (xs args) p_xs;
             writable_share sh
             )
       PARAMS (ti; 
              rep_type_val g p_x;
              rep_type_val g p_xs)
       GLOBALS ()
       SEP ( full_gc g t_info roots outlier ti sh ) 
  POST [ tptr tulong ]  
     EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info), 
     PROP (list_in_graph (X_in_graph (graph_X_var args)) g' ((x args) :: (xs args)) p'; 
           gc_graph_iso g roots g' roots
         ) 
(*     RETURNS  (rep_type_val g' p'), TOOD: Update to newest version. *)
     LOCAL (temp ret_temp (rep_type_val g' p'))
     SEP (full_gc g' t_info' roots outlier ti sh). 


Definition funspec_two :=
WITH args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type },  gv : globals, g : graph, p_x : rep_type, p_xs : rep_type, roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
  PRE  [thread_info, tulong, tulong] 
       PROP (X_in_graph (graph_X_var args) g (x args) p_x;
            list_in_graph (X_in_graph (graph_X_var args)) g (xs args) p_xs;
             writable_share sh
             )
       PARAMS (ti; 
              rep_type_val g p_x;
              rep_type_val g p_xs)
       GLOBALS ()
       SEP ( full_gc g t_info roots outlier ti sh ) 
  POST [ tptr tulong ]  
     EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info), 
     PROP (list_in_graph (X_in_graph (graph_X_var args)) g' ((x args) :: (xs args)) p'; 
           gc_graph_iso g roots g' roots
         ) 
(*     RETURNS  (rep_type_val g' p'), TOOD: Update to newest version. *)
     LOCAL (temp ret_temp (rep_type_val g' p'))
     SEP (full_gc g' t_info' roots outlier ti sh).

(*
Lemma help : funspec_sub (snd alloc_make_list_cons_spec) funspec_two.
Proof.
  do_funspec_sub.  destruct w. repeat destruct p.
   Intros. normalize.
  


Exists (s0).

  simpl. entailer!. *)


(* Original non-dependent one *) 


(* Variable graph_X_var : representable_X. 
Definition X := X_type graph_X_var. 

Variable blub : nat * nat. 

Definition alloc_make_list_cons_spec (* CHANGED *) (* (X : Type) (X_in_graph : graph -> X -> rep_type -> Prop) *) (* CHANGED *)  : ident * funspec :=
DECLARE _alloc_make_Coq_Init_Datatypes_list_cons (* CHANGED *) 
  WITH gv : globals, g : graph, p_x : rep_type, x : X, p_xs : rep_type, xs : list X, (* CHANGED *)  roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
  PRE  [thread_info, tulong, tulong]  (* CHANGED *)
       PROP (X_in_graph graph_X_var g x p_x;
            list_in_graph (X_in_graph graph_X_var) g xs p_xs; (* CHANGED *) 
             writable_share sh
             )
       PARAMS (ti; (* CHANGED *) 
              rep_type_val g p_x;
              rep_type_val g p_xs)
       GLOBALS ()
       SEP ( full_gc g t_info roots outlier ti sh ) 
  POST [ tptr tulong ]  
     EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info), 
     PROP (list_in_graph (X_in_graph graph_X_var) g' (x :: xs) p'; (* CHANGED *)
           gc_graph_iso g roots g' roots
         ) 
(*     RETURNS  (rep_type_val g' p'), TOOD: Update to newest version. *)
     LOCAL (temp ret_temp (rep_type_val g' p'))
     SEP (full_gc g' t_info' roots outlier ti sh). *) 

Print representable_X.

Fixpoint getTuple (XS : list representable_X) : Type := 
  match XS with 
  | nil => unit
  | cons X XS => X_type X * getTuple XS
end.

Record constructor_description := 
{ name : ident;
 (*  pms : list Type;  *) 
  args : list representable_X; 
  res : representable_X; 
  ctr : getTuple args -> X_type res
}.

(* Experiments with vectors *)
Inductive vector (A : Type) : nat -> Type :=
     vnil : vector A 0%nat | vcons : A -> forall n : nat, vector A n -> vector A (S n).

Variable _alloc_make_Coq_Init_Datatypes_vector_cons : ident.

Variable vector_in_graph : forall X n, (graph -> X -> rep_type -> Prop) -> graph -> vector X n -> rep_type -> Prop.

Variable vector_has :   forall X n (g : graph) (n0 : vector (X_type X) n) (v : VType),
  vector_in_graph (X_type X) n (X_in_graph X) g n0 (repNode v) -> graph_has_v g v. 

Variable vector_compatible : forall X n (g : graph) (to : nat) (lb : raw_vertex_block) (e : list (EType * (VType * VType)))
   (n0 : vector (X_type X) n) (p : rep_type),
 add_node_compatible g (new_copied_v g to) e ->
 graph_has_gen g to ->
 vector_in_graph (X_type X) n (X_in_graph X) g n0 p ->
 vector_in_graph (X_type X) n (X_in_graph X) (add_node g to lb e) n0 p.

Definition vector_representable_X (X : representable_X) (n :nat) : representable_X. 
Proof. 
  refine (Build_representable_X (vector (X_type X) n) (vector_in_graph (X_type X) n (X_in_graph X)) _ _).
  - apply vector_has. 
  - apply vector_compatible.
Defined.

Definition vcons_descr (X: representable_X) (n :nat) : constructor_description. 
  refine (Build_constructor_description _alloc_make_Coq_Init_Datatypes_vector_cons [X; vector_representable_X X n] (vector_representable_X X (S n)) _).
simpl. intros (x, (xs, _)). simpl. exact (vcons _ x n xs).
Defined.


(* TODO: So far we cannot yet say that they also satisfy the properties. *)

(* Definition list_representable_X (X : representable_X) : representable_X := 
  Build_representable_X (list (X_type X)) (list_in_graph (X_in_graph X)). 

Definition cons_descr (X: representable_X) : constructor_description.
refine (Build_constructor_description _alloc_make_Coq_Init_Datatypes_list_cons [X; list_representable_X X] (list_representable_X X) _ _).
simpl. intros (x, (xs, _)). exact (cons x xs).
Defined. *)


(* 
Fixpoint in_graphs (g : graph) (args : list representable_X) (xs :getTuple args) (ps : list rep_type) : Prop := 
 match args as l return (getTuple l -> Prop) with
  | [] => fun _ : getTuple [] => True
  | a :: args0 =>
      fun xs0 : getTuple (a :: args0) =>
      match ps with
      | [] => False
      | p :: ps0 => X_type_in_graph a g (fst xs0) p /\ in_graphs g args0 (snd xs0) ps0
      end
  end xs. *)

Locate "PRE".


(* General specification *) 
Definition alloc_make_spec_general (descr : constructor_description)  : ident * funspec :=
DECLARE (name descr)
  WITH gv : globals, g : graph, ps : list rep_type, xs : getTuple (args descr), roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
  PRE  [thread_info, tulong, tulong] (* TODO: CHANGE *)
       PROP (length ps = length (args descr);
            in_graphs g _ xs ps;
             writable_share sh
             )
       (* PARAMS (ti  (* ti *) (* ;  
              rep_type_val g p_x;
              rep_type_val g p_xs *) )  *)
       PARAMS (ti)
       GLOBALS ()
       SEP ( full_gc g t_info roots outlier ti sh ) 
  POST [ tptr tulong ]  
     EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info), 
     PROP ( X_type_in_graph (res descr) g' (ctr descr xs) p';
           gc_graph_iso g roots g' roots
         ) 
     LOCAL (temp ret_temp (rep_type_val g' p'))
     SEP (full_gc g' t_info' roots outlier ti sh).  



Definition alloc_make_list_cons_spec2 := alloc_make_spec_general (cons_descr representable_X_var). *)


(* If the error happens, that this identifier is used twice, this might happen because I imported the wrong program last. *)

Definition Gprog := ltac:(with_library prog [ make_bool_true_spec; make_nat_0_spec; alloc_make_list_nil_spec; alloc_make_list_cons_spec; alloc_make_nat_S_spec]).



