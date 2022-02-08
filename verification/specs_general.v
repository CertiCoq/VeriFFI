(** * General Specification of alloc functions

Kathrin Stark, 2021.

This file contains a general specification for the alloc function,
using a representation of constructors.
*)

From VeriFFI Require Export library.base_representation.
From VeriFFI Require Export library.meta.
From VeriFFI Require Export verification.graph_add.
(* From VeriFFI Require Export verification.example.glue. *)
From VeriFFI Require Export verification.specs_library.


(** ** 1. Representable Type Class

A type representable in a graph consists of:
1. a type, X_type, which will be representable in the graph
2. a function, X_in_graph, which defines the representation in a graph
3. consistency conditions on X_in_graph, X_has_v and X_monotone, needed to actually get the later proof through:
   a. X_has_v: Whenever a node represents an element of X_type, then this node is present in the graph.
   b. X_monotone: Adding (compatible) nodes to a graph doesn't change whether an element of a type is present in the graph.
 *)

(* Record representable_X  := *)
(*   { X_type : Type; *)
(*     X_in_graph : graph -> X_type -> rep_type -> Prop; *)
(*     X_has_v : forall g n v, X_in_graph g n (repNode v) -> graph_has_v g v; *)
(*     X_monotone : forall g to lb e n p, *)
(*         add_node_compatible g (new_copied_v g to) e *)
(*         -> graph_has_gen g to *)
(*         -> X_in_graph g n p *)
(*         -> X_in_graph (add_node g to lb e) n p *)
(*     }. *)

(* Existing Class representable_X. *)

(** ** 2. Encoding constructors

The code of a constructor which allows parameters, indices, dependent arguments
tailored to what we need for the specification.
The representation uses a weak HOAS representation.
See the examples section for more detailed examples.

ARG is not strictly necessary as it is an instance of DEPARG, but simplifies the later representation.
 *)

(* Inductive constrCode := *)
(* (* the type parameters in parametric polymorphism, isn't represented immediately in memory, *)
(* but the possibility for representation is needed later, e.g., A in [list A] *)
(*  *) *)
(*  | TYPEPARAM  : (representable_X -> constrCode) -> constrCode *)
(* (* Non-type parameters of a fixed type which isn't represented in memory, e.g., n in [n < m] *) *)
(*  | PARAM  : forall X : Type, (X -> constrCode) -> constrCode *)
(* (* index, represented in memory, e.g. the index of a vector *) *)
(*  | INDEX  : forall (X_: representable_X), (X_type X_ -> constrCode) -> constrCode *)
(*  (* non-dependent version of arguments, argument represented in memory, e.g. for X/list X of cons *) *)
(*  | ARG : representable_X -> constrCode -> constrCode *)
(*  (* dependent argument, represented in memory, e.g. in positive_nat_list *) *)
(*  | DEPARG : forall (X_: representable_X), (X_type X_ -> constrCode) -> constrCode *)
(* (* the end type, e.g., list X for cons : forall X, X -> list X -> **list X** *) *)
(*  | RES  : representable_X -> constrCode. *)


(** Representation of data needed for the argument part of an instance of a constrCodeuctor, e.g., in the with clause of a specification.
This will be a dependent tuple. *)
(* Fixpoint args (c : constrCode) : Type := *)
(*     match c with *)
(*     | TYPEPARAM f => {X_ : representable_X & args (f X_) } *)
(*     | PARAM X f => {x : X & args (f x) } *)
(*     | INDEX X_ f => {x : X_type X_ & args (f x)} *)
(*     | ARG X_ arg => (X_type X_ * args arg)%type *)
(*     | DEPARG X_ f => {x : X_type X_ & args (f x) } *)
(*     | RES x => unit *)
(* end. *)

(* (* Instance of result type *) *)
(* Fixpoint getRes (c: constrCode) (xs : args c) : representable_X := *)
(*   match c as l return (args l -> representable_X) with *)
(*   | TYPEPARAM f => fun H => let (X_, xs') := H in getRes (f X_) xs' *)
(*   | PARAM X f => fun H => let (x, xs') := H in getRes (f x) xs' *)
(*   | INDEX X_ f => fun H => let (x, xs') := H in getRes (f x) xs' *)
(*   | ARG X_ arg => fun H => let (x, xs') := H in getRes arg xs' *)
(*   | DEPARG X_ f => fun H  => let (x, xs') := H in getRes (f x) xs' *)
(*   | RES x => fun _ => x *)
(*   end xs. *)

(* (** Full description of a constructor: *)
(*    fitting identifier, the code for the constructor, *)
(*    and the corresponding Coq function for the constructor. *)

(*   This is what MetaCoq will have to generate. *)
(*  *) *)
(* Record constructor_description := *)
(* { name : ident; *)
(*   constr : constrCode; *)
(*   coqConstr : forall (xs : args constr), X_type (getRes constr xs) *)
(* }. *)

(** ** 3. A General Specification *)

(** Generation of the in_graphs predicate, given the constructor arguments. *)
Fixpoint in_graphs
         (g : graph) (c : reific Rep) (xs : args c) (ps : list rep_type) : Prop :=
  match c as l return (args l -> Prop) with
  | TYPEPARAM f =>
      fun H => let (X_, xs') := H in
               let (R_, xs') := xs' in
        in_graphs g (f X_ R_) xs' ps
  | PARAM X f =>
      fun H => let (x, xs') := H in
      in_graphs g (f x) xs' ps
  | INDEX X_ R_ f =>
      fun H => let (x, xs') := H in
      match ps with
      | [] => False
      | p :: ps' =>  @is_in_graph X_ (@in_graph X_ R_) g x p /\ in_graphs g (f x) xs' ps'
      end
  | ARG X_ R_ arg =>
      fun H (* : args (ARG X_ R_ arg) *) =>
      let (x, xs') := H in
      match ps with
      | [] => False
      | p :: ps' => @is_in_graph X_ (@in_graph X_ R_) g x p /\ in_graphs g arg xs' ps'
      end
  | DEPARG X_ R_ f =>
      fun H  => let (x, xs') := H in
      match ps with
      | [] => False
      | p :: ps' => @is_in_graph X_ (@in_graph X_ R_) g x p /\ in_graphs g (f x) xs' ps'
      end
  | RES x _ => fun _ => ps = nil
  end xs.

(** List of [tulong] depending on the number of arguments
    represented in memory, needed for the parameters. *)
Fixpoint get_size (c : reific Rep) (xs : args c) : nat :=
  match c as l return (args l -> nat) with
  | TYPEPARAM f =>
      fun H => let (X_, xs') := H in let (R_, xs') := xs' in get_size (f X_ R_) xs'
  | PARAM X f =>
      fun H => let (x, xs') := H in get_size (f x) xs'
  | INDEX _ _ f =>
      fun H => let (x, xs') := H in S (get_size (f x) xs')
  | ARG _ X_ arg =>
      fun H (* : args (ARG X_ arg) *) => let (x, xs') := H in S (get_size arg xs')
  | DEPARG _ X_ f => fun H  => let (x, xs') := H in S (get_size (f x) xs')
  | RES _ x => fun _ => O
  end xs.

Definition get_tulongs (c : reific Rep) (xs : args c) : list type :=
  repeat tulong (get_size c xs).

Lemma in_graphs_size (g : graph) (c : reific Rep) (xs : args c) (ps : list rep_type) :
  in_graphs g c xs ps -> get_size c xs = length ps.
Proof.
  revert ps.
  induction c; simpl in *; intros; try (destruct xs); try (destruct s); eauto.
  all: destruct ps; simpl; intuition eauto; try congruence.
Qed.

(** Custom notation with a list for PRE to make the specification better readable. *)
Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [[ xs ]] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (xs, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0,
             P at level 100, Q at level 100) : funspec_scope.

Definition alloc_make_spec_general
           (c : constructor_description)
           (n : nat) : ident * funspec :=
  DECLARE _w (* FIXME to actual C fn names somehow? *)
    WITH gv : globals, g : graph, ps : list rep_type,
         xs : args (ctor_reific c), roots : roots_t, sh : share,
         ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
    PRE  [[ thread_info :: repeat tulong n ]]
       PROP (n = get_size (ctor_reific c) xs ;
             in_graphs g _ xs ps ;
             writable_share sh)
       (PARAMSx (ti :: map (fun p => rep_type_val g p) ps)
       (GLOBALSx nil
       (SEPx (full_gc g t_info roots outlier ti sh :: nil))))
    POST [ tptr tulong ]
      EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info),
        PROP (let r := result (ctor_reific c) xs in
              @is_in_graph (projT1 r) (@in_graph (projT1 r) (projT2 r)) g' (ctor_real c xs) p' ;
              gc_graph_iso g roots g' roots)
        RETURN  (rep_type_val g' p')
        SEP (full_gc g' t_info' roots outlier ti sh).



(** ** 4. Examples *)

(* Require Import VeriFFI.generator.InGraph. *)
(* Require Import VeriFFI.generator.Rep. *)
(* Require Import VeriFFI.generator.Desc. *)
(* Unset Strict Unquote Universe Mode. *)

(* (** *** 4.0 Non-dependent, no indices/parameters - nat *) *)
(* Set Printing All. *)
(* Set Printing Universes. *)
(* MetaCoq Run (in_graph_gen list). *)
(* MetaCoq Run (in_graph_gen nat). *)
(* Instance Rep_nat : Rep nat. rep_gen. Defined. *)
(* MetaCoq Run (desc_gen O). *)
(* MetaCoq Run (desc_gen S). *)

(* (** nat has to be representable *) *)
(* Variable nat_has: forall (g : graph) (n : nat) (v : VType), nat_in_graph g n (repNode v) -> graph_has_v g v. *)

(* Variable nat_monotone:   forall (g : graph) (to : nat) (lb : raw_vertex_block) (e : list (EType * (VType * VType))) *)
(*     (n : nat) (p : rep_type), *)
(*   add_node_compatible g (new_copied_v g to) e -> *)
(*   graph_has_gen g to -> nat_in_graph g n p -> nat_in_graph (add_node g to lb e) n p. *)

(* Definition nat_representable: representable_X := *)
(* Build_representable_X nat nat_in_graph nat_has nat_monotone. *)

(* (** Constructor code  *) *)
(* Definition SucCode := *)
(*   ARG nat_representable (RES nat_representable). *)


(** *** 4.1 Parameters - Lists, cons

Specification we want:

Definition alloc_make_list_cons_spec : ident * funspec :=
DECLARE _alloc_make_Coq_Init_Datatypes_list_cons
  WITH gv : globals, g : graph, p_x : rep_type, p_xs : rep_type, args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type },    roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info
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
     RETURN  (rep_type_val g' p')
     SEP (full_gc g' t_info' roots outlier ti sh).
*)

(** 4.1.1 List has to be representable. *)
(* Parameter list_has : *)
(* forall X (g : graph) (n : list (X_type X)) (v : VType), *)
(*    list_in_graph (X_in_graph X) g n (repNode v) -> graph_has_v g v. *)

(* Parameter list_monotone : *)
(* forall X (g : graph) (to : nat) (lb : raw_vertex_block) (e : list (EType * (VType * VType))) *)
(*      (n : list (X_type X)) (p : rep_type), *)
(*    add_node_compatible g (new_copied_v g to) e -> *)
(*    graph_has_gen g to -> *)
(*    list_in_graph (X_in_graph X) g n p -> list_in_graph (X_in_graph X) (add_node g to lb e) n p. *)

(* Definition list_representable_X (X : representable_X) : representable_X := *)
(*   Build_representable_X (list (X_type X)) (list_in_graph (X_in_graph X)) (list_has X) (list_monotone X). *)

(* (** Constructor code  *) *)
(* Definition consCode := *)
(*   TYPEPARAM (fun X => ARG X (ARG (list_representable_X X) (RES (list_representable_X X)))). *)

(* (** Constructor description *) *)
(* Definition consDescr : constructor_description. *)
(* Proof. *)
(* refine (Build_constructor_description _alloc_make_Coq_Init_Datatypes_list_cons consCode _). *)
(* simpl. intros (X&x&xs&_). simpl. exact (x :: xs). *)
(* Defined. *)

(* Definition nilCode := *)
(*   TYPEPARAM (fun X => RES (list_representable_X X)). *)

(* Definition nilDescr : constructor_description. *)
(* Proof. *)
(* refine (Build_constructor_description _alloc_make_Coq_Init_Datatypes_list_cons nilCode _). *)
(* simpl. intros (X&_). simpl. exact nil. *)
(* Defined. *)

(* MetaCoq Run (in_graph_gen list). *)
(* Instance Rep_list : forall A, Rep A -> Rep (list A). rep_gen. Defined. *)
(* MetaCoq Run (desc_gen nil). *)
(* MetaCoq Run (desc_gen cons). *)


(* Definition graph_X_var  (args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type })  := let (graph_X_var, args') := args in graph_X_var. *)

(* Definition x (args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type }) : X_type (graph_X_var args). *)
(* Proof. *)
(*   destruct args, p. exact x0. *)
(* Defined. *)

(* Definition xs (args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type }) : list (X_type (graph_X_var args)). *)
(* Proof. *)
(*   destruct args, p. exact l. *)
(* Defined. *)

(* Definition alloc_make_list_cons_spec : ident * funspec := *)
(* DECLARE _alloc_make_Coq_Init_Datatypes_list_cons *)
(*   WITH gv : globals, g : graph, p_x : rep_type, p_xs : rep_type, args : {graph_X_var : representable_X & (X_type graph_X_var (* x *) * list (X_type graph_X_var) (* xs *))%type },    roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info *)
(*   PRE  [thread_info, tulong, tulong] *)
(*        PROP (X_in_graph (graph_X_var args) g (x args) p_x; *)
(*             list_in_graph (X_in_graph (graph_X_var args)) g (xs args) p_xs; *)
(*              writable_share sh *)
(*              ) *)
(*        PARAMS (ti; *)
(*               rep_type_val g p_x; *)
(*               rep_type_val g p_xs) *)
(*        GLOBALS () *)
(*        SEP ( full_gc g t_info roots outlier ti sh ) *)
(*   POST [ tptr tulong ] *)
(*      EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info), *)
(*      PROP (list_in_graph (X_in_graph (graph_X_var args)) g' ((x args) :: (xs args)) p'; *)
(*            gc_graph_iso g roots g' roots *)
(*          ) *)
(*      RETURN  (rep_type_val g' p') *)
(*      SEP (full_gc g' t_info' roots outlier ti sh). *)

(* (** Definitional equality will be hard because of unit/all ps would have to be in a list. *)
(*  Probably, we'll want funspec_sub instead. *) *)
(* (* Lemma cons_same_spec :  alloc_make_list_cons_spec = alloc_make_spec_general consDescr. *)
(* Proof. *)
(*   unfold alloc_make_spec_general. simpl. *)
(* Admitted. *)

(* Goal funspec_sub (snd (alloc_make_spec_general consDescr)) (snd alloc_make_list_cons_spec). *)
(* Proof. *)
(*   unfold funspec_sub. *)
(*   simpl. intuition. *)
(* Admitted. *) *)

(* (** *** 4.2 Indices/silent arguments - Vector, cons *) *)

(* Inductive vector (A : Type) : nat -> Type := *)
(*    | vnil : vector A 0%nat *)
(*    | vcons : A -> forall n : nat, vector A n -> vector A (S n). *)

(* (** 4.1.2 Vectors have to be representable - all this will be generated automatically. *) *)
(* Variable _alloc_make_Coq_Init_Datatypes_vector_cons : ident. *)

(* Variable vector_in_graph : forall X n, (graph -> X -> rep_type -> Prop) -> graph -> vector X n -> rep_type -> Prop. *)

(* Variable vector_has :   forall X n (g : graph) (n0 : vector (X_type X) n) (v : VType), *)
(*   vector_in_graph (X_type X) n (X_in_graph X) g n0 (repNode v) -> graph_has_v g v. *)

(* Variable vector_monotone : forall X n (g : graph) (to : nat) (lb : raw_vertex_block) (e : list (EType * (VType * VType))) *)
(*    (n0 : vector (X_type X) n) (p : rep_type), *)
(*  add_node_compatible g (new_copied_v g to) e -> *)
(*  graph_has_gen g to -> *)
(*  vector_in_graph (X_type X) n (X_in_graph X) g n0 p -> *)
(*  vector_in_graph (X_type X) n (X_in_graph X) (add_node g to lb e) n0 p. *)

(* Definition vector_representable_X (X : representable_X) (n :nat) : representable_X. *)
(* Proof. *)
(*   refine (Build_representable_X (vector (X_type X) n) (vector_in_graph (X_type X) n (X_in_graph X)) _ _). *)
(*   - apply vector_has. *)
(*   - apply vector_monotone. *)
(* Defined. *)

(* (** Constructor code *) *)
(* Definition vectorConsCode := TYPEPARAM  (fun X => (ARG X (INDEX nat_representable (fun n => ARG (vector_representable_X X n) (RES (vector_representable_X X (S n))))))). *)

(* (** Constructor description *) *)
(* Definition vectorConsDescr : constructor_description. *)
(* Proof. *)
(* refine (Build_constructor_description _alloc_make_Coq_Init_Datatypes_list_cons vectorConsCode _). *)
(* simpl. intros (X&x&n&xs&_). simpl. exact (vcons _ x n xs). *)
(* Defined. *)

(* (** *** 4.3 Parameters and indices mixed -  param_and_index. *)

(* The specification we'd want modulo a/b/pf being packed in a sigma type: *)

(*  Definition alloc_make_foo_spec : ident * funspec := *)
(* DECLARE _alloc_make_foo *)
(*   WITH gv : globals, g : graph, a : nat, b: nat, pf : a < b, roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info *)
(*   PRE  [thread_info, tulong] *)
(*        PROP (le_in_graph a b g pf p; *)
(*              writable_share sh *)
(*              ) *)
(*        PARAMS (ti; *)
(*               rep_type_val g p_x; *)
(*               rep_type_val g p_xs) *)
(*        GLOBALS () *)
(*        SEP ( full_gc g t_info roots outlier ti sh ) *)
(*   POST [ tptr tulong ] *)
(*      EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info), *)
(*      PROP (param_and_index_in_graph a b pf g' (foo a b pf) p'; *)
(*            gc_graph_iso g roots g' roots *)
(*          ) *)
(*      RETURN  (rep_type_val g' p') *)
(*      SEP (full_gc g' t_info' roots outlier ti sh). *)
(* *) *)

(* Inductive param_and_index (a b : nat) : (a < b)%nat -> Type := *)
(* | foo : forall (pf : (a < b)%nat), param_and_index a b pf. *)

(* Variable le_in_graph : forall (a b : nat), graph -> (a < b)%nat -> rep_type -> Prop. *)

(* Parameter le_has :   forall a b (g : graph) (n : (a < b)%nat) (v : VType), *)
(*   le_in_graph a b g n (repNode v) -> graph_has_v g v. *)

(* Parameter le_c :  forall a b (g : graph) (to : nat) (lb : raw_vertex_block) (e : list (EType * (VType * VType))) *)
(*     (n : (a < b)%nat) (p : rep_type), *)
(*   add_node_compatible g (new_copied_v g to) e -> *)
(*   graph_has_gen g to -> le_in_graph a b g n p -> le_in_graph a b (add_node g to lb e) n p. *)

(* Definition le_representable (a b : nat) : representable_X. *)
(* refine (Build_representable_X (a < b)%nat (le_in_graph a b) (le_has a b) (le_c a b)). *)
(* Defined. *)

(* Variable param_and_index_in_graph : forall (a b : nat) (pf : (a < b)%nat), graph -> param_and_index a b pf -> rep_type -> Prop. *)

(* Variable param_and_index_has :   forall a b (lex : (a < b)%nat) (g : graph) (n : param_and_index a b lex) (v : VType), *)
(*   param_and_index_in_graph a b lex g n (repNode v) -> graph_has_v g v. *)

(* Variable param_and_index_monotone:  forall a b (lex : (a < b)%nat) (g : graph) (to : nat) (lb : raw_vertex_block) (e : list (EType * (VType * VType))) *)
(*    (n : param_and_index a b lex) (p : rep_type), *)
(*  add_node_compatible g (new_copied_v g to) e -> *)
(*  graph_has_gen g to -> *)
(*  param_and_index_in_graph a b lex g n p -> *)
(*  param_and_index_in_graph a b lex (add_node g to lb e) n p. *)

(* Definition param_and_index_representable : forall  (a b : nat) (lex : (a < b)%nat), representable_X. *)
(* Proof. *)
(*   intros a b lex. refine (Build_representable_X _ (param_and_index_in_graph a b lex) (param_and_index_has a b lex) (param_and_index_monotone a b lex)). *)
(* Defined. *)

(* (* Code for foo *) *)
(* Definition param_and_indexCode := *)
(*   PARAM nat (fun a => PARAM nat (fun b => INDEX (le_representable a b) (fun pf => RES (param_and_index_representable a b pf) ) )). *)

(* Definition paramAndIndexDescr : constructor_description. *)
(* Proof. *)
(*   refine (Build_constructor_description  _alloc_make_Coq_Init_Datatypes_list_cons param_and_indexCode _). *)
(*   simpl. intros (a&b&pf&_). simpl. exact (foo a b pf). *)
(* Defined. *)

(* (** 4.4 Dependent arguments - positive_nat_list *)

(*  Definition alloc_make_positive_nat_list_cons_spec : ident * funspec := *)
(* DECLARE _alloc_make_Coq_Init_Datatypes_list_cons *)
(*   WITH gv : globals, g : graph, x : nat, pf : 0 < x, xs : positive_nat_list,  roots : roots_t, sh : share, ti : val, outlier : outlier_t, f_info : fun_info, t_info : GCGraph.thread_info *)
(*   PRE  [thread_info, tulong, tulong] *)
(*        PROP (nat_in_graph g x p_x; *)
(*              le_in_graph g pf p_pf; *)
(*              positive_nat_list_in_graph g xs p_xs; *)
(*              writable_share sh *)
(*              ) *)
(*        PARAMS (ti; *)
(*               rep_type_val g p_x; *)
(*               rep_type_val g p_xs) *)
(*        GLOBALS () *)
(*        SEP ( full_gc g t_info roots outlier ti sh ) *)
(*   POST [ tptr tulong ] *)
(*      EX (p' : rep_type) (g' : graph) (t_info' : GCGraph.thread_info), *)
(*      PROP (positive_nat_list_in_graph g (pcons x pf xs) p'; *)
(*            gc_graph_iso g roots g' roots *)
(*          ) *)
(*      RETURN  (rep_type_val g' p') *)
(*      SEP (full_gc g' t_info' roots outlier ti sh). *)
(*  *) *)

(* Inductive positive_nat_list : Type := *)
(* | pnil : positive_nat_list *)
(* | pcons : forall (x : nat), (0 < x)%nat -> positive_nat_list -> positive_nat_list. *)

(* Variable positive_nat_list_in_graph : graph -> positive_nat_list -> rep_type ->  Prop. *)

(* Variable positive_nat_list_has: forall (g : graph) (n : positive_nat_list) (v : VType), *)
(*   positive_nat_list_in_graph g n (repNode v) -> graph_has_v g v. *)

(* Variable positive_nat_list_c: *)
(*  forall (g : graph) (to : nat) (lb : raw_vertex_block) (e : list (EType * (VType * VType))) *)
(*    (n : positive_nat_list) (p : rep_type), *)
(*  add_node_compatible g (new_copied_v g to) e -> *)
(*  graph_has_gen g to -> *)
(*  positive_nat_list_in_graph g n p -> positive_nat_list_in_graph (add_node g to lb e) n p. *)

(* Definition positive_nat_list_representable : representable_X. *)
(* refine (Build_representable_X _ positive_nat_list_in_graph positive_nat_list_has positive_nat_list_c). *)
(* Defined. *)

(* (* Code *) *)
(* Definition positve_nat_listCode := *)
(*   DEPARG nat_representable (fun x => ARG (le_representable 0 x) (ARG positive_nat_list_representable (RES positive_nat_list_representable))). *)

(* (* Constructor description *) *)
(* Definition posNatListDescr : constructor_description. *)
(* Proof. *)
(*   refine (Build_constructor_description  _alloc_make_Coq_Init_Datatypes_list_cons positve_nat_listCode _). *)
(*   simpl. intros (a&b&pf&_). exact (pcons a b pf). *)
(* Defined. *)
