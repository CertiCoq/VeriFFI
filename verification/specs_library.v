(** * Library for Specifications

Kathrin Stark, 2021.
 *)

From VeriFFI.library Require Export base_representation.
From VeriFFI.verification Require Export graph_add.
Require Import CertiGraph.CertiGC.GCGraph.
Require Import CertiGraph.CertiGC.spatial_gcgraph.
Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
(* TODO: Dependency. *)

(** ** Library definitions for specifications *)

Require Import VST.floyd.proofauto.
From compcert Require Import export.Clightdefs.
(* Defining a canonical ident for [thread_info] so that
   we do not have to import a file compiled by Clightgen. *)
Definition _thread_info : ident := ident_of_string "thread_info".

(** Custom types for thread info *)
Definition thread_info_type := Tstruct _thread_info noattr.
Definition thread_info := tptr thread_info_type.

(* Representation of rep_type as a C value *)
Definition rep_type_val (g : graph) (x : rep_type) : val :=
match x with
| repZ y => odd_Z2val y
| repOut p => GC_Pointer2val p
| repNode v => vertex_address g v
end.

(** *** Graph Conditions *)

Definition array_type := int_or_ptr_type.

(** Propositional conditions from the garbage collector specification and getting the isomorphism property for the garbage collector:
The thread_info has to be a new one, roots and outlier stay preserved *)
Definition gc_condition_prop g (t_info: GCGraph.thread_info) roots outlier :=

graph_unmarked g /\ no_backward_edge g /\ no_dangling_dst g /\ ti_size_spec (ti_heap t_info) (** From garbage_collect_condition, removed that roots and finfo are compatible. *)
/\ safe_to_copy g
/\ graph_heap_compatible g (ti_heap t_info) /\ outlier_compatible g outlier /\ roots_compatible g outlier roots
/\ gc_correct.sound_gc_graph g /\ copy_compatible g.

Definition space_rest_rep {cs : compspecs} (sp: space): mpred :=
  if (Val.eq sp.(space_start) nullval)
  then emp
  else data_at_ (space_sh sp)
                (tarray int_or_ptr_type (sp.(total_space) - sp.(used_space)))
                (offset_val (WORD_SIZE * used_space sp) sp.(space_start)).

Definition heap_rest_rep {cs: compspecs} (hp: heap): mpred :=
  iter_sepcon space_rest_rep hp.(spaces).

Print CertiGraph.CertiGC.spatial_gcgraph.before_gc_thread_info_rep.

(* Adapted from Shengyi to get the right GC *)
Definition before_gc_thread_info_rep (sh: share) (ti: CertiGraph.CertiGC.GCGraph.thread_info) (t: val) :=
  CertiGraph.CertiGC.spatial_gcgraph.before_gc_thread_info_rep sh ti t. (*
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
*)

(* KS: Changes: 
Before: heap-struct rep and heap_rest_rep

Now
- frames_rep 
- heap_struct_rep 
*)

Print frames_rep. 
(* frames_rep =
fun (sh : share) (frs : list frame) =>
(frames_shell_rep sh frs * roots_rep sh (frames2rootpairs frs))%logic
	 : share -> list frame -> mpred *)

Print frames_shell_rep.
(* frames_shell_rep =
fix frames_shell_rep (sh : share) (frames : list frame) {struct frames} :
	mpred :=
  match frames with
  | [] => emp
  | fr :: rest =>
      (frame_shell_rep sh fr (frames_p rest) * frames_shell_rep sh rest)%logic
  end
     : share -> list frame -> mpred *)

Print heap_struct_rep.
(* heap_struct_rep =
fun (sh : share) (sp_reps : list (reptype space_type)) (h : val) =>
data_at sh heap_type sp_reps h
	 : share -> list (reptype space_type) -> val -> mpred *)

Compute (reptype space_type).
(* Arguments heap_struct_rep sh sp_reps%gfield_scope h
	 = (val * (val * (val * val)))%type
     : Type *)

(* Full condition for the garbage collector *)
Definition full_gc g (t_info: GCGraph.thread_info) roots outlier ti sh :=
  (outlier_rep outlier * before_gc_thread_info_rep sh t_info ti * ti_token_rep (ti_heap t_info) (ti_heap_p t_info) * graph_rep g && !!gc_condition_prop g t_info roots outlier)%logic.

