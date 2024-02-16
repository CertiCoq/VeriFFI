Require Import Coq.ZArith.ZArith
               Coq.Program.Basics
               Coq.Strings.String
               Coq.Lists.List
               Coq.Lists.ListSet.

Require Import ExtLib.Structures.Monads
               ExtLib.Data.Monads.OptionMonad
               ExtLib.Data.Monads.StateMonad
               ExtLib.Data.String.

Require Import VeriFFI.generator.gen_utils.
Require Import VeriFFI.library.base_representation.
Require Import VeriFFI.library.meta.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import ListNotations.

(*Unset Strict Unquote Universe Mode.*) (* There is no flag or option with this name *)

Ltac destruct_conj H :=
  match type of H with
  | @ex _ _ =>
    let p := fresh "_p" in
    let m := fresh "_M" in
    destruct H as [p m]; destruct_conj m
  | @and _ _ =>
    let m1 := fresh "_M" in
    let m2 := fresh "_M" in
    destruct H as [m1 m2]; destruct_conj m2
  | _ => idtac
  end.

Ltac prove_has_v :=
  intros g outlier x v;
  destruct x; intros H; simpl in *;
  try contradiction ; try (destruct_conj H; intuition).

Ltac prove_monotone_with_IH :=
  match goal with
  | [IH : forall (_ : rep_type), _ |- _ ] =>
    eapply IH; simpl; eauto
  end.

Ltac prove_monotone_with_IH' :=
  match goal with
  | [IH : forall (_ : @eq _ _ _) (_ : rep_type), _ |- _ ] =>
    eapply IH; simpl; eauto
  end.

Axiom graph_cRep_add_node : forall g to lb e p ts ps,
  add_node_compatible g (GCGraph.new_copied_v g to) e
   -> GCGraph.graph_has_gen g to
   -> graph_cRep g p ts ps
   -> graph_cRep (add_node g to lb e) p ts ps.

Ltac mon n :=
  let i := fresh "_i" in
  match goal with
  | [|- graph_predicate _ _ n _] =>
    let t := type of n in
    epose (i := @is_monotone t _ _ _ _ _ _ _ _ _ _)
  end;
  eapply i.

Ltac loop_over_app C :=
  match C with
  | ?a ?b =>
    match a with
    | ?c ?d => loop_over_app a ; mon d
    | ?e => mon b
    end
  | _ => idtac
  end.


Ltac prove_monotone :=
  intros g outliers to lb e x p C G; revert p;
  induction x;
  unshelve (match goal with
  | [|- forall _ _, graph_predicate _ _ ?this _] =>
    let p := fresh "p" in
    let H := fresh "H" in
    intros p H; hnf in H;
    destruct_conj H;
    repeat match goal with H: @graph_predicate ?A _ g outliers ?x ?p' |- _ =>
       apply (@is_monotone A ltac:(auto with typeclass_instances) g outliers to lb e x p' C G) in H
    end;
    repeat eexists; repeat split; 
    try eassumption; try (eapply graph_cRep_add_node; eauto);
    loop_over_app this;
    try prove_monotone_with_IH
   end);
   auto.

(*
Ltac prove_monotone :=
  intros g outliers to lb e x p C G; revert p;
  induction x;
  unshelve (match goal with
  | [|- forall _ _, graph_predicate _ _ ?this _] =>
    let p := fresh "p" in
    let H := fresh "H" in
    intros p H;
    hnf in H;
    destruct_conj H;
    repeat eexists;
    repeat split;
    loop_over_app this;
    try prove_monotone_with_IH;
    try (eauto || (eapply graph_cRep_add_node; eauto))
  end); auto.
*)

Ltac prove_outlier_compatible1 := 
 solve [
 let g := fresh "g" in let x := fresh "x" in let J := fresh "J" in
 intros g ?outliers x ?p _ J;
 exfalso;
 induction x;
 repeat match goal with 
        | H: graph_predicate _ _ _ (repOut _) |- _ => destruct H 
        | H: _ /\ _ |- _ => destruct H
        | H: exists _, _ |- _ => destruct H end;
 eauto]. 

Ltac prove_outlier_compat := 
  try prove_outlier_compatible1;
  try solve [intuition];
  match goal with |- ?A => fail 100 "Failed in prove_outlier_compat with goal:" A end.

Ltac show_goal :=
  match goal with |- ?A => idtac "GOAL:" A end.

Ltac in_graph_gen_tac :=
  intros;
  repeat (match goal with
          | [R : InGraph _ |- _] => destruct R
          end);
  econstructor; [solve [prove_has_v] | solve [prove_monotone] | solve [prove_outlier_compat]].

Require Import MetaCoq.Template.All.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation
       ListNotations
       MetaCoqNotations.

Require Import VeriFFI.generator.GraphPredicate.

Definition generate_InGraph_instance_type
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad named_term :=
  generate_instance_type ind mut one
    (fun ty_name t =>
      let n := "InGraph_" ++ ty_name in
      tProd (mkBindAnn (nNamed n) Relevant) (tApp <% InGraph %> [tVar ty_name]) t)
    (fun t => apply_to_pi_base (fun t' => tApp <% InGraph %> [t']) t).

(* Constructs the instance type for the type at hand,
   checks if there's an instance for it. *)
Definition find_missing_instance
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad bool :=
  tmMsg! ("Missing: " ++ string_of_inductive ind) ;;
  generate_InGraph_instance_type ind mut one >>=
  DB.deBruijn >>= tmUnquoteTyped Type >>= has_instance.

(* Take in a [global_declarations], which is a list of declarations,
   and find the inductive declarations in that list
   that do not have [InGraph] instances. *)
Fixpoint find_missing_instances
        (env : global_declarations) : TemplateMonad (list kername) :=
    match env with
    | (kn, InductiveDecl mut) :: env' =>
      rest <- find_missing_instances env' ;;
      ones <- monad_map_i
                (fun i => find_missing_instance
                            {| inductive_mind := kn ; inductive_ind := i |} mut)
                (ind_bodies mut) ;;
      if (fold_left andb ones true) (* if there are instances for all *)
        then ret rest (* then this one is not missing *)
        else ret (kn :: rest)
    | _ :: env' => find_missing_instances env'
    | nil =>
      tmMsg "End of missings" ;;
      ret nil
    end.

Definition tmLemma_ (id : ident) (A : Type) : TemplateMonad unit :=
  tmLemma id A ;; ret tt.

Definition add_instances_aux
           (kn : kername)
           (mut : mutual_inductive_body)
           (singles_tys : list (aname * named_term))
           (singles: list (def named_term)) : TemplateMonad (list unit) :=
  monad_map_i
    (fun i one =>
       let ind := {| inductive_mind := kn ; inductive_ind := i |} in
       quantified <- quantified ind mut one "InGraph_" <% InGraph %> ;;
       (* (* Now what can we do with this? *) *)
       (* (*    Let's start by going to its named representation. *) *)
       (* (* The reified type of the fully applied type constructor, *) *)
       (* (*    but with free variables! *) *)
       let tau := strip_quantifiers quantified in
       let quantifiers : list (aname * named_term) :=
           get_quantifiers id quantified in
       extra_quantified <- DB.deBruijn (build_quantifiers tProd quantifiers
                                                          (tApp <% InGraph %> [tau])) ;;
       instance_ty <- tmUnquoteTyped Type extra_quantified ;;
       (* (* tmPrint prog';; *) *)
       (* (* tmMsg "Inst" ;; *) *)
       (* (* tmPrint instance ;; *) *)
       name <- tmFreshName ("InGraph_" ++ ind_name one)%bs ;;
       tmLemma_ name instance_ty ;;
       (* tmLemma name instance_ty ;; *)

       (* This is sort of a hack. I couldn't use [tmUnquoteTyped] above *)
       (*    because of a mysterious type error. (Coq's type errors in monadic *)
       (*    contexts are just wild.) Therefore I had to [tmUnquote] it to get *)
       (*    a Σ-type. But when you project the second field out of that, *)
       (*    the type doesn't get evaluated to [InGraph _], it stays as *)
       (*    [my_projT2 {| ... |}]. The same thing goes for the first projection, *)
       (*    which is the type of the second projection. When the user prints *)
       (*    their [InGraph] instance, Coq shows the unevaluated version. *)
       (*    But we don't want to evaluate it [all] the way, that would unfoldd *)
       (*    the references to other instances of [InGraph]. We only want to get *)
       (*    the head normal form with [hnf]. *)
       (*    We have to do this both for the instance body and its type. *)
       (* tmEval hnf (my_projT2 instance) >>= *)
       (*   tmDefinitionRed_ false name (Some hnf) ;; *)

       (* Declare the new definition a type class instance *)
       mp <- tmCurrentModPath tt ;;
       tmExistingInstance export (ConstRef (mp, name)) ;;

       let fake_kn := (fst kn, ind_name one) in
       tmMsg! ("Added InGraph instance for " ++ string_of_kername fake_kn) ;;
       ret tt) (ind_bodies mut).

Definition add_instances (kn : kername) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  singles_tys <- singles_tys kn mut ;;
  (* tmEval all singles_tys >>= tmPrint ;; *)
  singles <- singles kn mut singles_tys ;;
  (* tmEval all singles >>= tmPrint ;; *)
  add_instances_aux kn mut singles_tys singles ;;
  ret tt.


(* Derives a [InGraph] instance for the type constructor [Tau],
   and the types its definition depends on. *)
Definition in_graph_gen {kind : Type} (Tau : kind) : TemplateMonad unit :=
  @graph_predicate_gen kind Tau ;;
  '(env, tau) <- tmQuoteRec Tau ;;
  missing <- find_missing_instances (declarations env) ;;
  monad_iter add_instances (rev missing).

Local Obligation Tactic := in_graph_gen_tac.
(*
 Require Import VeriFFI.generator.GraphPredicate. 
 MetaCoq Run (graph_predicate_gen nat). 
 MetaCoq Run (in_graph_gen nat).

 MetaCoq Run (graph_predicate_gen String.string). 
 MetaCoq Run (in_graph_gen String.string). 
*)

(* MetaCoq Run (graph_predicate_gen list). *)
(* MetaCoq Run (in_graph_gen list). *)

(* MetaCoq Run (graph_predicate_gen prod). *)
(* MetaCoq Run (in_graph_gen prod). *)

(* MetaCoq Run (in_graph_gen nat). *)
(* Instance InGraph_nat : InGraph nat. *)
(*   in_graph_gen_tac. *)
(* Defined. *)

(* MetaCoq Run (in_graph_gen bool). *)
(* Instance InGraph_bool : InGraph bool. *)
(* econstructor. *)
(* prove_has_v. *)
(* prove_monotone. *)
(* Defined. *)

(* Inductive T := *)
(* | C1 : T *)
(* | C2 : bool -> T *)
(* | C3 : bool -> bool -> T -> T. *)

(* MetaCoq Run (in_graph_gen T). *)
(* Instance InGraph_T : InGraph T. *)
(* econstructor. *)
(* prove_has_v. *)
(* prove_monotone. *)
(* Defined. *)


(* MetaCoq Run (in_graph_gen option). *)
(* Definition InGraph_option : forall A `{InGraph_A: InGraph A}, InGraph (option A). *)
(* intros. destruct InGraph_A. *)
(* econstructor. *)
(* prove_has_v. *)
(* prove_monotone. *)
(* Defined. *)

(* MetaCoq Run (in_graph_gen prod). *)
(* Definition InGraph_prod : forall A `{InGraph_A: InGraph A} B `{InGraph_B : InGraph B}, InGraph (prod A B). *)
(* intros. destruct InGraph_A. destruct InGraph_B. *)
(* econstructor. *)
(* prove_has_v. *)
(* prove_monotone. *)
(* Defined. *)


(* Inductive vec (A : Type) : nat -> Type := *)
(* | vnil : vec A O *)
(* | vcons : forall n, A -> vec A n -> vec A (S n). *)
(* MetaCoq Run (in_graph_gen vec). *)

(* (* MetaCoq Run (in_graph_gen vec). *) *)
(* Instance InGraph_vec (A : Type) (InGraph_A : InGraph A) (n : nat) : InGraph (vec A n) := *)
(*   let fix is_in_graph_vec (n : nat) (g : graph) (x : vec A n) (p : rep_type) {struct x} : Prop := *)
(*     match x with *)
(*     | vnil => graph_cRep g p (enum 0) [] *)
(*     | vcons arg0 arg1 arg2 => *)
(*         exists p0 p1 p2 : rep_type, *)
(*           @is_in_graph nat InGraph_nat g arg0 p0 /\ *)
(*           @is_in_graph A InGraph_A g arg1 p1 /\ *)
(*           is_in_graph_vec arg0 g arg2 p2 /\ *)
(*           graph_cRep g p (boxed 0 3) [p0; p1; p2] *)
(*     end *)
(*     in @Build_InGraph (vec A n) (is_in_graph_vec n). *)

(* Definition InGraph_vec : forall A `{InGraph_A: InGraph A} n, InGraph (vec A n). *)

(* intros. destruct InGraph_A. *)
(* econstructor. *)
(* prove_has_v. *)
(* prove_monotone. *)
(* Defined. *)


