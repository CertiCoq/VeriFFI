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

Require Import MetaCoq.Template.All.

(* Warning: MetaCoq doesn't use the Monad notation from ExtLib,
  therefore don't expect ExtLib functions to work with TemplateMonad. *)
Import monad_utils.MCMonadNotation
       ListNotations
       MetaCoqNotations.

Require Import VeriFFI.generator.GraphPredicate.

Definition Discriminator (A : Type) (descs : list ctor_desc) : Type :=
  Discrimination A.

Ltac disc_gen_tac :=
  idtac.
  (* intros; *)
  (* repeat (match goal with *)
  (*         | [R : Discrimination _ |- _] => destruct R *)
  (*         end); *)
  (* unshelve econstructor. *)
  (* [apply graph_predicate | prove_has_v | prove_monotone]. *)

Definition generate_Discrimination_instance_type
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad named_term :=
  generate_instance_type ind mut one
    (fun ty_name t => t)
    (fun t => apply_to_pi_base (fun t' => tApp <% Discrimination %> [t']) t).

(* Constructs the instance type for the type at hand,
   checks if there's an instance for it. *)
Definition find_missing_instance
           (ind : inductive)
           (mut : mutual_inductive_body)
           (one : one_inductive_body) : TemplateMonad bool :=
  tmMsg! ("Missing: " ++ string_of_inductive ind) ;;
  generate_Discrimination_instance_type ind mut one >>=
  DB.deBruijn >>= tmUnquoteTyped Type >>= has_instance.

(* Take in a [global_declarations], which is a list of declarations,
   and find the inductive declarations in that list
   that do not have [Discrimination] instances. *)
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

Definition tmInferInstance' (A : Type) (err : string) : TemplateMonad term :=
  o <- tmInferInstance (Some all) A ;;
  match o with
  | my_Some inst => tmQuote inst
  | my_None => tmFail err
  end.
  
Definition make_desc_list (ind : inductive)
                          (ctors : list constructor_body) : TemplateMonad term :=
  l <- monad_map_i
    (fun i _ =>
       t <- tmUnquoteTyped Type (tApp <% @CtorDesc %> [hole; tConstruct ind i []]) ;;
       t_inst <- tmInferInstance' t "No CtorDesc instance for constructor"%bs;;
       tmUnquoteTyped ctor_desc
                      (tApp <% @ctor_desc_of_val %> [hole; tConstruct ind i []; t_inst])) ctors ;;
  tmQuote l. 

Definition tmLemmaQuote (id : ident) (A : Type) : TemplateMonad term :=
  tmLemma id A >>= tmQuote.

Definition add_instances_aux
           (kn : kername)
           (mut : mutual_inductive_body) : TemplateMonad (list unit) :=
  monad_map_i
    (fun i one =>
       let ind := {| inductive_mind := kn ; inductive_ind := i |} in
       (* quantified <- generate_Discrimination_instance_type ind mut one ;; *)
       desc_list <- make_desc_list ind (ind_ctors one) ;;
       quantified_before <- generate_instance_type ind mut one
         (fun ty_name t => t)
         (* (fun t => apply_to_pi_base (fun t' => tApp <% Discrimination %> [t']) t) ;; *)
         (fun t => apply_to_pi_base (fun t' => tApp <% Discriminator %> [t'; desc_list]) t) ;;
                 (* [tApp <% holding %> [t'; <% @nil ctor_desc %>]]) t) ;; *)
       quantified_after <- generate_instance_type ind mut one
         (fun ty_name t => t)
         (fun t => apply_to_pi_base (fun t' => tApp <% Discrimination %> [t']) t) ;;
       
       instance_ty_before <- DB.deBruijn quantified_before >>= tmUnquoteTyped Type ;;
       quantified_after' <- DB.deBruijn quantified_after ;;
       instance_ty_after <- tmUnquoteTyped Type quantified_after' ;;

       name_before <- tmFreshName ("Discriminator_" ++ ind_name one)%bs ;;
       lemma <- tmLemmaQuote name_before instance_ty_before ;;

       name_after <- tmFreshName ("Discrimination_" ++ ind_name one)%bs ;;
       let def : term := tCast lemma Cast quantified_after' in
       (* Tried this, didn't work: 
         instance <- tmUnquoteTyped instance_ty_after def ;;
         @tmDefinition name_after instance_ty_after instance ;;
       *)

       (* This is sort of a hack. I couldn't use [tmUnquoteTyped] above *)
       (* because of a mysterious type error. (Coq's type errors in monadic *)
       (* contexts are just wild.) Therefore I had to [tmUnquote] it to get *)
       (* a Σ-type. But when you project the second field out of that, *)
       (* the type doesn't get evaluated to [Discrimination _], it stays as *)
       (* [my_projT2 {| ... |}]. The same thing goes for the first projection, *)
       (* which is the type of the second projection. When the user prints *)
       (* their [Discrimination] instance, Coq shows the unevaluated version. *)
       (* But we don't want to evaluate it [all] the way, that would unfold *)
       (* the references to other instances of [Discrimination]. We only want to get *)
       (* the head normal form with [hnf]. *)
       (* We have to do this both for the instance body and its type. *)
       instance <- tmUnquote def ;;
       tmEval hnf (my_projT2 instance) >>=
         tmDefinitionRed_ false name_after (Some hnf) ;;

       (* Declare the new definition a type class instance *)
       mp <- tmCurrentModPath tt ;;
       tmExistingInstance export (ConstRef (mp, name_after)) ;;

       let fake_kn := (fst kn, ind_name one) in
       tmMsg! ("Added Discrimination instance for " ++ string_of_kername fake_kn) ;;
       ret tt) (ind_bodies mut).

Definition add_instances (kn : kername) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  add_instances_aux kn mut ;;
  ret tt.


(* Derives a [Discrimination] instance for the type constructor [Tau],
   and the types its definition depends on. *)
Definition disc_gen {kind : Type} (Tau : kind) : TemplateMonad unit :=
  '(env, tau) <- tmQuoteRec Tau ;;
  missing <- find_missing_instances (declarations env) ;;
  monad_iter add_instances (rev missing).

Ltac discriminating :=
  match goal with
  | [ |- @Discriminator _ ?l ] => set l as descs
  end;
  unfold Discriminator; intros;
  constructor; intros x;
  match goal with
  (* one for each number of constructors, unfortunately *)
  | [ descs := nil |- _ ] =>
      case x eqn:eq_x; idtac
  | [ descs := ?d1 :: nil |- _ ] =>
      case x eqn:eq_x; exists d1
  | [ descs := ?d1 :: ?d2 :: nil |- _ ] =>
      case x eqn:eq_x; [ exists d1 | exists d2 ]
  | [ descs := ?d1 :: ?d2 :: ?d3 :: nil |- _ ] =>
      case x eqn:eq_x; [ exists d1 | exists d2 | exists d3 ]
  | [ descs := ?d1 :: ?d2 :: ?d3 :: ?d4 :: nil |- _ ] =>
      case x eqn:eq_x; [ exists d1 | exists d2 | exists d3 | exists d4 ]
  | [ descs := ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: nil |- _ ] =>
      case x eqn:eq_x; [ exists d1 | exists d2 | exists d3 | exists d4 | exists d5 ]
  | [ descs := ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: ?d6 :: nil |- _ ] =>
      case x eqn:eq_x; [ exists d1 | exists d2 | exists d3 | exists d4 | exists d5 | exists d6 ]
  | [ descs := ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: ?d6 :: ?d7 :: nil |- _ ] =>
      case x eqn:eq_x; [ exists d1 | exists d2 | exists d3 | exists d4 | exists d5 | exists d6 | exists d7 ]
  | [ descs := ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: ?d6 :: ?d7 :: ?d8 :: nil |- _ ] =>
      case x eqn:eq_x; [ exists d1 | exists d2 | exists d3 | exists d4 | exists d5 | exists d6 | exists d7 | exists d8 ]
  | [ descs := ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: ?d6 :: ?d7 :: ?d8 :: ?d9 :: nil |- _ ] =>
      case x eqn:eq_x; [ exists d1 | exists d2 | exists d3 | exists d4 | exists d5 | exists d6 | exists d7 | exists d8 | exists d9 ]
  | [ descs := ?d1 :: ?d2 :: ?d3 :: ?d4 :: ?d5 :: ?d6 :: ?d7 :: ?d8 :: ?d9 :: ?d10  :: nil |- _ ] =>
      case x eqn:eq_x; [ exists d1 | exists d2 | exists d3 | exists d4 | exists d5 | exists d6 | exists d7 | exists d8 | exists d9 | exists d10 ]
  end;
  match goal with
  (* one for each constructor arity, unfortunately *)
  | [ eq_x : @eq _ _ (_ ?v1 ?v2 ?v3 ?v4 ?v5 ?v6 ?v7 ?v8 ?v9 ?v10) |- _ ] => exists (v1; (v2; (v3; (v4; (v5; (v6; (v7; (v8; (v9; (v10; tt))))))))))
  | [ eq_x : @eq _ _ (_ ?v1 ?v2 ?v3 ?v4 ?v5 ?v6 ?v7 ?v8 ?v9) |- _ ] => exists (v1; (v2; (v3; (v4; (v5; (v6; (v7; (v8; (v9; tt)))))))))
  | [ eq_x : @eq _ _ (_ ?v1 ?v2 ?v3 ?v4 ?v5 ?v6 ?v7 ?v8) |- _ ] => exists (v1; (v2; (v3; (v4; (v5; (v6; (v7; (v8; tt))))))))
  | [ eq_x : @eq _ _ (_ ?v1 ?v2 ?v3 ?v4 ?v5 ?v6 ?v7) |- _ ] => exists (v1; (v2; (v3; (v4; (v5; (v6; (v7; tt)))))))
  | [ eq_x : @eq _ _ (_ ?v1 ?v2 ?v3 ?v4 ?v5 ?v6) |- _ ] => exists (v1; (v2; (v3; (v4; (v5; (v6; tt))))))
  | [ eq_x : @eq _ _ (_ ?v1 ?v2 ?v3 ?v4 ?v5) |- _ ] => exists (v1; (v2; (v3; (v4; (v5; tt)))))
  | [ eq_x : @eq _ _ (_ ?v1 ?v2 ?v3 ?v4) |- _ ] => exists (v1; (v2; (v3; (v4; tt))))
  | [ eq_x : @eq _ _ (_ ?v1 ?v2 ?v3) |- _ ] => exists (v1; (v2; (v3; tt)))
  | [ eq_x : @eq _ _ (_ ?v1 ?v2) |- _ ] => exists (v1; (v2; tt))
  | [ eq_x : @eq _ _ (_ ?v1) |- _ ] => exists (v1; tt)
  | [ eq_x : @eq _ _ _ |- _ ] => exists tt
  end;
  auto.

Require Import VeriFFI.generator.InGraph.
Require Import VeriFFI.generator.CtorDesc.
Ltac gen :=
  match goal with
  | [ |- @Discriminator _ _ ] => discriminating
  | [ |- @reflector _ _ _ _ ] => reflecting
  | _ => in_graph_gen_tac
  end.

Local Obligation Tactic := gen.

(* Unset MetaCoq Strict Unquote Universe Mode. *)
(* MetaCoq Run (in_graph_gen bool). *)
(* MetaCoq Run (descs_gen bool). *)
(* MetaCoq Run (disc_gen bool). *)

(* MetaCoq Run (in_graph_gen option). *)
(* MetaCoq Run (descs_gen option). *)

(* MetaCoq Run (in_graph_gen list). *)
(* MetaCoq Run (descs_gen list). *)
(* MetaCoq Run (disc_gen list). *)
