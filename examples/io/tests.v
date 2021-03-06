From CertiCoq.Plugin Require Import CertiCoq.

Require Import ExtLib.Structures.Monad.
Require Import String.

Inductive itree (E : Type -> Type) (R : Type) : Type :=
| Ret (r : R)
| Vis {X : Type} (e : E X) (k : X -> itree E R)
| Tau (t : itree E R).

Arguments Ret [E R].
Arguments Vis [E R] {X}.
Arguments Tau [E R].

Definition trigger {E : Type -> Type} {A : Type} (e : E A) : itree E A :=
  Vis e (fun x => Ret x).

Fixpoint ibind {E : Type -> Type} {A B : Type}
               (t : itree E A) (k : A -> itree E B) : itree E B :=
  match t with
  | Ret r => k r
  | Vis _ e h => Vis e (fun x => ibind (h x) k)
  | Tau t' => Tau (ibind t' k)
  end.

Instance Monad_itree {E} : Monad (itree E) :=
  {| ret := fun _ x => Ret x ; bind := @ibind _ |}.

Inductive console : Type -> Type :=
| print_string : string -> console unit
| scan_string : console string.

Import MonadNotation.
Open Scope monad_scope.

Definition prog : itree console unit :=
  trigger (print_string "What's your name?") ;;
  name <- trigger scan_string ;;
  trigger (print_string ("Hello " ++ name ++ "!")).

CertiCoq Generate Glue -file "glue" [itree, console, string, unit].
CertiCoq Compile prog.
