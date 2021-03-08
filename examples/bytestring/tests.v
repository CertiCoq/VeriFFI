From CertiCoq.Plugin Require Import CertiCoq.

Require Import Coq.Numbers.Cyclic.Int63.Int63.
Require Import ExtLib.Structures.Monad.
Require Import String.

Axioms (bytestring : Type)
       (append : bytestring -> bytestring -> bytestring)
       (pack : string -> bytestring)
       (unpack : bytestring -> string).

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
| print_string : bytestring -> console unit
| scan_string : console bytestring.

Import MonadNotation.
Open Scope monad_scope.

Definition prog : itree console unit :=
  trigger (print_string (append (pack "abcd") (pack "efgh"))).
  (* trigger (print_string (pack "hello there")). *)
  (* trigger (print_string (pack "What's your name?")) ;; *)
  (* name <- trigger scan_string ;; *)
  (* trigger (print_string (append (append (pack "Hello ") name) (pack "!"))). *)

CertiCoq Generate Glue -file "glue" [itree, console, string, unit].
CertiCoq Compile prog
         Extract Constants [
                    (* pack => "pack" with tinfo *)
                      append => "append" with tinfo
                    , pack => "pack" with tinfo
                    (* , pack => "pack" with tinfo *)
                    (* , unpack => "unpack" with tinfo *)
                    ]
  Include [ "io.h" ].
