Require Import VST.floyd.proofauto.
Require Import io.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import Coq.Strings.Ascii.
Require Import ITree.ITree.

Require Import VST.veric.juicy_extspec.

Require Export io_events.

Require Export ITree.ITree.
Require Export ITree.Eq.Eq.
Require Export ITree.Eq.SimUpToTaus.

Require Import prog.

Locate byte.
Check translate.

Fixpoint mytree_to_itree {E : Type -> Type} {A : Type} (t : mytree E A) : itree E A :=
  match t with
  | MyRet t => Ret t
  | MyTau t' => Tau (mytree_to_itree t')
  | MyVis _ e h => Vis e (fun x => mytree_to_itree (h x))
  end.

Definition stdin := 0%nat.
Definition stdout := 1%nat.

Check stdout.

Definition runitree_spec {CS : compspecs} :=
  WITH sh : share, buf : val, msg : list byte, len : Z, rest : list val, k : IO_itree
  PRE [ tptr tuchar, tint ]
    PROP (readable_share sh)
    PARAMS (buf; Vint (Int.repr (Zlength msg))) GLOBALS ()
    SEP (ITREE (write_list stdout msg ;; k);
           data_at sh (tarray tuchar len) (map Vubyte msg ++ rest) buf)
  POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (Zlength msg))))
    SEP (ITREE k;
           data_at sh (tarray tuchar len) (map Vubyte msg ++ rest) buf).

(* Print offset_val. *)
Print field_address.
(* Print field_address0. *)

Definition make_bytestring_padding (padding : Z) : list byte :=
  Zrepeat Byte.zero padding ++ [Byte.repr padding].

(* separation logic predicate to represent primitive strings in OCaml style *)
Definition bytestring_pred (sh : Share.t) (s : list byte) (p : val) : mpred :=
  EX (header : Ptrofs.int) (padding : Z),
    let bits : Z := (sizeof size_t * 8)%Z in
    let words : Ptrofs.int :=
        Ptrofs.shr header (Ptrofs.repr (bits - 10)) in
    let tag : Ptrofs.int :=
        let n := Ptrofs.repr (bits - 8) in
        Ptrofs.shr (Ptrofs.shl header n) n in
    let len : Z := ((Ptrofs.intval words * sizeof size_t) - padding)%Z in
      !! (Ptrofs.intval tag = 252) &&
      ( data_at sh size_t (Vptrofs header) (offset_val (-1) p)
      * data_at sh (tarray tschar len)
                   (map Vbyte (s ++ make_bytestring_padding padding)) p).

Definition bytestrlen_spec :=
 DECLARE _bytestrlen
  WITH sh : share, s : list byte, str : val
  PRE [ size_t ]
    PROP (readable_share sh)
    PARAMS (str)
    SEP (bytestring_pred sh s str)
  POST [ size_t ]
    PROP ()
    RETURN (Vptrofs (Ptrofs.repr (Zlength s)))
    SEP (bytestring_pred sh s str).

Definition Gprog : funspecs :=
  ltac:(with_library prog [ bytestrlen_spec ]).

Lemma body_bytestrlen: semax_body Vprog Gprog f_bytestrlen bytestrlen_spec.
Proof.
  leaf_function.
  start_function.
  unfold bytestring_pred.
  Intros header padding.

  forward.
  autorewrite with norm.
  entailer!.
  destruct str; entailer.

  forward.
  hint.
  deadvars!.
  autorewrite with norm.
  forward.
  Print denote_tc_iszero.
  unfold denote_tc_iszero.

  forward.

  hint.

  (* unfold offset_val. *)

(* try doing cast in separate statement *)

(* Set Printing All. *)

  hint.
  Print string.
  (* Check sem_sub_pi. *)
  (* Check field_address. *)
  (* evar (t : type); evar (gfs : list gfield); evar (p : val). *)
  (* Check str. *)
  (* assert_PROP (force_val (sem_sub_pi tulong Signed str (Vint (Int.repr 1))) *)
  (*              = field_address ?t ?gfs str). *)

  (* Print gfield. *)
  (* Print force_val. *)
  (* Print sem_sub_pi. *)
  (* entailer!. *)
  (* admit. *)

  (* forward. *)
Admitted.
