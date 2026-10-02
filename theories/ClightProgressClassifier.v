From Stdlib Require Import Bool List Arith Lia.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightSyntaxEquality ClightFiniteRegion ClightCountedLoop
  ClightCountedProtocol ClightRegionProgress.

(** Parsing only proposes a shape. Full AST equality binds the certificate,
    including signed types, iterator increment, and attributes. *)
Definition propose_counted_shape (source : statement) : option (ident * ident * statement) :=
  match source with
  | Sloop (Sifthenelse
      (Ebinop Olt (Etempvar iterator _) (Etempvar bound _) _) body Sbreak) _ =>
      Some (iterator, bound, body)
  | _ => None
  end.

Definition counted_progress_supported (source : statement) : bool :=
  match propose_counted_shape source with
  | Some (iterator, bound, body) =>
      if statement_eq source (counted_loop iterator bound body)
      then if peq iterator bound then false else memory_body body
      else false
  | None => false
  end.

Lemma counted_progress_supported_sound source : counted_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold counted_progress_supported.
  destruct (propose_counted_shape source) as [[[iterator bound] body]|]; try discriminate.
  destruct (statement_eq source (counted_loop iterator bound body)) as [EQ|NE]; try discriminate.
  destruct (peq iterator bound) as [SAME|DISTINCT]; try discriminate.
  intro BODY; subst source. exists (@counted_progress iterator bound DISTINCT body BODY); exact I.
Qed.

Definition progress_supported (source : statement) : bool :=
  (finite_statement source && negb (Nat.eqb (statement_weight source) 0)) ||
    counted_progress_supported source.

Theorem progress_supported_sound source : progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold progress_supported; rewrite orb_true_iff; intros [FINITE | COUNTED].
  - apply andb_true_iff in FINITE as [FIN POS].
    apply negb_true_iff, Nat.eqb_neq in POS.
    assert (ACTIVE : source <> Sskip) by (intro EQ; subst source; apply POS; reflexivity).
    exists (@finite_progress source FIN ACTIVE); exact I.
  - apply counted_progress_supported_sound; exact COUNTED.
Qed.

Example strict_loop_supported :
  progress_supported (counted_loop 1%positive 2%positive Sskip) = true.
Proof. vm_compute; reflexivity. Qed.

Example identical_counter_and_bound_refused :
  progress_supported (counted_loop 1%positive 1%positive Sskip) = false.
Proof. vm_compute; reflexivity. Qed.

Example mutable_counter_body_refused :
  progress_supported (counted_loop 1%positive 2%positive (counter_increment 1%positive)) = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions progress_supported_sound.
