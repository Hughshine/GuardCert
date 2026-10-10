From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.polygen Require Import PolIRs PolyTest.
From Vpl Require Import Impure.
From Guard Require Import PolCertCandidateRepresentation.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** A finite integer-affine decision tree certifies union coverage. Proposals
    are untrusted; each leaf is checked using the existing domain oracle.
    This library does not establish instruction or machine correspondence. *)
Module PolCertPieceDomainCoverFor (IRs : POLIRS).
Module C := PolCertCandidateRepresentationFor IRs.
Inductive cover_witness :=
| CoverPiece (piece : nat)
| CoverEmpty
| CoverSplit (row : list Z*Z) (yes no : cover_witness).
Fixpoint check_cover source pieces witness := match witness with
  | CoverPiece piece=>match nth_error pieces piece with
    | Some domain=>C.memory_check_domain_inclusion source domain
    | None=>pure false end
  | CoverEmpty=>isBottom source
  | CoverSplit row yes no=>
    BIND first <- check_cover (row::source) pieces yes -;
    if first then check_cover (neg_constraint row::source) pieces no else pure false
  end.
Theorem check_cover_sound witness : forall source pieces,
  mayReturn (check_cover source pieces witness) true ->
  forall index, in_poly index source=true ->
  exists piece, In piece pieces /\ in_poly index piece=true.
Proof.
  induction witness as [piece| |row yes IHYES no IHNO]; intros source pieces CHECK index SOURCE.
  - cbn in CHECK; destruct (nth_error pieces piece) as [domain|] eqn:PIECE;
      [|apply mayReturn_pure in CHECK; discriminate].
    exists domain; split; [eapply nth_error_In; exact PIECE|].
    eapply C.memory_check_domain_inclusion_correct; eassumption.
  - pose proof (@isBottom_correct_1 source true CHECK index); congruence.
  - cbn in CHECK; bind_imp_destruct CHECK accepted FIRST; destruct accepted;
      [|apply mayReturn_pure in CHECK; discriminate].
    destruct (satisfies_constraint index row) eqn:ROW.
    + eapply IHYES; [exact FIRST|].
      change (satisfies_constraint index row && in_poly index source=true); rewrite ROW,SOURCE; reflexivity.
    + eapply IHNO; [exact CHECK|].
      change (satisfies_constraint index (neg_constraint row) && in_poly index source=true).
      rewrite neg_constraint_correct,ROW,SOURCE; reflexivity.
Qed.
Definition disjoint first second := forall index,
  in_poly index first=true -> in_poly index second=false.
Lemma disjoint_symmetric first second : disjoint first second -> disjoint second first.
Proof.
  intros DISJOINT index SECOND; destruct (in_poly index first) eqn:FIRST; [|reflexivity].
  specialize (DISJOINT index FIRST); congruence.
Qed.
Lemma checked_disjoint first second : mayReturn (isBottom (first++second)) true -> disjoint first second.
Proof.
  intros CHECK index FIRST.
  pose proof (@isBottom_correct_1 (first++second) true CHECK index) as EMPTY.
  rewrite in_poly_app,FIRST in EMPTY; exact EMPTY.
Qed.
Fixpoint check_disjoint_head first rest := match rest with
  | []=>pure true
  | second::rest=>BIND empty <- isBottom (first++second) -;
    if empty then check_disjoint_head first rest else pure false end.
Lemma check_disjoint_head_sound first rest :
  mayReturn (check_disjoint_head first rest) true -> Forall (disjoint first) rest.
Proof.
  induction rest as [|second rest IH]; cbn; intro CHECK; [constructor|].
  bind_imp_destruct CHECK empty EMPTY; destruct empty;
    [|apply mayReturn_pure in CHECK; discriminate].
  constructor; [apply checked_disjoint; exact EMPTY|apply IH; exact CHECK].
Qed.
Fixpoint check_disjoint_family domains := match domains with
  | []=>pure true
  | first::rest=>BIND apart <- check_disjoint_head first rest -;
    if apart then check_disjoint_family rest else pure false end.
Theorem check_disjoint_family_sound domains :
  mayReturn (check_disjoint_family domains) true ->
  forall first second i j, nth_error domains i=Some first -> nth_error domains j=Some second ->
    i<>j -> disjoint first second.
Proof.
  induction domains as [|head rest IH]; cbn; intro CHECK;
    [intros first second [|i] j FIRST; discriminate|].
  bind_imp_destruct CHECK apart APART; destruct apart;
    [|apply mayReturn_pure in CHECK; discriminate].
  pose proof (@check_disjoint_head_sound head rest APART) as HEAD.
  intros first second [|i] [|j] FIRST SECOND DIFFERENT; cbn in FIRST,SECOND;
    try (exfalso; apply DIFFERENT; reflexivity).
  - inversion FIRST; subst first; apply Forall_forall with (x:=second) in HEAD;
      [exact HEAD|eapply nth_error_In; exact SECOND].
  - inversion SECOND; subst second; apply disjoint_symmetric.
    apply Forall_forall with (x:=first) in HEAD; [exact HEAD|eapply nth_error_In; exact FIRST].
  - eapply IH; [exact CHECK|exact FIRST|exact SECOND|congruence].
Qed.
End PolCertPieceDomainCoverFor.
