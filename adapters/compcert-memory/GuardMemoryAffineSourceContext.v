From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From Guard Require Import ClightCondition ClightGuard.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_source_other_parameters row bound expression :=
  nodup Pos.eq_dec (filter (fun identifier => negb (Pos.eqb identifier row || Pos.eqb identifier bound))
    (memory_source_affine_reads expression)).
Definition memory_source_context row bound expression := bound::memory_source_other_parameters row bound expression.
Lemma memory_source_other_parameter_member row bound expression identifier :
  In identifier (memory_source_other_parameters row bound expression) <->
    In identifier (memory_source_affine_reads expression) /\ identifier <> row /\ identifier <> bound.
Proof.
  unfold memory_source_other_parameters; rewrite nodup_In,filter_In.
  rewrite Bool.negb_true_iff,Bool.orb_false_iff,!Pos.eqb_neq; tauto.
Qed.
Lemma memory_source_context_read row bound expression identifier :
  In identifier (memory_source_affine_reads expression) -> identifier <> row ->
  In identifier (memory_source_context row bound expression).
Proof.
  intros MEMBER OTHER; unfold memory_source_context; cbn.
  destruct (Pos.eq_dec identifier bound) as [SAME|DISTINCT]; [left; symmetry; exact SAME|].
  right; apply memory_source_other_parameter_member; auto.
Qed.
Theorem memory_source_context_unique row bound expression : NoDup (memory_source_context row bound expression).
Proof.
  unfold memory_source_context; constructor.
  - intro MEMBER; apply memory_source_other_parameter_member in MEMBER; tauto.
  - unfold memory_source_other_parameters; apply NoDup_nodup.
Qed.
Lemma memory_source_context_member row bound expression identifier :
  In identifier (memory_source_context row bound expression) ->
    identifier = bound \/ In identifier (memory_source_affine_reads expression).
Proof.
  unfold memory_source_context; cbn; intros [SAME|MEMBER]; [auto|].
  right; apply memory_source_other_parameter_member in MEMBER; tauto.
Qed.
Theorem memory_source_context_typed context temps :
  (forall identifier, In identifier context -> exists word, temps ! identifier = Some (Vint word)) ->
  MemoryNested.A.typed_view context (map (memory_source_word_valuation temps) context) temps.
Proof.
  intros WORDS index identifier POSITION.
  assert (MEMBER : In identifier context) by (eapply nth_error_In; exact POSITION).
  destruct (WORDS identifier MEMBER) as [word WORD].
  exists word; split; [exact WORD|].
  change (@List.nth_error positive context index = Some identifier) in POSITION.
  assert (VALUE : nth_error (map (memory_source_word_valuation temps) context) index =
    Some (memory_source_word_valuation temps identifier)) by (rewrite List.nth_error_map,POSITION; reflexivity).
  apply nth_error_nth with (d := 0) in VALUE; rewrite VALUE.
  unfold memory_source_word_valuation; rewrite WORD; reflexivity.
Qed.
Print Assumptions memory_source_context_typed.
