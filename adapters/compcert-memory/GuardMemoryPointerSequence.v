From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryNaryLoops GuardMemoryNarySequence
  GuardMemoryNaryCompute GuardMemoryNaryRanges GuardMemoryPointerCompute GuardMemoryPointerRegistry
  GuardMemoryPointerNaryAccess GuardMemoryPointerSourceAccess GuardMemoryNaryAffineAccess GuardMemoryAffineSourceExpressions GuardMemoryBufferOffsets.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Inductive memory_pointer_sequence_physical block base values : list memory_nary_compute -> mem -> mem -> Prop :=
| PointerSequenceNil : forall memory, memory_pointer_sequence_physical block base values [] memory memory
| PointerSequenceCons : forall operation operations before middle final,
    memory_pointer_compute_physical block base values operation before middle ->
    memory_pointer_sequence_physical block base values operations middle final ->
    memory_pointer_sequence_physical block base values (operation::operations) before final.
Lemma memory_pointer_sequence_normal operations body :
  flatten_region body = map memory_pointer_compute_statement operations -> normal_statement body = true.
Proof. intro BODY; apply flatten_normal_certificate; rewrite BODY; apply Forall_map,Forall_forall; intros; reflexivity. Qed.
Lemma memory_pointer_sequence_quiet operations body :
  flatten_region body = map memory_pointer_compute_statement operations -> quiet_statement body = true.
Proof. intro BODY; apply flatten_quiet_certificate; rewrite BODY; apply Forall_map,Forall_forall; intros; reflexivity. Qed.
Lemma memory_pointer_sequence_writes operations body :
  flatten_region body = map memory_pointer_compute_statement operations -> writes_only [] body.
Proof. intro BODY; apply flatten_writes_certificate; rewrite BODY; apply Forall_map,Forall_forall; intros; constructor. Qed.
Lemma memory_pointer_statement_has_base operation fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory (memory_pointer_compute_statement operation) E0 after final Out_normal ->
  exists block base, temps ! (memory_nary_access_array (memory_nary_compute_write operation)) = Some (Vptr block base).
Proof.
  intro RUN; inversion RUN; subst.
  match goal with ACCESS : eval_lvalue _ _ _ _ (memory_pointer_nary_code _) _ _ _ |- _ =>
    destruct (@memory_pointer_lvalue_has_base ge locals _ memory (memory_nary_access_array (memory_nary_compute_write operation))
      (memory_source_affine_code (memory_nary_access_expression (memory_nary_compute_write operation))) _ _ _
      (memory_source_affine_type _) ACCESS) as [base POINTER]; eauto end.
Qed.
Lemma memory_pointer_sequence_tail_inverse limits operations layout pointer extent fe ge locals valuation temps memory after final block base :
  Forall (memory_pointer_compute_valid limits layout pointer extent) operations ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  temps ! pointer = Some (Vptr block base) ->
  tail_execution fe ge locals (map memory_pointer_compute_statement operations) temps memory after final ->
  memory_pointer_sequence_physical block base (map valuation layout) operations memory final /\ after = temps.
Proof.
  intros CERT RANGE; revert temps memory after final; induction CERT as [|operation operations HEAD CERT IH];
    intros temps memory after final WORDS POINTER RUN; cbn in RUN; inversion RUN; subst.
  - split; [constructor|reflexivity].
  - match goal with POINT : exec_stmt _ _ _ _ _ (memory_pointer_compute_statement _) _ _ _ _ |- _ =>
      destruct (@memory_pointer_compute_inverse limits layout pointer extent operation fe ge locals _ _ _ _ valuation block base
        HEAD RANGE WORDS POINTER POINT) as [ACT TEMPS]; subst end.
    match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ WORDS POINTER TAIL) as [REST EXIT] end.
    split; [econstructor; eauto|exact EXIT].
Qed.
Theorem memory_pointer_sequence_point_execution limits layout pointer extent block base values operations :
  Forall (memory_pointer_compute_valid limits layout pointer extent) operations -> memory_nary_ranges limits values ->
  forall before after,
    (memory_pointer_sequence_physical block base values operations before after <->
      memory_nary_sequence_point (map memory_nary_compute_instruction operations) values
        (RuntimeState (memory_pointer_buffer_locations pointer block base extent) before)
        (RuntimeState (memory_pointer_buffer_locations pointer block base extent) after)).
Proof.
  intro CERT; induction CERT as [|operation operations HEAD CERT IH]; intros RANGE before after;
    unfold memory_nary_sequence_point; cbn [map].
  - split; intro RUN; inversion RUN; subst; constructor.
  - split; intro RUN.
    + inversion RUN; subst.
      eapply Iter.IProgress with (st2 := RuntimeState (memory_pointer_buffer_locations pointer block base extent) middle).
      * apply (proj1 (@memory_pointer_compute_registry limits layout pointer extent operation block base values before middle HEAD RANGE)); assumption.
      * apply IH; assumption.
    + inversion RUN; subst.
      match goal with POINT : memory_nary_point _ _ _ ?middle |- _ =>
        destruct middle as [locations middle_memory];
        assert (LOCATIONS : locations = memory_pointer_buffer_locations pointer block base extent)
          by (exact (@memory_nary_point_locations _ values _ _ POINT)); subst locations end.
      eapply PointerSequenceCons with (middle := middle_memory).
      * apply (proj2 (@memory_pointer_compute_registry limits layout pointer extent operation block base values before middle_memory HEAD RANGE)); assumption.
      * apply IH; assumption.
Qed.
Print Assumptions memory_pointer_sequence_tail_inverse.
Print Assumptions memory_pointer_sequence_point_execution.
