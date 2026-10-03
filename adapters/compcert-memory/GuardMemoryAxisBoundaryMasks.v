From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryBooleanScan GuardMemoryFootprintCapabilities GuardMemoryNaryAffineExpressions GuardMemoryRecursiveSource.
From GuardMemory Require Import GuardMemoryAxisBoundaryMath GuardMemoryAxisBoundaryCells GuardMemoryAxisBoundaryScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_affine_axis_boundary_masks_statement layout counters zero flag bounds masks first second first_expression second_expression :=
  match masks with
  | [] => Sskip
  | mask::rest => Ssequence
      (memory_affine_axis_boundary_mask_statement layout counters zero flag bounds mask first second first_expression second_expression)
      (memory_affine_axis_boundary_masks_statement layout counters zero flag bounds rest first second first_expression second_expression)
  end.

Theorem memory_affine_axis_boundary_masks_execution first_expression second_expression first_term second_term
  layout counters zero bounds counts masks fe ge locals original memory extent first second flag live :
  memory_encode_nary_index layout first_expression = Some first_term ->
  memory_encode_nary_index layout second_expression = Some second_term ->
  NoDup layout -> NoDup counters -> length layout = length counts -> length counters = length counts ->
  first <> second -> extent <= Int.max_signed+1 ->
  Forall (fun count => 0 <= count /\ signed_range count) counts ->
  (forall identifier, In identifier counters -> ~ In identifier (bounds++zero::first::second::live) /\ identifier <> flag) ->
  ~ In flag (bounds++zero::first::second::live) ->
  memory_nest_bindings bounds counts original ->
  (forall coordinates, Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell first (memory_nary_index_value first_term coordinates)) /\
    memory_cell_capable (memory_multi_pointer_locations original extent) memory
      (point_cell second (memory_nary_index_value second_term coordinates))) ->
  Forall (fun mask => length mask = length counts) masks ->
  forall current accepted,
    temp_agree (bounds++first::second::live) original current ->
    current ! zero = Some (Vint Int.zero) -> current ! flag = Some (memory_boolean_word accepted) ->
    exists after,
      exec_stmt fe ge locals current memory
        (memory_affine_axis_boundary_masks_statement layout counters zero flag bounds masks first second first_expression second_expression)
        E0 after memory Out_normal /\
      temp_agree (bounds++zero::first::second::live) current after /\
      after ! flag = Some (memory_boolean_word (accepted && forallb
        (memory_affine_axis_boundary_mask_check (memory_multi_pointer_locations original extent) counts first second first_term second_term) masks)).
Proof.
  intros FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE COUNTER_UNIQUE SOURCE_LENGTH COUNTER_LENGTH DISTINCT EXTENT
    RANGES FRESH FLAG_FRESH WORDS CAPS MASKS.
  induction MASKS as [|mask masks MASK MASKS IH]; intros current accepted FRAME ZERO FLAG.
  - exists current; split; [constructor|split; [apply temp_agree_refl|cbn; rewrite andb_true_r; exact FLAG]].
  - destruct (@memory_affine_axis_boundary_mask_execution first_expression second_expression first_term second_term
      layout counters zero bounds counts mask fe ge locals original current memory extent first second flag live accepted
      FIRST_ENCODE SECOND_ENCODE SOURCE_UNIQUE COUNTER_UNIQUE SOURCE_LENGTH COUNTER_LENGTH MASK DISTINCT EXTENT
      RANGES FRESH FLAG_FRESH WORDS FRAME ZERO FLAG CAPS) as [middle [HEAD [MIDDLE_FRAME MIDDLE_FLAG]]].
    assert (PUBLIC : temp_agree (bounds++first::second::live) original middle).
    { eapply temp_agree_trans; [exact FRAME|].
      eapply temp_agree_weaken; [|exact MIDDLE_FRAME]; intros identifier MEMBER.
      apply in_app_or in MEMBER as [MEMBER|MEMBER]; apply in_or_app;
        [left; exact MEMBER|right; cbn; auto]. }
    assert (MIDDLE_ZERO : middle ! zero = Some (Vint Int.zero)).
    { rewrite MIDDLE_FRAME by (apply in_or_app; right; cbn; auto); exact ZERO. }
    destruct (IH middle (accepted && memory_affine_axis_boundary_mask_check
      (memory_multi_pointer_locations original extent) counts first second first_term second_term mask)
      PUBLIC MIDDLE_ZERO MIDDLE_FLAG) as [after [TAIL [AFTER_FRAME AFTER_FLAG]]].
    exists after; split.
    + cbn [memory_affine_axis_boundary_masks_statement]; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eassumption.
    + split; [eapply temp_agree_trans; eassumption|cbn [forallb]; rewrite andb_assoc; exact AFTER_FLAG].
Qed.

Lemma memory_axis_boundary_masks_valid dimensions :
  Forall (fun mask => length mask = dimensions) (memory_axis_boundary_masks dimensions).
Proof. apply Forall_forall; intros mask MEMBER; apply memory_axis_boundary_mask_member; exact MEMBER. Qed.
Print Assumptions memory_affine_axis_boundary_masks_execution.
Print Assumptions memory_axis_boundary_masks_valid.
