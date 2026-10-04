From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightStraightLine ClightFiniteRegion.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryNaryAffineAccess
  GuardMemoryNaryCompute GuardMemoryInstr GuardMemoryFlatArrayBackend
  GuardMemoryPointerNaryAccess GuardMemoryPointerCompute GuardMemoryMultiPointerCompute
  GuardMemorySourceValueInterface GuardMemorySourceParameters.
From GuardMemory Require Import GuardMemoryPointerDefinedIndex.
Import ListNotations.
Set Implicit Arguments.

Definition memory_pointer_operation_address_reads operation :=
  memory_source_affine_reads (memory_nary_access_expression (memory_nary_compute_write operation)) ++
  flat_map (fun access => memory_source_affine_reads (memory_nary_access_expression access))
    (memory_nary_compute_reads operation).

Theorem memory_pointer_operation_address_words limits layout scalars extent operation
  fe ge locals temps memory after final :
  memory_multi_pointer_compute_valid limits layout scalars extent operation ->
  exec_stmt fe ge locals temps memory (memory_pointer_compute_statement operation) E0 after final Out_normal ->
  forall identifier, In identifier (memory_pointer_operation_address_reads operation) ->
    exists word, temps ! identifier = Some (Vint word).
Proof.
  intros [WRITE [READS [COMPILE REFERENCED]]] RUN.
  assert (READ_TYPES : Forall (fun code => typeof code = type_int32s)
    (map memory_pointer_nary_code (memory_nary_compute_reads operation))).
  { apply Forall_map,Forall_forall; intros; reflexivity. }
  assert (TYPE : typeof (memory_nary_compute_source operation) = type_int32s)
    by (eapply memory_source_flat_type; [apply memory_pointer_register_types|exact READ_TYPES|exact COMPILE]).
  inversion RUN; subst after.
  match goal with CAST : sem_cast ?old _ _ _ = Some _ |- _ =>
    rewrite TYPE in CAST; destruct old; try discriminate CAST; inversion CAST; subst end.
  intros identifier MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
  - eapply memory_pointer_source_affine_used_word; [|exact MEMBER].
    match goal with LVALUE : eval_lvalue _ _ _ _ (memory_pointer_nary_code _) _ _ _ |- _ => exact LVALUE end.
  - apply in_flat_map in MEMBER as [access [ACCESS MEMBER]].
    apply In_nth_error in ACCESS as [index LOOKUP].
    assert (READ_LOOKUP : nth_error (map memory_pointer_nary_code (memory_nary_compute_reads operation)) index =
      Some (memory_pointer_nary_code access)) by (rewrite nth_error_map,LOOKUP; reflexivity).
    pose proof (@memory_source_reads_check_sound _ _ REFERENCED _ _ READ_LOOKUP) as USED.
    match goal with VALUE : eval_expr _ _ _ _ (memory_nary_compute_source operation) (Vint ?result) |- _ =>
      destruct (@memory_source_value_read_inverse ge locals temps memory
        (memory_pointer_register_codes (layout++scalars))
        (map memory_pointer_nary_code (memory_nary_compute_reads operation))
        (fun code value => eval_expr ge locals temps memory code value)
        (memory_pointer_register_types (layout++scalars)) READ_TYPES
        ltac:(intros; assumption) (memory_nary_compute_value operation)
        (memory_nary_compute_source operation) result COMPILE VALUE index USED)
        as [read [word [SAME EVAL]]] end.
    rewrite READ_LOOKUP in SAME; inversion SAME; subst read.
    eapply memory_pointer_source_load_used_word; [exact EVAL|exact MEMBER].
Qed.
Print Assumptions memory_pointer_operation_address_words.

Theorem memory_pointer_sequence_address_words limits operations layout scalars extent
  fe ge locals identifier :
  Forall (memory_multi_pointer_compute_valid limits layout scalars extent) operations ->
  forall temps memory after final,
    tail_execution fe ge locals (map memory_pointer_compute_statement operations) temps memory after final ->
    forall operation, In operation operations ->
      In identifier (memory_pointer_operation_address_reads operation) ->
      exists word, temps ! identifier = Some (Vint word).
Proof.
  intro CERT; induction CERT as [|head operations HEAD CERT IH];
    intros temps memory after final RUN operation MEMBER USED; [contradiction|].
  cbn in RUN; inversion RUN; subst.
  cbn in MEMBER; destruct MEMBER as [SAME|MEMBER].
  - subst operation; eapply memory_pointer_operation_address_words; eassumption.
  - match goal with TAIL : tail_execution _ _ _ _ _ _ _ _ |- _ =>
      destruct (IH _ _ _ _ TAIL operation MEMBER USED) as [word WORD] end.
    exists word.
    match goal with POINT : exec_stmt _ _ _ _ _ (memory_pointer_compute_statement head) _ _ _ _ |- _ =>
      pose proof (@writes_only_frame _ _ _ _ _ _ _ _ _ _ POINT [] ltac:(constructor)
        identifier ltac:(cbn; tauto)) as FRAME end.
    rewrite FRAME in WORD; exact WORD.
Qed.
Print Assumptions memory_pointer_sequence_address_words.
