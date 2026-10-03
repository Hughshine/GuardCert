From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightRectangularStore ClightRectangularGuard ClightIndexedArray
  CompCertMemoryActions ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryPolyhedral GuardMemoryRegistryBackend
  GuardMemoryNaryAffineExpressions GuardMemoryNaryAffineAccess GuardMemoryNaryRanges GuardMemoryNaryAccessCheck GuardMemoryNarySourceValues.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_nary_point instruction values before after :=
  GuardMemoryInstr.instr_semantics instruction values (memory_write_cells instruction values)
    (memory_read_cells instruction values) before after.

Record memory_nary_compute := MemoryNaryCompute {
  memory_nary_compute_write : memory_nary_access;
  memory_nary_compute_reads : list memory_nary_access;
  memory_nary_compute_value : value_expression;
  memory_nary_compute_source : expr
}.
Definition memory_nary_compute_statement operation :=
  Sassign (memory_nary_access_code (memory_nary_compute_write operation)) (memory_nary_compute_source operation).
Definition memory_nary_compute_instruction operation := MemoryInstruction
  (memory_nary_access_instruction (memory_nary_compute_write operation))
  (map memory_nary_access_instruction (memory_nary_compute_reads operation))
  (AddValue (memory_nary_compute_value operation) (ConstantValue 0)).
Definition memory_nary_compute_requests operation :=
  map memory_nary_access_descriptor (memory_nary_compute_write operation::memory_nary_compute_reads operation).
Definition memory_nary_compute_valid limits layout operation :=
  memory_nary_access_valid limits layout (memory_nary_compute_write operation) /\
  Forall (memory_nary_access_valid limits layout) (memory_nary_compute_reads operation) /\
  memory_compile_nary_source_value layout (memory_nary_compute_reads operation) (memory_nary_compute_value operation) =
    Some (memory_nary_compute_source operation) /\
  memory_nary_source_value_reads_check (memory_nary_compute_reads operation) (memory_nary_compute_value operation) = true.
Definition memory_nary_compute_physical ge locals point_values operation before after :=
  exists block loaded value,
    rect_array_binding (memory_nary_access_shape (memory_nary_compute_write operation)) ge locals
      (memory_nary_access_array (memory_nary_compute_write operation)) block /\
    Forall2 (memory_nary_source_access_loaded ge locals point_values before) (memory_nary_compute_reads operation) loaded /\
    evaluate_value point_values loaded (instruction_value (memory_nary_compute_instruction operation)) = Some value /\
    Mem.store Mint32 before block (4*memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) point_values)
      value = Some after.

Theorem memory_nary_compute_inverse limits layout operation fe ge locals temps memory after final valuation :
  memory_nary_compute_valid limits layout operation ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  exec_stmt fe ge locals temps memory (memory_nary_compute_statement operation) E0 after final Out_normal ->
  memory_nary_compute_physical ge locals (map valuation layout) operation memory final /\ after = temps.
Proof.
  intros [[VALID [ENCODE BOUND]] [READS [COMPILE REFERENCED]]] RANGE WORDS RUN.
  assert (TYPE : typeof (memory_nary_compute_source operation) = type_int32s)
    by (eapply memory_compile_nary_source_value_type; exact COMPILE).
  inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ ?current _ (memory_nary_access_code _) _ _ _ |- _ =>
    destruct (@memory_nary_access_lvalue_inverse (memory_nary_compute_write operation) layout valuation ge locals current memory _ _ _
      VALID ENCODE WORDS (BOUND _ RANGE) LVALUE) as [ARRAY [OFFSET FIELD]]; subst end.
  match goal with CAST : sem_cast ?old _ _ _ = Some _ |- _ =>
    rewrite TYPE in CAST; destruct old; try discriminate CAST; inversion CAST; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion ASSIGN; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE : Mem.storev _ _ _ _ = Some _ |- _ =>
    cbn [Mem.storev] in STORE; rewrite Ptrofs.unsigned_repr in STORE by
      (apply (@rect_small_offset_bound _ VALID); pose proof (BOUND _ RANGE); lia);
    destruct (zle (4*memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) (map valuation layout)+size_chunk Mint32) Ptrofs.modulus);
      try discriminate STORE end.
  match goal with VALUE : eval_expr _ _ ?current _ (memory_nary_compute_source operation) (Vint ?word) |- _ =>
    destruct (@memory_nary_source_value_loads_exist limits layout (memory_nary_compute_reads operation) (memory_nary_compute_value operation)
      (memory_nary_compute_source operation) ge locals current memory valuation word READS RANGE WORDS REFERENCED COMPILE VALUE)
      as [loaded LOADS];
    pose proof (@memory_nary_source_value_evaluation_inverse limits layout (memory_nary_compute_reads operation)
      (memory_nary_compute_value operation) (memory_nary_compute_source operation) loaded ge locals current memory valuation word
      READS RANGE WORDS LOADS COMPILE VALUE) as COMPUTE end.
  split; [|reflexivity]; match type of COMPUTE with _ = Some ?computed => exists loc,loaded,computed end; split; [exact ARRAY|]; split; [exact LOADS|].
  split; [|assumption].
  cbn [instruction_value memory_nary_compute_instruction evaluate_value]; rewrite COMPUTE; cbn; rewrite Int.add_zero; reflexivity.
Qed.

Lemma memory_nary_compute_normal operation : normal_statement (memory_nary_compute_statement operation) = true.
Proof. reflexivity. Qed.
Lemma memory_nary_compute_quiet operation : quiet_statement (memory_nary_compute_statement operation) = true.
Proof. reflexivity. Qed.
Lemma memory_nary_compute_writes operation : writes_only [] (memory_nary_compute_statement operation).
Proof. constructor. Qed.
Print Assumptions memory_nary_compute_inverse.

From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryNaryReadRegistry GuardMemoryLayoutRegistry GuardMemoryLoops GuardMemoryRectangles GuardMemoryMultipleArrays.
Theorem memory_nary_compute_registry descriptors entries ge locals point_values operation before after :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  NoDup (map memory_array_id entries) ->
  memory_descriptors_cover descriptors (memory_nary_compute_requests operation) ->
  0 <= memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) point_values <
    rectangle_extent (memory_nary_access_shape (memory_nary_compute_write operation)) ->
  Forall (fun access => 0 <= memory_nary_index_value (memory_nary_access_index access) point_values <
    rectangle_extent (memory_nary_access_shape access)) (memory_nary_compute_reads operation) ->
  (memory_nary_compute_physical ge locals point_values operation before after <->
    memory_nary_point (memory_nary_compute_instruction operation) point_values
      (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros ARRAYS UNIQUE COVER WBOUND RBOUNDS.
  change (memory_descriptors_cover descriptors (memory_nary_access_descriptor (memory_nary_compute_write operation)::
    map memory_nary_access_descriptor (memory_nary_compute_reads operation))) in COVER.
  inversion COVER; subst.
  assert (SINGLE : memory_descriptors_cover descriptors [memory_nary_access_descriptor (memory_nary_compute_write operation)])
    by (constructor; [assumption|constructor]).
  destruct (@memory_registry_requested_array descriptors [memory_nary_access_descriptor (memory_nary_compute_write operation)] entries ge locals
    (memory_nary_access_array (memory_nary_compute_write operation)) (memory_nary_access_shape (memory_nary_compute_write operation))
    ARRAYS SINGLE ltac:(cbn; auto)) as [entry [MEMBER [ID [EXTENT ARRAY]]]].
  destruct (@memory_nary_reads_resolve descriptors entries ge locals point_values (memory_nary_compute_reads operation)
    ARRAYS UNIQUE ltac:(assumption) RBOUNDS) as [locations [RELATED RESOLVE]].
  assert (WRITE : memory_array_registry entries
    (exact_cell (instruction_write (memory_nary_compute_instruction operation)) point_values) =
    Some (MemoryLocation Mint32 (memory_array_block entry)
      (4*memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) point_values)))
    by (eapply memory_nary_access_registry; eassumption).
  assert (READ : resolve_cells (memory_read_cells (memory_nary_compute_instruction operation) point_values)
    (memory_array_registry entries) = Some locations).
  { unfold memory_read_cells; cbn [memory_nary_compute_instruction instruction_reads]; rewrite map_map; exact RESOLVE. }
  unfold memory_nary_point.
  rewrite (@resolved_instruction_execution (memory_nary_compute_instruction operation) point_values (memory_array_registry entries)
    (MemoryLocation Mint32 (memory_array_block entry)
      (4*memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) point_values)) locations before after WRITE READ).
  split.
  - intros [block [loaded [value [BINDING [LOADS [COMPUTE STORE]]]]]].
    assert (SAME : block=memory_array_block entry) by (eapply rect_array_binding_unique; eassumption); subst block.
    exists loaded,value; split; [apply (proj1 (@memory_nary_reads_loads ge locals point_values _ _ RELATED before loaded)); exact LOADS|].
    split; assumption.
  - intros [loaded [value [LOADS [COMPUTE STORE]]]].
    exists (memory_array_block entry),loaded,value; split; [exact ARRAY|]; split.
    + apply (proj2 (@memory_nary_reads_loads ge locals point_values _ _ RELATED before loaded)); exact LOADS.
    + split; assumption.
Qed.
Print Assumptions memory_nary_compute_registry.
