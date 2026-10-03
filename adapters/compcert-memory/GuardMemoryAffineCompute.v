From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightRectangularStore ClightRectangularGuard ClightIndexedArray
  CompCertMemoryActions ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRegistryBackend
  GuardMemoryAffineAccessExpressions GuardMemoryAffineAccess GuardMemoryOffsetAccessRanges GuardMemorySourceValues.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_affine_compute := MemoryAffineCompute {
  memory_compute_write : memory_affine_access;
  memory_compute_reads : list memory_affine_access;
  memory_compute_value : value_expression;
  memory_compute_source : expr
}.
Definition memory_affine_compute_statement operation :=
  Sassign (memory_access_code (memory_compute_write operation)) (memory_compute_source operation).
Definition memory_affine_compute_instruction operation := MemoryInstruction
  (memory_access_instruction (memory_compute_write operation))
  (map memory_access_instruction (memory_compute_reads operation))
  (AddValue (memory_compute_value operation) (ConstantValue 0)).
Definition memory_affine_compute_requests operation :=
  map memory_access_descriptor (memory_compute_write operation::memory_compute_reads operation).
Definition memory_affine_compute_valid base row column operation :=
  memory_offset_access_valid base row column (memory_compute_write operation) /\
  Forall (memory_offset_access_valid base row column) (memory_compute_reads operation) /\
  memory_compile_source_value row column (memory_compute_reads operation) (memory_compute_value operation) =
    Some (memory_compute_source operation) /\
  memory_source_value_reads_check (memory_compute_reads operation) (memory_compute_value operation) = true.
Definition memory_affine_compute_physical ge locals i j operation before after :=
  exists block loaded value,
    rect_array_binding (memory_access_shape (memory_compute_write operation)) ge locals
      (memory_access_array (memory_compute_write operation)) block /\
    Forall2 (memory_source_access_loaded ge locals i j before) (memory_compute_reads operation) loaded /\
    evaluate_value [i;j] loaded (instruction_value (memory_affine_compute_instruction operation)) = Some value /\
    Mem.store Mint32 before block (4*memory_index_value (memory_access_index (memory_compute_write operation)) i j)
      value = Some after.

Theorem memory_affine_compute_inverse base row column operation fe ge locals temps memory after final i j :
  row <> column -> memory_affine_compute_valid base row column operation ->
  0 <= i < rectangle_outer_limit base -> 0 <= j < rectangle_stride base ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  exec_stmt fe ge locals temps memory (memory_affine_compute_statement operation) E0 after final Out_normal ->
  memory_affine_compute_physical ge locals i j operation memory final /\ after = temps.
Proof.
  intros DISTINCT [[VALID [ENCODE BOUND]] [READS [COMPILE REFERENCED]]] I J ROW COLUMN RUN.
  assert (TYPE : typeof (memory_compute_source operation) = type_int32s)
    by (eapply memory_compile_source_value_type; exact COMPILE).
  inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ ?current _ (memory_access_code _) _ _ _ |- _ =>
    destruct (@memory_affine_access_inverse (memory_access_shape (memory_compute_write operation))
      (memory_access_array (memory_compute_write operation)) (memory_access_expression (memory_compute_write operation))
      row column (memory_access_index (memory_compute_write operation)) ge locals current memory i j _ _ _
      VALID DISTINCT ENCODE ROW COLUMN (BOUND i j I J) LVALUE) as [ARRAY [OFFSET FIELD]]; subst end.
  match goal with CAST : sem_cast ?old _ _ _ = Some _ |- _ =>
    rewrite TYPE in CAST; destruct old; try discriminate CAST; inversion CAST; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion ASSIGN; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE : Mem.storev _ _ _ _ = Some _ |- _ =>
    cbn [Mem.storev] in STORE; rewrite Ptrofs.unsigned_repr in STORE by
      (apply (@rect_small_offset_bound _ VALID); pose proof (BOUND i j I J); lia);
    destruct (zle (4*memory_index_value (memory_access_index (memory_compute_write operation)) i j+size_chunk Mint32) Ptrofs.modulus);
      try discriminate STORE end.
  match goal with VALUE : eval_expr _ _ ?current _ (memory_compute_source operation) (Vint ?word) |- _ =>
    destruct (@memory_source_value_loads_exist base row column (memory_compute_reads operation) (memory_compute_value operation)
      (memory_compute_source operation) ge locals current memory i j word DISTINCT READS I J ROW COLUMN REFERENCED COMPILE VALUE)
      as [loaded LOADS];
    pose proof (@memory_source_value_evaluation_inverse base row column (memory_compute_reads operation)
      (memory_compute_value operation) (memory_compute_source operation) loaded ge locals current memory i j word
      DISTINCT READS I J ROW COLUMN LOADS COMPILE VALUE) as COMPUTE end.
  split; [|reflexivity]; exists loc,loaded,(Vint i0); split; [exact ARRAY|]; split; [exact LOADS|].
  split; [|assumption].
  cbn [instruction_value memory_affine_compute_instruction evaluate_value]; rewrite COMPUTE; cbn; rewrite Int.add_zero; reflexivity.
Qed.

Lemma memory_affine_compute_normal operation : normal_statement (memory_affine_compute_statement operation) = true.
Proof. reflexivity. Qed.
Lemma memory_affine_compute_quiet operation : quiet_statement (memory_affine_compute_statement operation) = true.
Proof. reflexivity. Qed.
Lemma memory_affine_compute_writes operation : writes_only [] (memory_affine_compute_statement operation).
Proof. constructor. Qed.
Print Assumptions memory_affine_compute_inverse.

From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryAffineReadRegistry GuardMemoryLayoutRegistry GuardMemoryLoops GuardMemoryRectangles GuardMemoryMultipleArrays.
Theorem memory_affine_compute_registry descriptors entries ge locals i j operation before after :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  NoDup (map memory_array_id entries) ->
  memory_descriptors_cover descriptors (memory_affine_compute_requests operation) ->
  0 <= memory_index_value (memory_access_index (memory_compute_write operation)) i j <
    rectangle_extent (memory_access_shape (memory_compute_write operation)) ->
  Forall (fun access => 0 <= memory_index_value (memory_access_index access) i j <
    rectangle_extent (memory_access_shape access)) (memory_compute_reads operation) ->
  (memory_affine_compute_physical ge locals i j operation before after <->
    memory_point (memory_affine_compute_instruction operation) i j
      (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros ARRAYS UNIQUE COVER WBOUND RBOUNDS.
  change (memory_descriptors_cover descriptors (memory_access_descriptor (memory_compute_write operation)::
    map memory_access_descriptor (memory_compute_reads operation))) in COVER.
  inversion COVER; subst.
  assert (SINGLE : memory_descriptors_cover descriptors [memory_access_descriptor (memory_compute_write operation)])
    by (constructor; [assumption|constructor]).
  destruct (@memory_registry_requested_array descriptors [memory_access_descriptor (memory_compute_write operation)] entries ge locals
    (memory_access_array (memory_compute_write operation)) (memory_access_shape (memory_compute_write operation))
    ARRAYS SINGLE ltac:(cbn; auto)) as [entry [MEMBER [ID [EXTENT ARRAY]]]].
  destruct (@memory_affine_reads_resolve descriptors entries ge locals i j (memory_compute_reads operation)
    ARRAYS UNIQUE ltac:(assumption) RBOUNDS) as [locations [RELATED RESOLVE]].
  assert (WRITE : memory_array_registry entries
    (exact_cell (instruction_write (memory_affine_compute_instruction operation)) [i;j]) =
    Some (MemoryLocation Mint32 (memory_array_block entry)
      (4*memory_index_value (memory_access_index (memory_compute_write operation)) i j)))
    by (eapply memory_affine_access_registry; eassumption).
  assert (READ : resolve_cells (memory_read_cells (memory_affine_compute_instruction operation) [i;j])
    (memory_array_registry entries) = Some locations).
  { unfold memory_read_cells; cbn [memory_affine_compute_instruction instruction_reads]; rewrite map_map; exact RESOLVE. }
  unfold memory_point.
  rewrite (@resolved_instruction_execution (memory_affine_compute_instruction operation) [i;j] (memory_array_registry entries)
    (MemoryLocation Mint32 (memory_array_block entry)
      (4*memory_index_value (memory_access_index (memory_compute_write operation)) i j)) locations before after WRITE READ).
  split.
  - intros [block [loaded [value [BINDING [LOADS [COMPUTE STORE]]]]]].
    assert (SAME : block=memory_array_block entry) by (eapply rect_array_binding_unique; eassumption); subst block.
    exists loaded,value; split; [apply (proj1 (@memory_affine_reads_loads ge locals i j _ _ RELATED before loaded)); exact LOADS|].
    split; assumption.
  - intros [loaded [value [LOADS [COMPUTE STORE]]]].
    exists (memory_array_block entry),loaded,value; split; [exact ARRAY|]; split.
    + apply (proj2 (@memory_affine_reads_loads ge locals i j _ _ RELATED before loaded)); exact LOADS.
    + split; assumption.
Qed.
Print Assumptions memory_affine_compute_registry.
