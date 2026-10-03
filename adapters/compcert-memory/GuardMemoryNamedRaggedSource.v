From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightStraightLine
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryNamedOperations GuardMemoryNamedRegistrySource
  GuardMemoryRaggedLoops GuardMemoryRaggedClight.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_ragged_first {S} (point : Z -> Z -> S -> S -> Prop) rows columns before after :
  rows <> O -> columns <> O -> memory_ragged_iterations point rows columns before after ->
  exists middle, point 0 0 before middle.
Proof.
  intros RP CP RUN; destruct rows as [|rows]; [contradiction|].
  unfold memory_ragged_iterations in RUN; inversion RUN; subst.
  match goal with ROW : counted_iterations _ (Z.to_nat (0+Z.of_nat columns)) _ _ _ |- _ =>
    rewrite Z.add_0_l,Nat2Z.id in ROW;
    destruct columns as [|columns]; [contradiction|]; inversion ROW; subst;
    eexists; eassumption end.
Qed.
Lemma memory_ragged_index base N M i j : rectangle_layout_valid base ->
  0 < N <= rectangle_outer_limit base -> 0 < M -> N+M-1 <= rectangle_stride base ->
  0 <= i < N -> 0 <= j < i+M ->
  0 <= i*rectangle_stride base+j < rectangle_extent base /\
  0 <= i*rectangle_stride base < rectangle_extent base.
Proof.
  intros VALID NB MB WIDTH I J; pose proof (rectangle_limits VALID) as [NS [MS [POS EXTENT]]].
  split.
  - apply rectangle_point_bound with (N := N) (M := rectangle_stride base); auto; lia.
  - replace (i*rectangle_stride base) with (i*rectangle_stride base+0) by lia.
    apply rectangle_point_bound with (N := N) (M := rectangle_stride base); auto; lia.
Qed.

Section SOURCE.
Variable base : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid base.
Variable operations : list named_array_operation.
Hypothesis LAYOUTS : Forall (named_operation_layout base) operations.
Variable row bound column inner_bound parameter : ident.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RK : row <> inner_bound.
Hypothesis NK : bound <> inner_bound.
Hypothesis CK : column <> inner_bound.
Hypothesis MC : parameter <> column.
Hypothesis MK : parameter <> inner_bound.
Hypothesis MR : parameter <> row.
Hypothesis BODY : flatten_region body = map (named_operation_statement row column) operations.
Hypothesis OUTER : flatten_region outer_body =
  [memory_ragged_setup row parameter inner_bound; rectangle_reset column;
    frontend_counted_loop column inner_bound body].

Theorem named_array_operations_ragged_source_decode fe ge locals le memory after final rows columns :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! parameter = Some (Vint (Int.repr (Z.of_nat columns))) -> signed_range (Z.of_nat rows) ->
  0 < Z.of_nat rows <= rectangle_outer_limit base -> 0 < Z.of_nat columns ->
  Z.of_nat rows+Z.of_nat columns-1 <= rectangle_stride base ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (named_array_descriptors base operations) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    L.loop_semantics (memory_ragged_sequence (map named_operation_instruction operations))
      [Z.of_nat rows;Z.of_nat columns]
      (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) /\
    after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
      (memory_ragged_settle column inner_bound (Z.of_nat columns) (Z.of_nat rows-1) le).
Proof.
  intros ZERO BOUND PARAM NS NB MB WIDTH SOURCE.
  assert (RP : rows <> O) by (intro SAME; rewrite SAME in NB; cbn in NB; lia).
  assert (CP : columns <> O) by (intro SAME; rewrite SAME in MB; cbn in MB; lia).
  pose proof (rectangle_limits VALID) as [NL [ML LIMITS]].
  destruct (@memory_ragged_source_decode fe ge locals row bound column inner_bound parameter body outer_body
    (fun i j => named_array_operations_physical ge locals i j operations) rows columns
    RN RC NC RK NK CK MC MK MR RP NS
    ltac:(intros; unfold signed_range in *; change Int.min_signed with (-2147483648) in *; lia)
    (@named_array_operations_body_normal operations row column body BODY)
    (@named_array_operations_body_quiet operations row column body BODY)
    (@named_array_operations_body_writes operations row column body BODY) OUTER
    ltac:(intros i j temps before next final' I J ROW COLUMN RUN;
      destruct (@memory_ragged_index base (Z.of_nat rows) (Z.of_nat columns) i j VALID NB MB WIDTH I J) as [INDEX READ_INDEX];
      apply flatten_region_execution in RUN; rewrite BODY in RUN;
      exact (@named_array_operations_tail_inverse base operations row column fe ge locals i j temps before next final'
        VALID LAYOUTS INDEX READ_INDEX ROW COLUMN RUN))
    le memory after final ZERO BOUND PARAM SOURCE) as [ITER EXIT].
  destruct (@memory_ragged_first mem (fun i j => named_array_operations_physical ge locals i j operations)
    rows columns memory final RP CP ITER) as [first HEAD].
  destruct (@named_array_operations_registry base operations ge locals memory first VALID LAYOUTS HEAD)
    as [entries [ARRAYS [UNIQUE POINTERS]]].
  exists entries; split; [exact ARRAYS|]; split; [exact UNIQUE|]; split; [exact POINTERS|]; split; [|exact EXIT].
  apply (proj1 (@memory_ragged_sequence_lift (memory_array_registry entries)
    (map named_operation_instruction operations) (fun i j => named_array_operations_physical ge locals i j operations)
    rows columns memory final
    ltac:(intros i j before next I J;
      destruct (@memory_ragged_index base (Z.of_nat rows) (Z.of_nat columns) i j VALID NB MB WIDTH I J) as [INDEX READ_INDEX];
      apply named_array_operations_point_execution with (base := base) (universe := operations);
      [exact ARRAYS|exact UNIQUE|exact LAYOUTS|apply Forall_forall; auto|exact INDEX|exact READ_INDEX]))).
  exact ITER.
Qed.
End SOURCE.
Print Assumptions named_array_operations_ragged_source_decode.
