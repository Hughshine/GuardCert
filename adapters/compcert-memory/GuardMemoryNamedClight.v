From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import RectangularIteration ClightCondition ClightNoWrap ClightCountedLoop
  ClightRectangularStore ClightRectangularGuard ClightRectangularRegion ClightFrontendLoopProtocol
  ClightStraightLine ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryMultipleArrays GuardMemoryRegistryBackend GuardMemoryNamedOperations GuardMemoryNamedRegistrySource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section SOURCE.
Variable base : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid base.
Variable operations : list named_array_operation.
Hypothesis LAYOUTS : Forall (named_operation_layout base) operations.
Variable row bound column inner_bound : ident.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RM : row <> inner_bound.
Hypothesis CM : column <> inner_bound.
Hypothesis BODY : flatten_region body = map (named_operation_statement row column) operations.
Hypothesis OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body].

Theorem named_array_operations_source_clight_decode fe ge locals le memory after final rows columns :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  signed_range (Z.of_nat rows) -> signed_range (Z.of_nat columns) ->
  0 < Z.of_nat rows <= rectangle_outer_limit base -> 0 < Z.of_nat columns <= rectangle_stride base ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (named_array_descriptors base operations) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    L.loop_semantics (memory_rectangle_sequence (map named_operation_instruction operations))
      [Z.of_nat rows;Z.of_nat columns]
      (RuntimeState (memory_array_registry entries) memory)
      (RuntimeState (memory_array_registry entries) final) /\
    after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
      (PTree.set column (Vint (Int.repr (Z.of_nat columns))) le).
Proof.
  intros ZERO BOUND INNER NS MS NB MB SOURCE.
  destruct (@named_array_operations_source_clight_iterations base VALID operations LAYOUTS
    row bound column inner_bound body outer_body RN RC NC RM CM BODY OUTER
    fe ge locals le memory after final rows columns ZERO BOUND INNER NS MS NB MB SOURCE)
    as [ITER EXIT].
  assert (POS : rows <> O) by (intro SAME; rewrite SAME in NB; cbn in NB; lia).
  assert (POS' : columns <> O) by (intro SAME; rewrite SAME in MB; cbn in MB; lia).
  destruct (@rectangular_first mem (fun i j => named_array_operations_physical ge locals i j operations)
    rows columns memory final POS POS' ITER) as [first HEAD].
  destruct (@named_array_operations_registry base operations ge locals memory first VALID LAYOUTS HEAD)
    as [entries [ARRAYS [UNIQUE POINTERS]]].
  exists entries; split; [exact ARRAYS|]; split; [exact UNIQUE|]; split; [exact POINTERS|]; split; [|exact EXIT].
  apply (proj1 (@memory_rectangle_sequence_lift (memory_array_registry entries)
    (map named_operation_instruction operations)
    (fun i j => named_array_operations_physical ge locals i j operations) rows columns memory final
    ltac:(intros i j before after' I J;
      apply named_array_operations_point_execution with (base := base) (universe := operations);
      [exact ARRAYS|exact UNIQUE|exact LAYOUTS|apply Forall_forall; auto| |];
      [apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); assumption|
       replace (i*rectangle_stride base) with (i*rectangle_stride base+0) by lia;
       apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); auto; lia]))).
  exact ITER.
Qed.
End SOURCE.
Print Assumptions named_array_operations_source_clight_decode.
