From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightLoopSyntax ClightTempFrame
  ClightStraightLine ClightRectangularStore ClightRectangularUpdate ClightRectangularRowUpdate
  ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion
  RectangularIteration RectangularSchedule CompCertStoreSchedule CompCertMemoryActions
  ClightRegionProgress ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryPolyhedral GuardMemoryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Inductive rectangle_memory_mode := WriteOnly | OwnCellUpdate | RowPrefixUpdate.
Definition mode_instruction mode d array := match mode with
  | WriteOnly => rect_memory_write d array
  | OwnCellUpdate => rect_memory_update d array
  | RowPrefixUpdate => rect_memory_row_update d array end.
Definition mode_statement mode d array row column := match mode with
  | WriteOnly => rect_store d array row column
  | OwnCellUpdate => rect_update d array row column
  | RowPrefixUpdate => rect_row_update d array row column end.
Definition mode_physical mode d block i j := match mode with
  | WriteOnly => store_action_run (rectangle_action block (rectangle_stride d) (rect_payload d) (i,j))
  | OwnCellUpdate => memory_action_run (rect_update_action d block i j)
  | RowPrefixUpdate => memory_action_run (rect_row_update_action d block i j) end.

Lemma mode_normal mode d array row column : normal_statement (mode_statement mode d array row column) = true.
Proof. destruct mode; reflexivity. Qed.
Lemma mode_quiet mode d array row column : quiet_statement (mode_statement mode d array row column) = true.
Proof. destruct mode; reflexivity. Qed.
Lemma mode_writes mode d array row column : writes_only [] (mode_statement mode d array row column).
Proof. destruct mode; constructor. Qed.
Lemma mode_normal_body mode d array row column body :
  flatten_region body = [mode_statement mode d array row column] -> normal_statement body = true.
Proof. intro FLAT; apply flatten_normal_certificate; rewrite FLAT; constructor; [apply mode_normal|constructor]. Qed.
Lemma mode_quiet_body mode d array row column body :
  flatten_region body = [mode_statement mode d array row column] -> quiet_statement body = true.
Proof. intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; constructor; [apply mode_quiet|constructor]. Qed.
Lemma mode_writes_body mode d array row column body :
  flatten_region body = [mode_statement mode d array row column] -> writes_only [] body.
Proof. intro FLAT; apply flatten_writes_certificate; rewrite FLAT; constructor; [apply mode_writes|constructor]. Qed.

Lemma mode_instruction_execution mode d array block i j before after :
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  0 <= i * rectangle_stride d < rectangle_extent d ->
  (mode_physical mode d block i j before after <->
   memory_point (mode_instruction mode d array) i j
     (RuntimeState (flat_array_locations array block (rectangle_extent d)) before)
     (RuntimeState (flat_array_locations array block (rectangle_extent d)) after)).
Proof.
  intros WRITE READ; destruct mode; cbn [mode_physical mode_instruction]; symmetry.
  - exact (@rect_memory_write_execution d array block i j before after WRITE).
  - exact (@rect_memory_update_execution d array block i j before after WRITE).
  - exact (@rect_memory_row_update_execution d array block i j before after WRITE READ).
Qed.

Section BRIDGE.
Variable mode : rectangle_memory_mode.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable array row bound column inner_bound : ident.
Variable block : Values.block.
Hypothesis ARRAY : rect_array_binding d ge locals array block.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RM : row <> inner_bound.
Hypothesis CM : column <> inner_bound.
Variable rows columns : nat.
Hypothesis NB : 0 < Z.of_nat rows <= rectangle_outer_limit d.
Hypothesis MB : 0 < Z.of_nat columns <= rectangle_stride d.
Hypothesis NS : signed_range (Z.of_nat rows).
Hypothesis MS : signed_range (Z.of_nat columns).

Lemma mode_point_bound i j : 0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
  0 <= i * rectangle_stride d + j < rectangle_extent d.
Proof. intros I J; apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); assumption. Qed.
Lemma mode_read_bound i : 0 <= i < Z.of_nat rows -> 0 <= i * rectangle_stride d < rectangle_extent d.
Proof.
  intro I; replace (i * rectangle_stride d) with (i * rectangle_stride d + 0) by lia.
  apply mode_point_bound; [exact I|lia].
Qed.

Lemma mode_clight_inverse i j le memory after final :
  0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
  le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
  exec_stmt fe ge locals le memory (mode_statement mode d array row column) E0 after final Out_normal ->
  mode_physical mode d block i j memory final /\ after = le.
Proof.
  intros I J ROW COLUMN EXEC; destruct mode; cbn [mode_statement mode_physical] in *.
  - destruct (@rect_store_inverse d VALID fe ge locals le memory array row column i j E0 after final Out_normal
      ROW COLUMN (mode_point_bound I J) EXEC) as [b [BIND [_ [TEMPS [_ STORE]]]]].
    assert (SAME : b = block) by (eapply rect_array_binding_unique; eauto); subst b; auto.
  - destruct (@rect_update_inverse d VALID fe ge locals le memory array row column i j E0 after final Out_normal
      ROW COLUMN (mode_point_bound I J) EXEC) as [b [BIND [_ [TEMPS [_ STORE]]]]].
    assert (SAME : b = block) by (eapply rect_array_binding_unique; eauto); subst b; auto.
  - destruct (@rect_row_update_inverse d VALID fe ge locals le memory array row column i j E0 after final Out_normal
      ROW COLUMN (mode_point_bound I J) (mode_read_bound I) EXEC) as [b [BIND [_ [TEMPS [_ STORE]]]]].
    assert (SAME : b = block) by (eapply rect_array_binding_unique; eauto); subst b; auto.
Qed.
Lemma mode_clight_evaluation i j le memory final :
  0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
  le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
  mode_physical mode d block i j memory final ->
  exec_stmt fe ge locals le memory (mode_statement mode d array row column) E0 le final Out_normal.
Proof.
  intros I J ROW COLUMN EXEC; destruct mode; cbn [mode_statement mode_physical] in *.
  - apply (@rect_store_evaluation d VALID fe ge locals le memory array row column block i j final ARRAY ROW COLUMN
      (mode_point_bound I J) EXEC).
  - apply (@rect_update_evaluation d VALID fe ge locals le memory array row column block i j final ARRAY ROW COLUMN
      (mode_point_bound I J) EXEC).
  - apply (@rect_row_update_evaluation d VALID fe ge locals le memory array row column block i j final ARRAY ROW COLUMN
      (mode_point_bound I J) (mode_read_bound I) EXEC).
Qed.

Variable logical_array : ident.

Theorem memory_rectangle_source_clight_decode body outer_body le memory after final :
  flatten_region body = [mode_statement mode d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body] ->
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  GuardMemoryIRs.Loop.loop_semantics (memory_rectangle_loop (mode_instruction mode d logical_array))
    [Z.of_nat rows;Z.of_nat columns]
    (RuntimeState (flat_array_locations logical_array block (rectangle_extent d)) memory)
    (RuntimeState (flat_array_locations logical_array block (rectangle_extent d)) final) /\
  after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
    (PTree.set column (Vint (Int.repr (Z.of_nat columns))) le).
Proof.
  intros BODY OUTER ZERO BOUND INNER EXEC.
  assert (POS : rows <> O) by (intro EQ; rewrite EQ in NB; cbn in NB; lia).
  destruct (@rectangle_source_decode fe ge locals row bound column inner_bound body outer_body
    (mode_physical mode d block) rows columns RN RC NC RM CM POS NS MS
    (@mode_normal_body mode d array row column body BODY) (@mode_quiet_body mode d array row column body BODY) (@mode_writes_body mode d array row column body BODY) OUTER
    ltac:(intros i j temps before after' final' I J ROW COLUMN RUN;
      apply (@flattened_singleton_execution fe ge locals body (mode_statement mode d array row column)
        temps before after' final' BODY) in RUN;
      eapply mode_clight_inverse; eauto)
    le memory after final ZERO BOUND INNER EXEC) as [ITER EXIT].
  split; [|exact EXIT].
  apply (proj1 (@memory_rectangle_lift (flat_array_locations logical_array block (rectangle_extent d))
    (mode_instruction mode d logical_array) (mode_physical mode d block) rows columns memory final
    ltac:(intros; apply mode_instruction_execution; [apply mode_point_bound|apply mode_read_bound]; assumption))).
  exact ITER.
Qed.

Theorem memory_rectangle_candidate_clight_encode le memory final :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  GuardMemoryIRs.Loop.loop_semantics (memory_rectangle_loop (mode_instruction mode d logical_array))
    [Z.of_nat rows;Z.of_nat columns]
    (RuntimeState (flat_array_locations logical_array block (rectangle_extent d)) memory)
    (RuntimeState (flat_array_locations logical_array block (rectangle_extent d)) final) ->
  exec_stmt fe ge locals le memory
    (frontend_counted_loop row bound (rectangle_outer_body column inner_bound (mode_statement mode d array row column))) E0
    (PTree.set row (Vint (Int.repr (Z.of_nat rows)))
      (PTree.set column (Vint (Int.repr (Z.of_nat columns))) le)) final Out_normal.
Proof.
  intros ZERO BOUND INNER EXEC.
  apply (proj2 (@memory_rectangle_lift (flat_array_locations logical_array block (rectangle_extent d))
    (mode_instruction mode d logical_array) (mode_physical mode d block) rows columns memory final
    ltac:(intros; apply mode_instruction_execution; [apply mode_point_bound|apply mode_read_bound]; assumption))) in EXEC.
  assert (POS : rows <> O) by (intro EQ; rewrite EQ in NB; cbn in NB; lia).
  apply (@rectangle_target_encode fe ge locals row bound column inner_bound
    (mode_statement mode d array row column) (mode_physical mode d block) rows columns
    RN RC NC RM CM POS NS MS
    ltac:(intros; eapply mode_clight_evaluation; eauto) le memory final ZERO BOUND INNER EXEC).
Qed.
End BRIDGE.

Print Assumptions memory_rectangle_source_clight_decode.
Print Assumptions memory_rectangle_candidate_clight_encode.
