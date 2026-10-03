From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts AbstractSchedule CompCertMemoryEquivalence
  CompCertStoreSchedule CompCertMemoryActions RectangularSchedule RectangularMemorySchedule RectangularIteration ClightGuard ClightCondition ClightNoWrap
  ClightRedundantSet ClightRegionRule ClightRegionRewrite ClightTempFrame ClightStraightLine
  ClightCountedLoop ClightCountedProtocol ClightZeroTrip ClightFramedLoop ClightFrontendLoopProtocol
  ClightFrontendRegion ClightLoopExecution ClightLoopSyntax ClightRegionProgress
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion ClightRectangularUpdate.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma rect_update_body_normal d array row column body :
  flatten_region body = [rect_update d array row column] -> normal_statement body = true.
Proof. intro FLAT; apply flatten_normal_certificate; rewrite FLAT; repeat constructor. Qed.
Lemma rect_update_body_quiet d array row column body :
  flatten_region body = [rect_update d array row column] -> quiet_statement body = true.
Proof. intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; repeat constructor. Qed.
Lemma rect_update_body_writes d array row column body :
  flatten_region body = [rect_update d array row column] -> writes_only [] body.
Proof. intro FLAT; apply flatten_writes_certificate; rewrite FLAT; repeat constructor. Qed.

Lemma rectangle_update_source_guard_domain d fe ge locals le memory array row bound column inner_bound body outer_body le' final :
  row <> bound -> row <> column -> bound <> column -> column <> inner_bound ->
  flatten_region body = [rect_update d array row column] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body] ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  rectangle_guard_domain row bound inner_bound (Entry ge locals le memory).
Proof.
  intros RN RC NC CM BODY OUTER RUN.
  destruct (@frontend_entry_test fe ge locals le memory row bound outer_body le' final RUN) as [flag TEST].
  destruct (@counter_test_domain row bound (Entry ge locals le memory) flag TEST)
    as [x [upper [X UP]]].
  cbn [entry_temps] in X, UP.
  split; [exists x; exact X|split; [exists upper; exact UP|]].
  intros ZERO POS; change (le ! row = Some (Vint Int.zero)) in ZERO.
  cbn [entry_temps] in POS; unfold temp_word in POS; rewrite UP in POS.
  assert (UP' : le ! bound = Some (Vint (Int.repr (Int.signed upper)))).
  { rewrite Int.repr_signed; exact UP. }
  assert (TEST0 : expression_test (counter_condition row bound) (Entry ge locals le memory) true).
  { replace true with (0 <? Int.signed upper) by (apply Z.ltb_lt; exact POS).
    apply (@counter_condition_at ge locals le memory row bound 0 (Int.signed upper)); auto.
    - change (-2147483648 <= 0 <= 2147483647); lia.
    - apply Int.signed_range. }
  assert (WRITES := @rectangle_outer_writes column inner_bound body outer_body
    (@rect_update_body_writes d array row column body BODY) OUTER).
  assert (FRAME : forall before mem tr after mem',
    exec_stmt fe ge locals before mem outer_body tr after mem' Out_normal -> temp_agree [row;bound] before after).
  { intros; eapply structured_temp_frame; [exact WRITES|cbn; intros id LIVE WRITE; intuition congruence|eassumption]. }
  destruct (@frontend_iteration_decode fe ge locals le memory row bound outer_body le' final TEST0
    (@normal_statement_execution fe ge locals outer_body
      (@rectangle_outer_normal column inner_bound body outer_body (@rect_update_body_quiet d array row column body BODY) OUTER)) FRAME RUN)
    as [body_temps [body_memory [BODY_RUN REST]]].
  apply (@flattened_pair_execution fe ge locals outer_body (rectangle_reset column)
    (frontend_counted_loop column inner_bound body) le memory body_temps body_memory OUTER) in BODY_RUN.
  destruct (sequence_normal_decode BODY_RUN) as [reset_temps [reset_memory [RESET INNER]]].
  destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset_temps reset_memory.
  destruct (@frontend_entry_test fe ge locals _ memory column inner_bound body body_temps body_memory INNER)
    as [inner_flag INNER_TEST].
  destruct (@counter_test_domain column inner_bound _ inner_flag INNER_TEST) as [j [m [J M]]].
  exists m; cbn in M |- *; rewrite PTree.gso in M by congruence; exact M.
Qed.

Definition rect_update_point d ge locals array i j before after :=
  exists block, rect_array_binding d ge locals array block /\
    memory_action_run (rect_update_action d block i j) before after.

Section RULE.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable array row bound column inner_bound : ident.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RM : row <> inner_bound.
Hypothesis CM : column <> inner_bound.
Hypothesis BODY : flatten_region body = [rect_update d array row column].
Hypothesis OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body].

Theorem rectangle_update_local fe ge locals le memory le' final N M :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr N)) ->
  le ! inner_bound = Some (Vint (Int.repr M)) -> signed_range N -> signed_range M ->
  0 < N <= rectangle_outer_limit d -> 0 < M <= rectangle_stride d ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  exec_stmt fe ge locals le memory (rectangle_interchanged row bound column inner_bound (rect_update d array row column))
    E0 le' final Out_normal.
Proof.
  intros ZERO NLOOK MLOOK NS MS NB MB RUN.
  set (rows := Z.to_nat N); set (columns := Z.to_nat M).
  assert (RZ : Z.of_nat rows = N) by (unfold rows; apply Z2Nat.id; lia).
  assert (CZ : Z.of_nat columns = M) by (unfold columns; apply Z2Nat.id; lia).
  assert (RP : rows <> O) by (intro EQ; rewrite EQ in RZ; cbn in RZ; lia).
  assert (CP : columns <> O) by (intro EQ; rewrite EQ in CZ; cbn in CZ; lia).
  assert (DECODE : forall i j temps before after mem',
    0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
    temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
    exec_stmt fe ge locals temps before body E0 after mem' Out_normal ->
    rect_update_point d ge locals array i j before mem' /\ after = temps).
  { intros i j temps before after mem' I J RI CJ EXEC.
    apply (@flattened_singleton_execution fe ge locals body (rect_update d array row column)
      temps before after mem' BODY) in EXEC.
    destruct (@rect_update_inverse d VALID fe ge locals temps before array row column i j E0 after mem' Out_normal
      RI CJ ltac:(apply rectangle_point_bound with (N := N) (M := M); auto; lia) EXEC)
      as [block [ARRAY [_ [EXIT [_ STORE]]]]].
    split; [exists block; split; [exact ARRAY|exact STORE]|exact EXIT]. }
  destruct (@rectangle_source_decode fe ge locals row bound column inner_bound body outer_body
    (rect_update_point d ge locals array) rows columns RN RC NC RM CM RP
    ltac:(rewrite RZ; exact NS) ltac:(rewrite CZ; exact MS)
    (@rect_update_body_normal d array row column body BODY) (@rect_update_body_quiet d array row column body BODY)
    (@rect_update_body_writes d array row column body BODY) OUTER DECODE le memory le' final ZERO
    ltac:(rewrite RZ; exact NLOOK) ltac:(rewrite CZ; exact MLOOK) RUN) as [ITER EXIT].
  destruct (@rectangular_first mem (rect_update_point d ge locals array) rows columns memory final RP CP ITER)
    as [first [block [ARRAY FIRST]]].
  assert (FIXED : rectangular_iterations (fun i j =>
    instruction_run (rectangle_memory_scheduling block (rectangle_stride d) (rect_update_compute d)) (i,j)) rows columns memory final).
  { eapply rectangular_iterations_map; [|exact ITER].
    intros i j before after [b [BINDING STORE]].
    assert (EQ : b = block) by (eapply rect_array_binding_unique; eauto); subst b; exact STORE. }
  apply rectangular_schedule in FIXED.
  apply rectangle_memory_interchange_preserves_memory in FIXED; [|rewrite CZ; lia].
  assert (SWAPPED : rectangular_iterations (fun j i =>
    instruction_run (rectangle_memory_scheduling block (rectangle_stride d) (rect_update_compute d)) (i,j)) columns rows memory final).
  { apply rectangular_schedule; exact FIXED. }
  assert (ENCODE : forall j i temps before after, 0 <= j < Z.of_nat columns -> 0 <= i < Z.of_nat rows ->
    temps ! column = Some (Vint (Int.repr j)) -> temps ! row = Some (Vint (Int.repr i)) ->
    instruction_run (rectangle_memory_scheduling block (rectangle_stride d) (rect_update_compute d)) (i,j) before after ->
    exec_stmt fe ge locals temps before (rect_update d array row column) E0 temps after Out_normal).
  { intros j i temps before after J I CJ RI STORE; apply (@rect_update_evaluation d VALID
      fe ge locals temps before array row column block i j after ARRAY RI CJ); auto.
    apply rectangle_point_bound with (N := N) (M := M); auto; lia. }
  assert (TARGET := @rectangle_target_encode fe ge locals column inner_bound row bound
    (rect_update d array row column)
    (fun j i => instruction_run (rectangle_memory_scheduling block (rectangle_stride d) (rect_update_compute d)) (i,j))
    columns rows CM ltac:(congruence) ltac:(congruence) ltac:(congruence) RN CP
    ltac:(rewrite CZ; exact MS) ltac:(rewrite RZ; exact NS) ENCODE
    (PTree.set column (Vint Int.zero) le) memory final (PTree.gss _ _ _)
    ltac:(rewrite PTree.gso by congruence; rewrite CZ; exact MLOOK)
    ltac:(rewrite PTree.gso by congruence; rewrite RZ; exact NLOOK) SWAPPED).
  rewrite rectangle_temps_commute in TARGET by congruence; rewrite PTree.set2 in TARGET.
  rewrite EXIT; unfold rectangle_interchanged.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [unfold rectangle_reset; constructor; constructor|exact TARGET].
Qed.

Definition rectangle_update_region_rule : encoded_region_rule (frontend_counted_loop row bound outer_body)
  (rectangle_interchanged row bound column inner_bound (rect_update d array row column)).
Proof.
  refine {| region_rule_atoms := unit; region_rule_domain := rectangle_guard_domain row bound inner_bound;
    region_rule_dimension := rectangle_guard_dimension row bound inner_bound VALID;
    region_rule_primitives := rectangle_guard_primitives row bound inner_bound VALID;
    region_rule_formula := Fact tt |}.
  - intros temps p locals le memory le' final RUN.
    exact (@rectangle_update_source_guard_domain d (adapter_entry temps) (globalenv p) locals le memory
      array row bound column inner_bound body outer_body le' final RN RC NC CM BODY OUTER RUN).
  - intros temps p locals le memory le' final RUN [ZERO [[ND NR] [MD MR]]].
    destruct ND as [n NLOOK]; destruct MD as [m MLOOK].
    cbn [entry_temps] in NLOOK, MLOOK.
    cbn [entry_temps] in NR, MR; unfold temp_word in NR, MR; rewrite NLOOK in NR; rewrite MLOOK in MR.
    change (le ! row = Some (Vint Int.zero)) in ZERO.
    exists final; split; [|apply memory_equivalent_refl].
    eapply rectangle_update_local with (N := Int.signed n) (M := Int.signed m); auto using Int.signed_range.
    all: try (rewrite Int.repr_signed; assumption).
    all: apply Int.signed_range.
Defined.
End RULE.

Print Assumptions rectangle_update_local.
Print Assumptions rectangle_update_region_rule.
