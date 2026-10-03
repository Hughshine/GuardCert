From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import AbstractGuard SemanticFacts CompCertMemoryEquivalence
  ClightGuard ClightCondition ClightNoWrap ClightRedundantSet ClightRegionRule ClightRegionRewrite
  ClightCountedLoop ClightLoopSyntax ClightTempFrame ClightStraightLine
  ClightRectangularStore ClightRectangularUpdate ClightRectangularRowUpdate
  ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion
  ClightRectangularUpdateRegion ClightRectangularRowRegion
  RectangularIteration RectangularSchedule CompCertStoreSchedule CompCertMemoryActions
  ClightRegionProgress ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryPolyhedral GuardMemoryLoops GuardMemoryClightRectangles GuardMemoryPolyhedralRectangles.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition checked_rectangle_dependences mode d :=
  validate_memory_equivalence
    (rectangle_poly_program (mode_instruction mode d 3%positive) (rectangle_stride d) rectangle_row_schedule)
    (rectangle_poly_program (mode_instruction mode d 3%positive) (rectangle_stride d) rectangle_column_schedule).

Lemma mode_clight_inverse_any mode d (VALID : rectangle_layout_valid d) fe ge locals array row column
  i j le memory after final :
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  0 <= i * rectangle_stride d < rectangle_extent d ->
  le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
  exec_stmt fe ge locals le memory (mode_statement mode d array row column) E0 after final Out_normal ->
  (exists block, rect_array_binding d ge locals array block /\ mode_physical mode d block i j memory final) /\ after = le.
Proof.
  intros WRITE READ ROW COLUMN EXEC; destruct mode; cbn [mode_statement mode_physical] in *.
  - destruct (@rect_store_inverse d VALID fe ge locals le memory array row column i j E0 after final Out_normal
      ROW COLUMN WRITE EXEC) as [block [BINDING [_ [TEMPS [_ STORE]]]]]; split; [exists block; auto|exact TEMPS].
  - destruct (@rect_update_inverse d VALID fe ge locals le memory array row column i j E0 after final Out_normal
      ROW COLUMN WRITE EXEC) as [block [BINDING [_ [TEMPS [_ STORE]]]]]; split; [exists block; auto|exact TEMPS].
  - destruct (@rect_row_update_inverse d VALID fe ge locals le memory array row column i j E0 after final Out_normal
      ROW COLUMN WRITE READ EXEC) as [block [BINDING [_ [TEMPS [_ STORE]]]]]; split; [exists block; auto|exact TEMPS].
Qed.

Section LOCAL.
Variable mode : rectangle_memory_mode.
Variable d : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid d.
Variable array row bound column inner_bound : ident.
Variable body outer_body : statement.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RM : row <> inner_bound.
Hypothesis CM : column <> inner_bound.
Hypothesis BODY : flatten_region body = [mode_statement mode d array row column].
Hypothesis OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column inner_bound body].

Lemma memory_mode_source_guard_domain fe ge locals le memory le' final :
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  rectangle_guard_domain row bound inner_bound (Entry ge locals le memory).
Proof.
  intro RUN; destruct mode.
  - exact (@rectangle_source_guard_domain d fe ge locals le memory array row bound column inner_bound body outer_body
      le' final RN RC NC CM BODY OUTER RUN).
  - exact (@rectangle_update_source_guard_domain d fe ge locals le memory array row bound column inner_bound body outer_body
      le' final RN RC NC CM BODY OUTER RUN).
  - exact (@rectangle_row_update_source_guard_domain d fe ge locals le memory array row bound column inner_bound body outer_body
      le' final RN RC NC CM BODY OUTER RUN).
Qed.

Lemma memory_mode_source_binding fe ge locals le memory le' final rows columns :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  signed_range (Z.of_nat rows) -> signed_range (Z.of_nat columns) ->
  0 < Z.of_nat rows <= rectangle_outer_limit d -> 0 < Z.of_nat columns <= rectangle_stride d ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  exists block, rect_array_binding d ge locals array block.
Proof.
  intros ZERO BOUND INNER NS MS NB MB SOURCE.
  assert (POS : rows <> O) by (intro EQ; rewrite EQ in NB; cbn in NB; lia).
  assert (POS' : columns <> O) by (intro EQ; rewrite EQ in MB; cbn in MB; lia).
  set (point := fun i j before after => exists block,
    rect_array_binding d ge locals array block /\ mode_physical mode d block i j before after).
  destruct (@rectangle_source_decode fe ge locals row bound column inner_bound body outer_body
    point rows columns RN RC NC RM CM POS NS MS
    (@mode_normal_body mode d array row column body BODY)
    (@mode_quiet_body mode d array row column body BODY)
    (@mode_writes_body mode d array row column body BODY) OUTER
    ltac:(intros i j temps before after' final' I J ROW COLUMN RUN;
      apply (@flattened_singleton_execution fe ge locals body (mode_statement mode d array row column)
        temps before after' final' BODY) in RUN;
      exact (@mode_clight_inverse_any mode d VALID fe ge locals array row column i j temps before after' final'
        ltac:(apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); assumption)
        ltac:(replace (i * rectangle_stride d) with (i * rectangle_stride d + 0) by lia;
          apply rectangle_point_bound with (N := Z.of_nat rows) (M := Z.of_nat columns); assumption || lia)
        ROW COLUMN RUN)) le memory le' final ZERO BOUND INNER SOURCE) as [ITER EXIT].
  destruct (@rectangular_first mem point rows columns memory final POS POS' ITER)
    as [first [block [BINDING RUN]]]; exists block; exact BINDING.
Qed.

Theorem memory_validated_rectangle_local
  (DEPENDENCES : mayReturn (checked_rectangle_dependences mode d) true)
  fe ge locals le memory le' final N M :
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr N)) ->
  le ! inner_bound = Some (Vint (Int.repr M)) -> signed_range N -> signed_range M ->
  0 < N <= rectangle_outer_limit d -> 0 < M <= rectangle_stride d ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  exec_stmt fe ge locals le memory
    (rectangle_interchanged row bound column inner_bound (mode_statement mode d array row column))
    E0 le' final Out_normal.
Proof.
  intros ZERO NLOOK MLOOK NS MS NB MB SOURCE.
  set (rows := Z.to_nat N); set (columns := Z.to_nat M).
  assert (RZ : Z.of_nat rows = N) by (unfold rows; apply Z2Nat.id; lia).
  assert (CZ : Z.of_nat columns = M) by (unfold columns; apply Z2Nat.id; lia).
  assert (POS : columns <> O) by (intro EQ; rewrite EQ in CZ; cbn in CZ; lia).
  destruct (@memory_mode_source_binding fe ge locals le memory le' final rows columns ZERO
    ltac:(rewrite RZ; exact NLOOK) ltac:(rewrite CZ; exact MLOOK)
    ltac:(rewrite RZ; exact NS) ltac:(rewrite CZ; exact MS)
    ltac:(rewrite RZ; exact NB) ltac:(rewrite CZ; exact MB) SOURCE) as [block ARRAY].
  destruct (@memory_rectangle_source_clight_decode mode d VALID fe ge locals array row bound column inner_bound block
    ARRAY RN RC NC RM CM rows columns ltac:(rewrite RZ; exact NB) ltac:(rewrite CZ; exact MB)
    ltac:(rewrite RZ; exact NS) ltac:(rewrite CZ; exact MS) 3%positive body outer_body le memory le' final
    BODY OUTER ZERO ltac:(rewrite RZ; exact NLOOK) ltac:(rewrite CZ; exact MLOOK) SOURCE) as [LOOP EXIT].
  assert (NONALIAS : GuardMemoryInstr.NonAlias
    (RuntimeState (flat_array_locations 3%positive block (rectangle_extent d)) memory)).
  { apply flat_array_locations_nonalias. }
  pose proof (@validated_memory_rectangle_interchange (mode_instruction mode d 3%positive)
    (rectangle_stride d) rows columns _ _ ltac:(rewrite CZ; lia) NONALIAS DEPENDENCES LOOP) as LOGICAL.
  apply (proj2 (@memory_rectangle_columns_lift
    (flat_array_locations 3%positive block (rectangle_extent d)) (mode_instruction mode d 3%positive)
    (mode_physical mode d block) rows columns memory final
    ltac:(intros i j first last I J; apply mode_instruction_execution;
      [apply rectangle_point_bound with (N := N) (M := M); auto; lia|
       replace (i * rectangle_stride d) with (i * rectangle_stride d + 0) by lia;
       apply rectangle_point_bound with (N := N) (M := M); auto; lia]))) in LOGICAL.
  assert (TARGET := @rectangle_target_encode fe ge locals column inner_bound row bound
    (mode_statement mode d array row column) (fun j i => mode_physical mode d block i j) columns rows
    CM ltac:(congruence) ltac:(congruence) ltac:(congruence) RN POS
    ltac:(rewrite CZ; exact MS) ltac:(rewrite RZ; exact NS)
    ltac:(intros j i temps before after J I COLUMN ROW RUN;
      exact (@mode_clight_evaluation mode d VALID fe ge locals array row bound column inner_bound block ARRAY
        RN RC NC RM CM rows columns ltac:(rewrite RZ; exact NB) ltac:(rewrite CZ; exact MB)
        i j temps before after I J ROW COLUMN RUN))
    (PTree.set column (Vint Int.zero) le) memory final (PTree.gss _ _ _)
    ltac:(rewrite PTree.gso by congruence; rewrite CZ; exact MLOOK)
    ltac:(rewrite PTree.gso by congruence; rewrite RZ; exact NLOOK) LOGICAL).
  rewrite rectangle_temps_commute in TARGET by congruence; rewrite PTree.set2 in TARGET.
  rewrite EXIT; unfold rectangle_interchanged.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [unfold rectangle_reset; constructor; constructor|exact TARGET].
Qed.

Definition memory_validated_rectangle_rule
  (DEPENDENCES : mayReturn (checked_rectangle_dependences mode d) true) :
  encoded_region_rule (frontend_counted_loop row bound outer_body)
    (rectangle_interchanged row bound column inner_bound (mode_statement mode d array row column)).
Proof.
  refine {| region_rule_atoms := unit; region_rule_domain := rectangle_guard_domain row bound inner_bound;
    region_rule_dimension := rectangle_guard_dimension row bound inner_bound VALID;
    region_rule_primitives := rectangle_guard_primitives row bound inner_bound VALID;
    region_rule_formula := Fact tt |}.
  - intros; eapply memory_mode_source_guard_domain; eauto.
  - intros temps p locals le memory le' final RUN [ZERO [[ND NR] [MD MR]]].
    destruct ND as [n NLOOK]; destruct MD as [m MLOOK].
    cbn [entry_temps] in NLOOK, MLOOK, NR, MR; unfold temp_word in NR, MR;
      rewrite NLOOK in NR; rewrite MLOOK in MR.
    change (le ! row = Some (Vint Int.zero)) in ZERO.
    exists final; split; [|apply memory_equivalent_refl].
    eapply memory_validated_rectangle_local with (N := Int.signed n) (M := Int.signed m);
      auto using Int.signed_range.
    all: try (rewrite Int.repr_signed; assumption).
    all: apply Int.signed_range.
Defined.
End LOCAL.
Print Assumptions memory_validated_rectangle_local.
Print Assumptions memory_validated_rectangle_rule.
