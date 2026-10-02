From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts AbstractSchedule CompCertMemoryEquivalence
  CompCertStoreSchedule ClightGuard ClightCondition ClightRedundantSet ClightRegionRule ClightRegionRewrite
  ClightTempFrame ClightStraightLine ClightCountedLoop ClightCountedProtocol ClightZeroTrip
  ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightLoopSyntax
  ClightMatrixStore ClightMatrixGuard ClightMatrixLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma matrix_source_guard_domain fe ge locals le memory array row bound column inner_bound body outer_body le' final :
  row <> column -> bound <> column -> column <> inner_bound ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column inner_bound body] ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  matrix_guard_domain row bound inner_bound (Entry ge locals le memory).
Proof.
  intros RC NC CM BODY OUTER RUN.
  destruct (@frontend_entry_test fe ge locals le memory row bound outer_body le' final RUN) as [flag TEST].
  destruct (@counter_test_domain row bound (Entry ge locals le memory) flag TEST)
    as [x [upper [X UP]]].
  split; [exists x; exact X|split; [exists upper; exact UP|]].
  intros ZERO TWO; change (le ! row = Some (Vint (Int.repr 0))) in ZERO.
  change (le ! bound = Some (Vint (Int.repr 2))) in TWO.
  assert (TEST0 := @counter_test_small ge locals le memory row bound 0 ltac:(lia) ZERO TWO).
  assert (WRITES := @matrix_outer_body_writes array row column inner_bound body outer_body BODY OUTER).
  assert (FRAME : forall before mem tr after mem',
    exec_stmt fe ge locals before mem outer_body tr after mem' Out_normal -> temp_agree [row;bound] before after).
  { intros; eapply structured_temp_frame; [exact WRITES|cbn; intros id LIVE WRITE; intuition congruence|eassumption]. }
  destruct (@frontend_iteration_decode fe ge locals le memory row bound outer_body le' final TEST0
    (@normal_statement_execution fe ge locals outer_body
      (@matrix_outer_body_normal array row column inner_bound body outer_body BODY OUTER)) FRAME RUN)
    as [body_temps [body_memory [BODY_RUN REST]]].
  apply (@flattened_pair_execution fe ge locals outer_body (matrix_reset column)
    (frontend_counted_loop column inner_bound body) le memory body_temps body_memory OUTER) in BODY_RUN.
  destruct (sequence_normal_decode BODY_RUN) as [reset_temps [reset_memory [RESET INNER]]].
  destruct (@matrix_reset_decode fe ge locals le memory column E0 reset_temps reset_memory Out_normal RESET)
    as [_ [TEMPS [MEMORY _]]]; subst reset_temps reset_memory.
  destruct (@frontend_entry_test fe ge locals _ memory column inner_bound body body_temps body_memory INNER)
    as [inner_flag INNER_TEST].
  destruct (@counter_test_domain column inner_bound _ inner_flag INNER_TEST) as [j [m [J M]]].
  exists m; cbn in M |- *; rewrite PTree.gso in M by congruence; exact M.
Qed.

Definition matrix_region_rule array row bound column inner_bound body outer_body
  (RN : row <> bound) (RC : row <> column) (NC : bound <> column)
  (RM : row <> inner_bound) (CM : column <> inner_bound)
  (BODY : flatten_region body = [matrix_store array row column])
  (OUTER : flatten_region outer_body = [matrix_reset column; frontend_counted_loop column inner_bound body]) :
  encoded_region_rule (frontend_counted_loop row bound outer_body)
    (matrix_interchanged row bound column inner_bound array).
Proof.
  refine {| region_rule_atoms := unit; region_rule_domain := matrix_guard_domain row bound inner_bound;
    region_rule_dimension := matrix_guard_dimension row bound inner_bound;
    region_rule_primitives := matrix_guard_primitives row bound inner_bound;
    region_rule_formula := Fact tt |}.
  - intros temps p locals le memory le' final RUN.
    exact (@matrix_source_guard_domain (adapter_entry temps) (globalenv p) locals le memory
      array row bound column inner_bound body outer_body le' final RC NC CM BODY OUTER RUN).
  - intros temps p locals le memory le' final RUN [ZERO [TWO INNER_TWO]].
    change (le ! row = Some (Vint (Int.repr 0))) in ZERO.
    change (le ! bound = Some (Vint (Int.repr 2))) in TWO.
    change (le ! inner_bound = Some (Vint (Int.repr 2))) in INNER_TWO.
    destruct (@matrix_source_decode (adapter_entry temps) (globalenv p) locals le memory
      array row bound column inner_bound body outer_body le' final RN RC NC RM CM BODY OUTER
      ZERO TWO INNER_TWO RUN) as [block [ARRAY [SCHEDULE EXIT]]].
    apply matrix_interchange_preserves_actual_memory in SCHEDULE.
    exists final; split; [rewrite EXIT; eapply matrix_target_encode; eauto|apply memory_equivalent_refl].
Defined.

Print Assumptions matrix_source_guard_domain.
Print Assumptions matrix_region_rule.
