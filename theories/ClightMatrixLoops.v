From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractSchedule CompCertStoreSchedule ClightCondition ClightNoWrap
  ClightTempFrame ClightStraightLine ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol
  ClightLoopExecution ClightLoopSyntax ClightMatrixStore.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition matrix_reset id := Sset id (matrix_constant 0).
Definition matrix_point block i j := matrix_cell block (i * 2 + j) (i * 10 + j + 1).
Definition matrix_row_body column inner_bound body :=
  Ssequence (matrix_reset column) (frontend_counted_loop column inner_bound body).
Definition matrix_column_body row bound array column :=
  Ssequence (matrix_reset row) (frontend_counted_loop row bound (matrix_store array row column)).
Definition matrix_interchanged row bound column inner_bound array :=
  Ssequence (matrix_reset column)
    (frontend_counted_loop column inner_bound (matrix_column_body row bound array column)).

Lemma matrix_temps_commute first second x y (temps : temp_env) : first <> second ->
  PTree.set first x (PTree.set second y temps) = PTree.set second y (PTree.set first x temps).
Proof.
  intro DISTINCT; apply PTree.extensionality; intro key; rewrite !PTree.gsspec.
  destruct (peq key first), (peq key second); subst; try congruence; reflexivity.
Qed.

Lemma matrix_body_normal array row column body :
  flatten_region body = [matrix_store array row column] -> normal_statement body = true.
Proof.
  intro FLAT; apply flatten_normal_certificate; rewrite FLAT; constructor; [reflexivity|constructor].
Qed.
Lemma matrix_body_writes array row column body :
  flatten_region body = [matrix_store array row column] -> writes_only [] body.
Proof.
  intro FLAT; apply flatten_writes_certificate; rewrite FLAT; constructor; [constructor|constructor].
Qed.

Lemma matrix_row_loop_decode fe ge locals le memory array row column inner_bound body i le' final :
  row <> column -> column <> inner_bound ->
  flatten_region body = [matrix_store array row column] ->
  le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr 0)) ->
  le ! inner_bound = Some (Vint (Int.repr 2)) -> 0 <= i <= 1 ->
  exec_stmt fe ge locals le memory (frontend_counted_loop column inner_bound body) E0 le' final Out_normal ->
  exists block middle, matrix_array_binding ge locals array block /\
    store_action_run (matrix_point block i 0) memory middle /\
    store_action_run (matrix_point block i 1) middle final /\
    le' = PTree.set column (Vint (Int.repr 2)) le.
Proof.
  intros RC CM FLAT ROW ZERO TWO RANGE RUN.
  destruct (@frontend_two_trip_memory_decode fe ge locals le memory column inner_bound body le' final
    CM ZERO TWO (@normal_statement_execution fe ge locals body (@matrix_body_normal array row column body FLAT))
    (@matrix_body_writes array row column body FLAT) RUN) as [middle [FIRST [SECOND EXIT]]].
  apply (@flattened_singleton_execution fe ge locals body (matrix_store array row column)
    le memory le middle FLAT) in FIRST.
  apply (@flattened_singleton_execution fe ge locals body (matrix_store array row column)
    _ middle _ final FLAT) in SECOND.
  destruct (@matrix_store_inverse fe ge locals le memory array row column i 0 E0 le middle Out_normal
    ROW ZERO RANGE ltac:(lia) FIRST) as [block [ARRAY [_ [_ [_ STORE1]]]]].
  assert (ROW1 : (PTree.set column (Vint (Int.repr 1)) le) ! row = Some (Vint (Int.repr i)))
    by (rewrite PTree.gso by congruence; exact ROW).
  destruct (@matrix_store_inverse fe ge locals _ middle array row column i 1 E0 _ final Out_normal
    ROW1 (PTree.gss _ _ _) RANGE ltac:(lia) SECOND) as [block' [ARRAY' [_ [_ [_ STORE2]]]]].
  assert (SAME : block = block') by (eapply matrix_array_binding_unique; eauto); subst block'.
  exists block, middle; repeat split; auto.
Qed.

Lemma matrix_column_loop_encode fe ge locals le memory array row column bound block j middle final :
  row <> column -> row <> bound -> matrix_array_binding ge locals array block ->
  le ! row = Some (Vint (Int.repr 0)) -> le ! column = Some (Vint (Int.repr j)) ->
  le ! bound = Some (Vint (Int.repr 2)) -> 0 <= j <= 1 ->
  store_action_run (matrix_point block 0 j) memory middle ->
  store_action_run (matrix_point block 1 j) middle final ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound (matrix_store array row column)) E0
    (PTree.set row (Vint (Int.repr 2)) le) final Out_normal.
Proof.
  intros RC RN ARRAY ZERO COLUMN TWO RANGE FIRST SECOND.
  eapply frontend_two_trip_memory_encode; [exact RN|exact ZERO|exact TWO| |].
  - exact (@matrix_store_evaluation fe ge locals le memory array row column block 0 j middle
      ARRAY ZERO COLUMN ltac:(lia) RANGE FIRST).
  - apply (@matrix_store_evaluation fe ge locals _ middle array row column block 1 j final ARRAY).
    + apply PTree.gss.
    + rewrite PTree.gso by congruence; exact COLUMN.
    + lia.
    + exact RANGE.
    + exact SECOND.
Qed.

Lemma matrix_reset_decode fe ge locals le memory id trace le' final outcome :
  exec_stmt fe ge locals le memory (matrix_reset id) trace le' final outcome ->
  trace = E0 /\ le' = PTree.set id (Vint (Int.repr 0)) le /\ final = memory /\ outcome = Out_normal.
Proof.
  intro RUN; unfold matrix_reset, matrix_constant in RUN; inversion RUN; subst.
  match goal with CONST : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply eval_const_inv in CONST; subst end; auto.
Qed.

Print Assumptions matrix_row_loop_decode.
Print Assumptions matrix_column_loop_encode.

Lemma matrix_body_quiet array row column body :
  flatten_region body = [matrix_store array row column] ->
  ClightRegionProgress.quiet_statement body = true.
Proof.
  intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor].
Qed.

Lemma matrix_outer_body_normal array row column inner_bound body outer_body :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column inner_bound body] ->
  normal_statement outer_body = true.
Proof.
  intros BODY OUTER; apply flatten_normal_certificate; rewrite OUTER.
  constructor; [reflexivity|constructor; [|constructor]].
  cbn [normal_statement frontend_counted_loop ClightRegionProgress.quiet_statement counter_increment].
  rewrite (@matrix_body_quiet array row column body BODY); reflexivity.
Qed.

Lemma matrix_outer_body_writes array row column inner_bound body outer_body :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column inner_bound body] ->
  writes_only [column] outer_body.
Proof.
  intros BODY OUTER.
  assert (WRITES : writes_only [column] body).
  { apply (@writes_only_weaken [] [column] body); [cbn; tauto|apply (@matrix_body_writes array row column body BODY)]. }
  apply flatten_writes_certificate; rewrite OUTER.
  constructor; [constructor; cbn; auto|constructor; [|constructor]].
  unfold frontend_counted_loop, counter_increment; repeat constructor; auto.
Qed.

Lemma matrix_row_body_decode fe ge locals le memory array row column inner_bound body outer_body i le' final :
  row <> column -> column <> inner_bound ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column inner_bound body] ->
  le ! row = Some (Vint (Int.repr i)) -> le ! inner_bound = Some (Vint (Int.repr 2)) -> 0 <= i <= 1 ->
  exec_stmt fe ge locals le memory outer_body E0 le' final Out_normal ->
  exists block middle, matrix_array_binding ge locals array block /\
    store_action_run (matrix_point block i 0) memory middle /\
    store_action_run (matrix_point block i 1) middle final /\
    le' = PTree.set column (Vint (Int.repr 2)) le.
Proof.
  intros RC CM BODY OUTER ROW TWO RANGE RUN.
  apply (@flattened_pair_execution fe ge locals outer_body (matrix_reset column)
    (frontend_counted_loop column inner_bound body) le memory le' final OUTER) in RUN.
  destruct (sequence_normal_decode RUN) as [reset_temps [reset_memory [RESET INNER]]].
  destruct (@matrix_reset_decode fe ge locals le memory column E0 reset_temps reset_memory Out_normal RESET)
    as [_ [TEMPS [MEMORY _]]]; subst reset_temps reset_memory.
  assert (ROW0 : (PTree.set column (Vint (Int.repr 0)) le) ! row = Some (Vint (Int.repr i)))
    by (rewrite PTree.gso by congruence; exact ROW).
  assert (TWO0 : (PTree.set column (Vint (Int.repr 0)) le) ! inner_bound = Some (Vint (Int.repr 2)))
    by (rewrite PTree.gso by congruence; exact TWO).
  destruct (@matrix_row_loop_decode fe ge locals _ memory array row column inner_bound body i le' final
    RC CM BODY ROW0 (PTree.gss _ _ _) TWO0 RANGE INNER)
    as [block [middle [ARRAY [FIRST [SECOND EXIT]]]]].
  rewrite PTree.set2 in EXIT; exists block, middle; repeat split; assumption.
Qed.

Lemma matrix_source_decode fe ge locals le memory array row bound column inner_bound body outer_body le' final :
  row <> bound -> row <> column -> bound <> column -> row <> inner_bound -> column <> inner_bound ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column inner_bound body] ->
  le ! row = Some (Vint (Int.repr 0)) -> le ! bound = Some (Vint (Int.repr 2)) ->
  le ! inner_bound = Some (Vint (Int.repr 2)) ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 le' final Out_normal ->
  exists block, matrix_array_binding ge locals array block /\
    schedule_run compcert_store_scheduling (matrix_rows block) memory final /\
    le' = PTree.set row (Vint (Int.repr 2)) (PTree.set column (Vint (Int.repr 2)) le).
Proof.
  intros RN RC NC RM CM BODY OUTER ZERO TWO INNER_TWO RUN.
  assert (WRITES := @matrix_outer_body_writes array row column inner_bound body outer_body BODY OUTER).
  assert (FRAME : forall before mem tr after mem',
    exec_stmt fe ge locals before mem outer_body tr after mem' Out_normal -> temp_agree [row;bound] before after).
  { intros; eapply structured_temp_frame; [exact WRITES|cbn; intros id LIVE WRITE; intuition congruence|eassumption]. }
  destruct (@frontend_two_trip_decode fe ge locals le memory row bound outer_body le' final RN ZERO TWO
    (@normal_statement_execution fe ge locals outer_body
      (@matrix_outer_body_normal array row column inner_bound body outer_body BODY OUTER)) FRAME RUN)
    as [l1 [m1 [l2 [FIRST [SECOND EXIT]]]]].
  destruct (@matrix_row_body_decode fe ge locals le memory array row column inner_bound body outer_body 0 l1 m1
    RC CM BODY OUTER ZERO INNER_TWO ltac:(lia) FIRST)
    as [block [middle1 [ARRAY [STORE0 [STORE1 TEMPS1]]]]]; subst l1.
  assert (ROW1 : (PTree.set row (Vint (Int.repr 1)) (PTree.set column (Vint (Int.repr 2)) le)) ! row =
    Some (Vint (Int.repr 1))) by apply PTree.gss.
  assert (INNER_TWO1 : (PTree.set row (Vint (Int.repr 1)) (PTree.set column (Vint (Int.repr 2)) le)) ! inner_bound =
    Some (Vint (Int.repr 2))) by (rewrite !PTree.gso by congruence; exact INNER_TWO).
  destruct (@matrix_row_body_decode fe ge locals _ m1 array row column inner_bound body outer_body 1 l2 final
    RC CM BODY OUTER ROW1 INNER_TWO1 ltac:(lia) SECOND)
    as [block' [middle2 [ARRAY' [STORE2 [STORE3 TEMPS2]]]]].
  assert (SAME : block = block') by (eapply matrix_array_binding_unique; eauto); subst block'.
  exists block; split; [exact ARRAY|split].
  - unfold matrix_rows; econstructor; [exact STORE0|econstructor; [exact STORE1|]].
    econstructor; [exact STORE2|econstructor; [exact STORE3|constructor]].
  - rewrite EXIT, TEMPS2.
    rewrite (@matrix_temps_commute column row (Vint (Int.repr 2)) (Vint (Int.repr 1))
      (PTree.set column (Vint (Int.repr 2)) le)) by congruence.
    rewrite !PTree.set2; reflexivity.
Qed.

Print Assumptions matrix_source_decode.

Lemma matrix_column_body_encode fe ge locals le memory array row bound column block j middle final :
  row <> bound -> row <> column -> matrix_array_binding ge locals array block ->
  le ! column = Some (Vint (Int.repr j)) -> le ! bound = Some (Vint (Int.repr 2)) -> 0 <= j <= 1 ->
  store_action_run (matrix_point block 0 j) memory middle ->
  store_action_run (matrix_point block 1 j) middle final ->
  exec_stmt fe ge locals le memory (matrix_column_body row bound array column) E0
    (PTree.set row (Vint (Int.repr 2)) le) final Out_normal.
Proof.
  intros RN RC ARRAY COLUMN TWO RANGE FIRST SECOND.
  unfold matrix_column_body; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - unfold matrix_reset, matrix_constant; constructor; constructor.
  - replace (PTree.set row (Vint (Int.repr 2)) le) with
      (PTree.set row (Vint (Int.repr 2)) (PTree.set row (Vint (Int.repr 0)) le)) by apply PTree.set2.
    apply (@matrix_column_loop_encode fe ge locals _ memory array row column bound block j middle final
      RC RN ARRAY (PTree.gss _ _ _)); [| |exact RANGE|exact FIRST|exact SECOND].
    + rewrite PTree.gso by congruence; exact COLUMN.
    + rewrite PTree.gso by congruence; exact TWO.
Qed.

Lemma matrix_target_encode fe ge locals le memory array row bound column inner_bound block final :
  row <> bound -> row <> column -> bound <> column -> row <> inner_bound -> column <> inner_bound ->
  matrix_array_binding ge locals array block ->
  le ! bound = Some (Vint (Int.repr 2)) -> le ! inner_bound = Some (Vint (Int.repr 2)) ->
  schedule_run compcert_store_scheduling (matrix_columns block) memory final ->
  exec_stmt fe ge locals le memory (matrix_interchanged row bound column inner_bound array) E0
    (PTree.set row (Vint (Int.repr 2)) (PTree.set column (Vint (Int.repr 2)) le)) final Out_normal.
Proof.
  intros RN RC NC RM CM ARRAY TWO INNER_TWO SCHEDULE.
  destruct (four_store_schedule_decode SCHEDULE) as [m1 [m2 [m3 [STORE00 [STORE10 [STORE01 STORE11]]]]]].
  set (l0 := PTree.set column (Vint (Int.repr 0)) le).
  set (l1 := PTree.set row (Vint (Int.repr 2)) l0).
  set (next := PTree.set column (Vint (Int.repr 1)) l1).
  set (l2 := PTree.set row (Vint (Int.repr 2)) next).
  assert (N0 : l0 ! bound = Some (Vint (Int.repr 2))).
  { unfold l0; rewrite PTree.gso by congruence; exact TWO. }
  assert (N1 : next ! bound = Some (Vint (Int.repr 2))).
  { unfold next,l1,l0; rewrite !PTree.gso by congruence; exact TWO. }
  assert (J0 : l0 ! column = Some (Vint (Int.repr 0))) by (unfold l0; apply PTree.gss).
  assert (J0' : l1 ! column = Some (Vint (Int.repr 0))).
  { unfold l1; rewrite PTree.gso by congruence; exact J0. }
  assert (J1 : next ! column = Some (Vint (Int.repr 1))) by (unfold next; apply PTree.gss).
  assert (J1' : l2 ! column = Some (Vint (Int.repr 1))).
  { unfold l2; rewrite PTree.gso by congruence; exact J1. }
  assert (M0 : l0 ! inner_bound = Some (Vint (Int.repr 2))).
  { unfold l0; rewrite PTree.gso by congruence; exact INNER_TWO. }
  assert (M1 : l1 ! inner_bound = Some (Vint (Int.repr 2))).
  { unfold l1; rewrite PTree.gso by congruence; exact M0. }
  assert (MN : next ! inner_bound = Some (Vint (Int.repr 2))).
  { unfold next; rewrite PTree.gso by congruence; exact M1. }
  assert (M2 : l2 ! inner_bound = Some (Vint (Int.repr 2))).
  { unfold l2; rewrite PTree.gso by congruence; exact MN. }
  assert (TARGET : exec_stmt fe ge locals le memory (matrix_interchanged row bound column inner_bound array)
    E0 (PTree.set column (Vint (Int.repr 2)) l2) final Out_normal).
  { unfold matrix_interchanged.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := l0) (m1 := memory).
    - unfold l0,matrix_reset,matrix_constant; constructor; constructor.
    - assert (TEST0 := @counter_test_small ge locals l0 memory column inner_bound 0 ltac:(lia) J0 M0).
      eapply frontend_iteration_encode with (body_temps := l1) (body_memory := m2).
      + exact TEST0.
      + eapply counter_condition_active; apply (@counter_test_small ge locals l1 m2 column inner_bound 0);
          [lia|exact J0'|exact M1].
      + exact (@matrix_column_body_encode fe ge locals l0 memory array row bound column block 0 m1 m2
          RN RC ARRAY J0 N0 ltac:(lia) STORE00 STORE10).
      + rewrite (@counter_increment_small column l1 0 J0'); change (0 + 1)%Z with 1%Z.
        assert (TEST1 := @counter_test_small ge locals next m2 column inner_bound 1 ltac:(lia) J1 MN).
        eapply frontend_iteration_encode with (body_temps := l2) (body_memory := final).
        * exact TEST1.
        * eapply counter_condition_active; apply (@counter_test_small ge locals l2 final column inner_bound 1);
            [lia|exact J1'|exact M2].
        * exact (@matrix_column_body_encode fe ge locals next m2 array row bound column block 1 m3 final
            RN RC ARRAY J1 N1 ltac:(lia) STORE01 STORE11).
        * rewrite (@counter_increment_small column l2 1 J1'); change (1 + 1)%Z with 2%Z.
          apply frontend_zero_trip_encode; apply (@counter_test_small ge locals _ final column inner_bound 2).
          -- lia.
          -- apply PTree.gss.
          -- rewrite PTree.gso by congruence; exact M2. }
  assert (EXIT : PTree.set column (Vint (Int.repr 2)) l2 =
    PTree.set row (Vint (Int.repr 2)) (PTree.set column (Vint (Int.repr 2)) le)).
  { unfold l2,next,l1,l0.
    rewrite (@matrix_temps_commute row column (Vint (Int.repr 2)) (Vint (Int.repr 1))
      (PTree.set row (Vint (Int.repr 2)) (PTree.set column (Vint (Int.repr 0)) le))) by congruence.
    rewrite !PTree.set2.
    rewrite (@matrix_temps_commute column row (Vint (Int.repr 2)) (Vint (Int.repr 2))
      (PTree.set column (Vint (Int.repr 0)) le)) by congruence.
    rewrite PTree.set2; reflexivity. }
  rewrite EXIT in TARGET; exact TARGET.
Qed.

Print Assumptions matrix_target_encode.
