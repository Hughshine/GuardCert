From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightCountedProtocol ClightFramedLoop ClightZeroTrip ClightTempFrame
  ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightFrontendLoopProtocol ClightFrontendRegion ClightRegionProgress
  ClightRectangularLoops ClightRectangularStore ClightRectangularGuard ClightNoWrap ClightPureExpr ClightLoopExecution ClightParametricLoops.
From GuardMemory Require Import GuardMemoryVariableCounterExit GuardMemoryRaggedLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_ragged_bound row parameter :=
  Ebinop Oadd (Etempvar row type_int32s) (Etempvar parameter type_int32s) type_int32s.
Definition memory_ragged_setup row parameter inner_bound :=
  Sset inner_bound (memory_ragged_bound row parameter).
Definition memory_ragged_outer row parameter column inner_bound body :=
  Ssequence (memory_ragged_setup row parameter inner_bound)
    (rectangle_outer_body column inner_bound body).
Definition memory_ragged_settle column inner_bound columns i temps :=
  PTree.set column (Vint (Int.repr (i+columns)))
    (PTree.set inner_bound (Vint (Int.repr (i+columns))) temps).

Lemma memory_ragged_setup_decode fe ge locals le memory row parameter inner_bound i columns after final :
  le ! row = Some (Vint (Int.repr i)) -> le ! parameter = Some (Vint (Int.repr columns)) ->
  exec_stmt fe ge locals le memory (memory_ragged_setup row parameter inner_bound) E0 after final Out_normal ->
  after = PTree.set inner_bound (Vint (Int.repr (i+columns))) le /\ final = memory.
Proof.
  intros ROW PARAM RUN; unfold memory_ragged_setup in RUN.
  assert (VALUE : eval_expr ge locals le memory (memory_ragged_bound row parameter)
    (Vint (Int.repr (i+columns)))).
  { unfold memory_ragged_bound; eapply eval_Ebinop; [constructor; exact ROW|constructor; exact PARAM|].
    change (Some (Vint (Int.add (Int.repr i) (Int.repr columns))) = Some (Vint (Int.repr (i+columns))));
    rewrite rect_integer_add; reflexivity. }
  inversion RUN; subst.
  match goal with GOT : eval_expr _ _ _ _ _ ?value |- _ =>
    assert (SAME : value = Vint (Int.repr (i+columns))) by (eapply (pure_scalar_determinate (a := memory_ragged_bound row parameter)); [unfold memory_ragged_bound; repeat constructor|eassumption|exact VALUE]); subst value end.
  split; reflexivity.
Qed.

Lemma memory_ragged_counter_exit row column inner_bound columns count x temps :
  row <> column -> row <> inner_bound -> column <> inner_bound ->
  memory_counter_exit row (memory_ragged_settle column inner_bound columns) (S count) x temps =
    PTree.set row (Vint (Int.repr (x+Z.of_nat (S count))))
      (memory_ragged_settle column inner_bound columns (x+Z.of_nat count) temps).
Proof.
  intros RC RK CK; revert x temps; induction count as [|count IH]; intros x temps.
  - cbn [memory_counter_exit]; rewrite Z.add_0_r; reflexivity.
  - change (memory_counter_exit row (memory_ragged_settle column inner_bound columns) (S count) (x+1)
      (PTree.set row (Vint (Int.repr (x+1))) (memory_ragged_settle column inner_bound columns x temps)) =
      PTree.set row (Vint (Int.repr (x+Z.of_nat (S (S count)))))
        (memory_ragged_settle column inner_bound columns (x+Z.of_nat (S count)) temps)).
    rewrite IH.
    unfold memory_ragged_settle.
    apply PTree.extensionality; intro id.
    destruct (peq id row) as [->|NR]; [rewrite !PTree.gss; f_equal; f_equal; f_equal; rewrite !Nat2Z.inj_succ; lia|].
    rewrite !PTree.gso by congruence.
    destruct (peq id column) as [->|NC]; [repeat first [rewrite PTree.gss | rewrite PTree.gso by congruence]; f_equal; f_equal; f_equal; rewrite !Nat2Z.inj_succ; lia|].
    rewrite !PTree.gso by congruence.
    destruct (peq id inner_bound) as [->|NK]; [repeat first [rewrite PTree.gss | rewrite PTree.gso by congruence]; f_equal; f_equal; f_equal; rewrite !Nat2Z.inj_succ; lia|].
    rewrite !PTree.gso by congruence; reflexivity.
Qed.

Lemma memory_ragged_outer_writes row column inner_bound parameter body outer_body :
  writes_only [] body ->
  flatten_region outer_body = [memory_ragged_setup row parameter inner_bound; rectangle_reset column;
    frontend_counted_loop column inner_bound body] -> writes_only [inner_bound;column] outer_body.
Proof.
  intros WRITES OUTER; apply flatten_writes_certificate; rewrite OUTER.
  constructor; [constructor; cbn; auto|constructor; [constructor; cbn; auto|constructor; [|constructor]]].
  unfold frontend_counted_loop,counter_increment; repeat constructor;
    try (cbn; auto); eapply writes_only_weaken; [|exact WRITES]; cbn; tauto.
Qed.
Lemma memory_ragged_outer_normal row column inner_bound parameter body outer_body :
  quiet_statement body = true ->
  flatten_region outer_body = [memory_ragged_setup row parameter inner_bound; rectangle_reset column;
    frontend_counted_loop column inner_bound body] -> normal_statement outer_body = true.
Proof.
  intros QUIET OUTER; apply flatten_normal_certificate; rewrite OUTER; constructor; [reflexivity|].
  constructor; [reflexivity|constructor; [|constructor]].
  cbn [normal_statement frontend_counted_loop quiet_statement counter_increment]; rewrite QUIET; reflexivity.
Qed.

Section SOURCE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable row bound column inner_bound parameter : ident.
Variable body outer_body : statement.
Variable point : Z -> Z -> mem -> mem -> Prop.
Variable rows columns : nat.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RK : row <> inner_bound.
Hypothesis NK : bound <> inner_bound.
Hypothesis CK : column <> inner_bound.
Hypothesis MP : parameter <> column.
Hypothesis MK : parameter <> inner_bound.
Hypothesis MR : parameter <> row.
Hypothesis ROWS : rows <> O.
Hypothesis NS : signed_range (Z.of_nat rows).
Hypothesis INNER : forall i, 0 <= i < Z.of_nat rows -> signed_range (i+Z.of_nat columns).
Hypothesis NORMAL : normal_statement body = true.
Hypothesis QUIET : quiet_statement body = true.
Hypothesis WRITES : writes_only [] body.
Hypothesis OUTER : flatten_region outer_body =
  [memory_ragged_setup row parameter inner_bound; rectangle_reset column;
    frontend_counted_loop column inner_bound body].

Lemma memory_ragged_row_decode
  (DECODE : forall i j le memory after final, 0 <= i < Z.of_nat rows -> 0 <= j < i+Z.of_nat columns ->
    le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
    exec_stmt fe ge locals le memory body E0 after final Out_normal -> point i j memory final /\ after = le) :
  forall i le memory after final, 0 <= i < Z.of_nat rows ->
    le ! row = Some (Vint (Int.repr i)) -> le ! parameter = Some (Vint (Int.repr (Z.of_nat columns))) ->
    exec_stmt fe ge locals le memory outer_body E0 after final Out_normal ->
    counted_iterations (point i) (Z.to_nat (i+Z.of_nat columns)) 0 memory final /\
      after = memory_ragged_settle column inner_bound (Z.of_nat columns) i le.
Proof.
  intros i le memory after final I ROW PARAM RUN.
  apply flatten_region_execution in RUN; rewrite OUTER in RUN.
  inversion RUN; subst.
  match goal with SET : exec_stmt _ _ _ _ _ (memory_ragged_setup _ _ _) _ _ _ _ |- _ =>
    destruct (@memory_ragged_setup_decode fe ge locals le memory row parameter inner_bound i (Z.of_nat columns)
      _ _ ROW PARAM SET) as [TEMPS MEMORY]; subst end.
  assert (TAIL : exec_stmt fe ge locals
    (PTree.set inner_bound (Vint (Int.repr (i+Z.of_nat columns))) le) memory
    (rectangle_outer_body column inner_bound body) E0 after final Out_normal).
  { match goal with REST : tail_execution _ _ _ [_;_] _ _ _ _ |- _ => inversion REST; subst end.
    match goal with REST : tail_execution _ _ _ [_] _ _ _ _ |- _ => inversion REST; subst end.
    match goal with REST : tail_execution _ _ _ [] _ _ _ _ |- _ => inversion REST; subst end.
    unfold rectangle_outer_body; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eauto. }
  assert (LENGTH : Z.of_nat (Z.to_nat (i+Z.of_nat columns)) = i+Z.of_nat columns)
    by (rewrite Z2Nat.id; lia).
  apply (@flattened_pair_execution fe ge locals (rectangle_outer_body column inner_bound body)
    (rectangle_reset column) (frontend_counted_loop column inner_bound body)
    _ memory after final eq_refl) in TAIL.
  destruct (sequence_normal_decode TAIL) as [middle [m1 [RESET LOOP]]].
  destruct (rectangle_reset_decode RESET) as [_ [SET [MEM _]]]; subst middle m1.
  set (prepared := PTree.set column (Vint Int.zero)
    (PTree.set inner_bound (Vint (Int.repr (i+Z.of_nat columns))) le)) in *.
  destruct (@frontend_parametric_decode fe ge locals column inner_bound body None (point i) 0
    (i+Z.of_nat columns) [row] prepared CK
    ltac:(unfold settle_fresh,settle_names; cbn; tauto)
    ltac:(cbn [settle_fresh settle_names In]; intuition congruence)
    ltac:(cbn [settle_fresh settle_names In]; tauto) NORMAL WRITES (@INNER i I)
    ltac:(intros j temps before next after' J COL K FRAME BODY;
      eapply DECODE; auto; rewrite FRAME by (cbn; auto);
      unfold prepared; rewrite !PTree.gso by congruence; exact ROW)
    (Z.to_nat (i+Z.of_nat columns)) 0 prepared memory after final
    ltac:(rewrite LENGTH; lia) ltac:(change (-2147483648 <= 0 <= 2147483647); lia)
    ltac:(lia) ltac:(unfold prepared; change (Int.repr 0) with Int.zero; apply PTree.gss)
    ltac:(unfold prepared; rewrite PTree.gso by congruence; apply PTree.gss)
    (temp_agree_refl [row] _) LOOP) as [ITER EXIT].
  split; [exact ITER|].
  rewrite EXIT; unfold loop_exit; destruct (Z.to_nat (i+Z.of_nat columns));
    cbn [loop_settle]; unfold prepared,memory_ragged_settle.
  - assert (ZERO : i+Z.of_nat columns = 0) by (rewrite <- LENGTH; reflexivity).
    rewrite ZERO; change (Int.repr 0) with Int.zero; rewrite PTree.set2; reflexivity.
  - rewrite PTree.set2; reflexivity.
Qed.

Theorem memory_ragged_source_decode
  (DECODE : forall i j le memory after final, 0 <= i < Z.of_nat rows -> 0 <= j < i+Z.of_nat columns ->
    le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
    exec_stmt fe ge locals le memory body E0 after final Out_normal -> point i j memory final /\ after = le) :
  forall le memory after final,
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! parameter = Some (Vint (Int.repr (Z.of_nat columns))) ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  memory_ragged_iterations point rows columns memory final /\
    after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
      (memory_ragged_settle column inner_bound (Z.of_nat columns) (Z.of_nat rows-1) le).
Proof.
  intros le memory after final ZERO BOUND PARAM RUN.
  destruct (@frontend_variable_settle_decode fe ge locals row bound outer_body
    (memory_ragged_settle column inner_bound (Z.of_nat columns))
    (fun i => counted_iterations (point i) (Z.to_nat (i+Z.of_nat columns)) 0)
    0 (Z.of_nat rows) [parameter] le RN (@memory_ragged_outer_normal row column inner_bound parameter body outer_body QUIET OUTER)
    ltac:(intros; eapply structured_temp_frame; [exact (@memory_ragged_outer_writes row column inner_bound parameter body outer_body WRITES OUTER)| |eassumption]; cbn; intuition congruence)
    ltac:(intros; unfold memory_ragged_settle; rewrite !PTree.gso by congruence; reflexivity)
    ltac:(intros; unfold memory_ragged_settle; eapply temp_agree_trans; apply temp_agree_set; cbn; intuition congruence)
    ltac:(cbn; intuition congruence) NS
    ltac:(intros i temps before next after' RI I N FRAME BODY; apply memory_ragged_row_decode with (DECODE := DECODE); auto; rewrite FRAME by (cbn; auto); exact PARAM)
    rows 0 le memory after final ltac:(lia) ltac:(change (-2147483648 <= 0 <= 2147483647); lia)
    ltac:(lia) ZERO BOUND (temp_agree_refl _ _) RUN) as [ITER EXIT].
  split; [exact ITER|].
  destruct rows as [|rest]; [contradiction|].
  rewrite memory_ragged_counter_exit in EXIT by congruence.
  replace (0+Z.of_nat (S rest)) with (Z.of_nat (S rest)) in EXIT by lia.
  replace (0+Z.of_nat rest) with (Z.of_nat (S rest)-1) in EXIT by (rewrite Nat2Z.inj_succ; lia).
  exact EXIT.
Qed.
End SOURCE.
Print Assumptions memory_ragged_source_decode.

Lemma memory_ragged_source_guard_domain fe ge locals le memory row bound column inner_bound parameter body outer_body after final :
  row <> column -> row <> inner_bound -> bound <> column -> bound <> inner_bound -> row <> bound ->
  normal_statement outer_body = true -> writes_only [inner_bound;column] outer_body ->
  flatten_region outer_body = [memory_ragged_setup row parameter inner_bound; rectangle_reset column;
    frontend_counted_loop column inner_bound body] ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  rectangle_guard_domain row bound parameter (Entry ge locals le memory).
Proof.
  intros RC RK NC NK RN NORMAL WRITES OUTER RUN.
  destruct (@frontend_entry_test fe ge locals le memory row bound outer_body after final RUN) as [flag TEST].
  destruct (@counter_test_domain row bound (Entry ge locals le memory) flag TEST) as [x [upper [X UP]]].
  cbn [entry_temps] in X,UP.
  split; [exists x; exact X|split; [exists upper; exact UP|]].
  intros ZERO POS; change (le ! row = Some (Vint Int.zero)) in ZERO.
  cbn [entry_temps] in POS; unfold temp_word in POS; rewrite UP in POS.
  assert (TRUE : expression_test (counter_condition row bound) (Entry ge locals le memory) true).
  { replace true with (0 <? Int.signed upper) by (apply Z.ltb_lt; exact POS).
    apply (@counter_condition_at ge locals le memory row bound 0 (Int.signed upper)); auto.
    - rewrite Int.repr_signed; exact UP.
    - change (-2147483648 <= 0 <= 2147483647); lia.
    - apply Int.signed_range. }
  assert (FRAME : forall before mem trace next mem',
    exec_stmt fe ge locals before mem outer_body trace next mem' Out_normal -> temp_agree [row;bound] before next).
  { intros; eapply structured_temp_frame; [exact WRITES|cbn; intuition congruence|eassumption]. }
  destruct (@frontend_iteration_decode fe ge locals le memory row bound outer_body after final TRUE
    (@normal_statement_execution fe ge locals outer_body NORMAL) FRAME RUN) as [middle [m1 [BODY REST]]].
  apply flatten_region_execution in BODY; rewrite OUTER in BODY; inversion BODY; subst.
  match goal with SET : exec_stmt _ _ _ _ _ (memory_ragged_setup _ _ _) _ _ _ _ |- _ =>
    unfold memory_ragged_setup,memory_ragged_bound in SET; inversion SET; subst end.
  match goal with EVAL : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ =>
    destruct (scalar_binary_inv EVAL) as [left [right [LEFT [RIGHT ADD]]]];
    apply scalar_temp_inv in LEFT,RIGHT; rewrite ZERO in LEFT; inversion LEFT; subst left;
    destruct right; cbn in ADD; try discriminate;
    eexists; exact RIGHT end.
Qed.
Print Assumptions memory_ragged_source_guard_domain.
