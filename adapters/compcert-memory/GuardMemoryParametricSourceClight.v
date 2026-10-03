From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightRedundantSet ClightNoWrap ClightCountedLoop ClightCountedProtocol ClightFramedLoop ClightZeroTrip ClightTempFrame
  ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightFrontendLoopProtocol ClightFrontendRegion ClightRegionProgress
  ClightRectangularLoops ClightRectangularStore ClightRectangularGuard ClightNoWrap ClightPureExpr ClightLoopExecution ClightParametricLoops.
From GuardMemory Require Import GuardMemoryVariableCounterExit GuardMemoryRaggedLoops GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_parametric_setup inner_bound expression := Sset inner_bound expression.
Definition memory_parametric_settle column inner_bound (upper : Z -> Z) i temps :=
  PTree.set column (Vint (Int.repr (upper i)))
    (PTree.set inner_bound (Vint (Int.repr (upper i))) temps).
Lemma memory_parametric_setup_decode fe ge locals le memory inner_bound expression value after final :
  pure_scalar expression ->
  eval_expr ge locals le memory expression (Vint (Int.repr value)) ->
  exec_stmt fe ge locals le memory (memory_parametric_setup inner_bound expression) E0 after final Out_normal ->
  after = PTree.set inner_bound (Vint (Int.repr value)) le /\ final = memory.
Proof.
  intros PURE VALUE RUN; unfold memory_parametric_setup in RUN; inversion RUN; subst.
  match goal with GOT : eval_expr _ _ _ _ _ ?result |- _ =>
    assert (SAME : result = Vint (Int.repr value))
      by (eapply pure_scalar_determinate; eauto); subst result end.
  split; reflexivity.
Qed.
Lemma memory_parametric_counter_exit row column inner_bound upper count x temps :
  row <> column -> row <> inner_bound -> column <> inner_bound ->
  memory_counter_exit row (memory_parametric_settle column inner_bound upper) (S count) x temps =
    PTree.set row (Vint (Int.repr (x+Z.of_nat (S count))))
      (memory_parametric_settle column inner_bound upper (x+Z.of_nat count) temps).
Proof.
  intros RC RK CK; revert x temps; induction count as [|count IH]; intros x temps.
  - cbn [memory_counter_exit]; rewrite Z.add_0_r; reflexivity.
  - change (memory_counter_exit row (memory_parametric_settle column inner_bound upper) (S count) (x+1)
      (PTree.set row (Vint (Int.repr (x+1))) (memory_parametric_settle column inner_bound upper x temps)) =
      PTree.set row (Vint (Int.repr (x+Z.of_nat (S (S count)))))
        (memory_parametric_settle column inner_bound upper (x+Z.of_nat (S count)) temps)).
    rewrite IH.
    unfold memory_parametric_settle.
    apply PTree.extensionality; intro id.
    destruct (peq id row) as [->|NR]; [rewrite !PTree.gss; f_equal; f_equal; f_equal; rewrite !Nat2Z.inj_succ; lia|].
    rewrite !PTree.gso by congruence.
    destruct (peq id column) as [->|NC]; [repeat first [rewrite PTree.gss | rewrite PTree.gso by congruence]; f_equal; f_equal; f_equal; f_equal; rewrite !Nat2Z.inj_succ; lia|].
    rewrite !PTree.gso by congruence.
    destruct (peq id inner_bound) as [->|NK]; [repeat first [rewrite PTree.gss | rewrite PTree.gso by congruence]; f_equal; f_equal; f_equal; f_equal; rewrite !Nat2Z.inj_succ; lia|].
    rewrite !PTree.gso by congruence; reflexivity.
Qed.

Lemma memory_parametric_outer_writes column inner_bound expression body outer_body :
  writes_only [] body ->
  flatten_region outer_body = [memory_parametric_setup inner_bound expression; rectangle_reset column;
    frontend_counted_loop column inner_bound body] -> writes_only [inner_bound;column] outer_body.
Proof.
  intros WRITES OUTER; apply flatten_writes_certificate; rewrite OUTER.
  constructor; [constructor; cbn; auto|constructor; [constructor; cbn; auto|constructor; [|constructor]]].
  unfold frontend_counted_loop,counter_increment; repeat constructor;
    try (cbn; auto); eapply writes_only_weaken; [|exact WRITES]; cbn; tauto.
Qed.
Lemma memory_parametric_outer_normal column inner_bound expression body outer_body :
  quiet_statement body = true ->
  flatten_region outer_body = [memory_parametric_setup inner_bound expression; rectangle_reset column;
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
Variable row bound column inner_bound : ident.
Variable expression : expr.
Variable upper : Z -> Z.
Variable body outer_body : statement.
Variable point : Z -> Z -> mem -> mem -> Prop.
Variable rows : nat.
Variable stable : list ident.
Variable base : temp_env.
Hypothesis RN : row <> bound.
Hypothesis RC : row <> column.
Hypothesis NC : bound <> column.
Hypothesis RK : row <> inner_bound.
Hypothesis NK : bound <> inner_bound.
Hypothesis CK : column <> inner_bound.
Hypothesis SR : ~ In row stable.
Hypothesis SC : ~ In column stable.
Hypothesis SK : ~ In inner_bound stable.
Hypothesis ROWS : rows <> O.
Hypothesis NS : signed_range (Z.of_nat rows).
Hypothesis INNER : forall i, 0 <= i < Z.of_nat rows -> 0 <= upper i /\ signed_range (upper i).
Hypothesis PURE : pure_scalar expression.
Hypothesis VALUE : forall i le memory, 0 <= i < Z.of_nat rows ->
  le ! row = Some (Vint (Int.repr i)) -> temp_agree stable base le ->
  eval_expr ge locals le memory expression (Vint (Int.repr (upper i))).
Hypothesis NORMAL : normal_statement body = true.
Hypothesis QUIET : quiet_statement body = true.
Hypothesis WRITES : writes_only [] body.
Hypothesis OUTER : flatten_region outer_body =
  [memory_parametric_setup inner_bound expression; rectangle_reset column;
    frontend_counted_loop column inner_bound body].
Lemma memory_parametric_row_decode
  (DECODE : forall i j le memory after final, 0 <= i < Z.of_nat rows -> 0 <= j < upper i ->
    le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
    exec_stmt fe ge locals le memory body E0 after final Out_normal -> point i j memory final /\ after = le) :
  forall i le memory after final, 0 <= i < Z.of_nat rows ->
    le ! row = Some (Vint (Int.repr i)) -> temp_agree stable base le ->
    exec_stmt fe ge locals le memory outer_body E0 after final Out_normal ->
    counted_iterations (point i) (Z.to_nat (upper i)) 0 memory final /\
      after = memory_parametric_settle column inner_bound upper i le.
Proof.
  intros i le memory after final I ROW FRAME RUN.
  apply flatten_region_execution in RUN; rewrite OUTER in RUN.
  inversion RUN; subst.
  match goal with SET : exec_stmt _ _ _ _ _ (memory_parametric_setup _ _) _ _ _ _ |- _ =>
    destruct (@memory_parametric_setup_decode fe ge locals le memory inner_bound expression (upper i)
      _ _ PURE (@VALUE i le memory I ROW FRAME) SET) as [TEMPS MEMORY]; subst end.
  destruct (@INNER i I) as [POSITIVE SAFE].
  assert (TAIL : exec_stmt fe ge locals
    (PTree.set inner_bound (Vint (Int.repr (upper i))) le) memory
    (rectangle_outer_body column inner_bound body) E0 after final Out_normal).
  { match goal with REST : tail_execution _ _ _ [_;_] _ _ _ _ |- _ => inversion REST; subst end.
    match goal with REST : tail_execution _ _ _ [_] _ _ _ _ |- _ => inversion REST; subst end.
    match goal with REST : tail_execution _ _ _ [] _ _ _ _ |- _ => inversion REST; subst end.
    unfold rectangle_outer_body; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eauto. }
  assert (LENGTH : Z.of_nat (Z.to_nat (upper i)) = upper i)
    by (rewrite Z2Nat.id; lia).
  apply (@flattened_pair_execution fe ge locals (rectangle_outer_body column inner_bound body)
    (rectangle_reset column) (frontend_counted_loop column inner_bound body)
    _ memory after final eq_refl) in TAIL.
  destruct (sequence_normal_decode TAIL) as [middle [m1 [RESET LOOP]]].
  destruct (rectangle_reset_decode RESET) as [_ [SET [MEM _]]]; subst middle m1.
  set (prepared := PTree.set column (Vint Int.zero)
    (PTree.set inner_bound (Vint (Int.repr (upper i))) le)) in *.
  destruct (@frontend_parametric_decode fe ge locals column inner_bound body None (point i) 0
    (upper i) [row] prepared CK
    ltac:(unfold settle_fresh,settle_names; cbn; tauto)
    ltac:(cbn [settle_fresh settle_names In]; intuition congruence)
    ltac:(cbn [settle_fresh settle_names In]; tauto) NORMAL WRITES SAFE
    ltac:(intros j temps before next after' J COL K ITER_FRAME BODY;
      eapply DECODE; auto; rewrite ITER_FRAME by (cbn; auto);
      unfold prepared; rewrite !PTree.gso by congruence; exact ROW)
    (Z.to_nat (upper i)) 0 prepared memory after final
    ltac:(rewrite LENGTH; lia) ltac:(change (-2147483648 <= 0 <= 2147483647); lia)
    ltac:(lia) ltac:(unfold prepared; change (Int.repr 0) with Int.zero; apply PTree.gss)
    ltac:(unfold prepared; rewrite PTree.gso by congruence; apply PTree.gss)
    (temp_agree_refl [row] _) LOOP) as [ITER EXIT].
  split; [exact ITER|].
  rewrite EXIT; unfold loop_exit; destruct (Z.to_nat (upper i));
    cbn [loop_settle]; unfold prepared,memory_parametric_settle.
  - assert (ZERO : upper i = 0) by (rewrite <- LENGTH; reflexivity).
    rewrite ZERO; change (Int.repr 0) with Int.zero; rewrite PTree.set2; reflexivity.
  - rewrite PTree.set2; reflexivity.
Qed.

Theorem memory_parametric_source_decode
  (DECODE : forall i j le memory after final, 0 <= i < Z.of_nat rows -> 0 <= j < upper i ->
    le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
    exec_stmt fe ge locals le memory body E0 after final Out_normal -> point i j memory final /\ after = le) :
  forall le memory after final,
  le ! row = Some (Vint Int.zero) -> le ! bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  temp_agree stable base le ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  counted_iterations (fun i => counted_iterations (point i) (Z.to_nat (upper i)) 0) rows 0 memory final /\
    after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
      (memory_parametric_settle column inner_bound upper (Z.of_nat rows-1) le).
Proof.
  intros le memory after final ZERO BOUND FRAME RUN.
  destruct (@frontend_variable_settle_decode fe ge locals row bound outer_body
    (memory_parametric_settle column inner_bound upper)
    (fun i => counted_iterations (point i) (Z.to_nat (upper i)) 0)
    0 (Z.of_nat rows) stable base RN (@memory_parametric_outer_normal column inner_bound expression body outer_body QUIET OUTER)
    ltac:(intros; eapply structured_temp_frame; [exact (@memory_parametric_outer_writes column inner_bound expression body outer_body WRITES OUTER)| |eassumption]; cbn; intuition congruence)
    ltac:(intros; unfold memory_parametric_settle; rewrite !PTree.gso by congruence; reflexivity)
    ltac:(intros; unfold memory_parametric_settle; eapply temp_agree_trans; apply temp_agree_set; assumption)
    SR NS
    ltac:(intros i temps before next after' RI I N AGREEMENT BODY; apply memory_parametric_row_decode with (DECODE := DECODE); auto)
    rows 0 le memory after final ltac:(lia) ltac:(change (-2147483648 <= 0 <= 2147483647); lia)
    ltac:(lia) ZERO BOUND FRAME RUN) as [ITER EXIT].
  split; [exact ITER|].
  destruct rows as [|rest]; [contradiction|].
  rewrite memory_parametric_counter_exit in EXIT by congruence.
  replace (0+Z.of_nat (S rest)) with (Z.of_nat (S rest)) in EXIT by lia.
  replace (0+Z.of_nat rest) with (Z.of_nat (S rest)-1) in EXIT by (rewrite Nat2Z.inj_succ; lia).
  exact EXIT.
Qed.
End SOURCE.
Print Assumptions memory_parametric_source_decode.

(** Defined execution of the first inner header supplies the source words
    needed to evaluate a guard, including reads multiplied by zero. *)
Theorem memory_parametric_outer_source_words fe ge locals le memory column inner_bound expression body outer_body after final :
  column <> inner_bound ->
  flatten_region outer_body =
    [memory_parametric_setup inner_bound (memory_source_affine_code expression);
      rectangle_reset column; frontend_counted_loop column inner_bound body] ->
  exec_stmt fe ge locals le memory outer_body E0 after final Out_normal ->
  forall identifier, In identifier (memory_source_affine_reads expression) ->
    exists word, le ! identifier = Some (Vint word).
Proof.
  intros CK SHAPE RUN.
  apply flatten_region_execution in RUN; rewrite SHAPE in RUN; inversion RUN; subst.
  match goal with SET : exec_stmt _ _ _ _ _ (memory_parametric_setup _ _) _ _ _ _ |- _ =>
    unfold memory_parametric_setup in SET; inversion SET; subst end.
  match goal with REST : tail_execution _ _ _ [_;_] _ _ _ _ |- _ => inversion REST; subst end.
  match goal with RESET : exec_stmt _ _ _ _ _ (rectangle_reset _) _ _ _ _ |- _ =>
    destruct (rectangle_reset_decode RESET) as [_ [TEMPS [MEM _]]]; subst end.
  match goal with REST : tail_execution _ _ _ [_] _ _ _ _ |- _ => inversion REST; subst end.
  match goal with LOOP : exec_stmt _ _ _ _ _ (frontend_counted_loop _ _ _) _ _ _ _ |- _ =>
    destruct (frontend_entry_test LOOP) as [flag TEST];
    destruct (counter_test_domain TEST) as [x [upper [COLUMN BOUND]]] end.
  cbn [entry_temps] in BOUND.
  rewrite PTree.gso in BOUND by congruence; rewrite PTree.gss in BOUND.
  inversion BOUND; subst.
  eapply memory_source_affine_defined_words; eassumption.
Qed.
Print Assumptions memory_parametric_outer_source_words.

Definition memory_parametric_source_word_domain row bound expression s :=
  register_domain row s /\ register_domain bound s /\
    ((entry_temps s) ! row = Some (Vint Int.zero) ->
      0 < Int.signed (temp_word bound (entry_temps s)) ->
      forall identifier, In identifier (memory_source_affine_reads expression) ->
        exists word, (entry_temps s) ! identifier = Some (Vint word)).
Theorem memory_parametric_source_words fe ge locals le memory row bound column inner_bound expression body outer_body after final :
  row <> bound -> row <> column -> row <> inner_bound -> bound <> column -> bound <> inner_bound ->
  column <> inner_bound ->
  normal_statement outer_body = true -> writes_only [inner_bound;column] outer_body ->
  flatten_region outer_body =
    [memory_parametric_setup inner_bound (memory_source_affine_code expression);
      rectangle_reset column; frontend_counted_loop column inner_bound body] ->
  exec_stmt fe ge locals le memory (frontend_counted_loop row bound outer_body) E0 after final Out_normal ->
  memory_parametric_source_word_domain row bound expression (Entry ge locals le memory).
Proof.
  intros RN RC RK NC NK CK NORMAL WRITES SHAPE RUN.
  destruct (frontend_entry_test RUN) as [flag TEST].
  destruct (counter_test_domain TEST) as [x [upper [ROW BOUND]]].
  cbn [entry_temps] in ROW,BOUND.
  split; [exists x; exact ROW|split; [exists upper; exact BOUND|]].
  intros ZERO POSITIVE; cbn [entry_temps] in ZERO,POSITIVE|-*.
  unfold temp_word in POSITIVE; rewrite BOUND in POSITIVE.
  assert (TRUE : expression_test (counter_condition row bound) (Entry ge locals le memory) true).
  { replace true with (0 <? Int.signed upper) by (apply Z.ltb_lt; exact POSITIVE).
    apply (@counter_condition_at ge locals le memory row bound 0 (Int.signed upper)); auto.
    - rewrite Int.repr_signed; exact BOUND.
    - change (-2147483648 <= 0 <= 2147483647); lia.
    - apply Int.signed_range. }
  assert (FRAME : forall before mem trace next mem',
    exec_stmt fe ge locals before mem outer_body trace next mem' Out_normal -> temp_agree [row;bound] before next).
  { intros; eapply structured_temp_frame; [exact WRITES|cbn; intuition congruence|eassumption]. }
  destruct (@frontend_iteration_decode fe ge locals le memory row bound outer_body after final TRUE
    (@normal_statement_execution fe ge locals outer_body NORMAL) FRAME RUN) as [middle [m1 [BODY REST]]].
  eapply memory_parametric_outer_source_words; eassumption.
Qed.
Print Assumptions memory_parametric_source_words.
