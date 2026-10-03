From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightTempFrame ClightStraightLine
  ClightFrontendLoopProtocol ClightRegionProgress ClightLoopExecution ClightLoopSyntax ClightParametricLoops RectangularIteration.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition rectangle_reset id := Sset id (Econst_int Int.zero type_int32s).
Definition rectangle_outer_body inner inner_bound body :=
  Ssequence (rectangle_reset inner) (frontend_counted_loop inner inner_bound body).

Lemma rectangle_reset_decode fe ge locals le memory id trace after final outcome :
  exec_stmt fe ge locals le memory (rectangle_reset id) trace after final outcome ->
  trace = E0 /\ after = PTree.set id (Vint Int.zero) le /\ final = memory /\ outcome = Out_normal.
Proof.
  intro RUN; unfold rectangle_reset in RUN; inversion RUN; subst.
  match goal with CONST : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply eval_const_inv in CONST; subst end; auto.
Qed.

Lemma rectangle_outer_normal inner inner_bound body outer_body :
  quiet_statement body = true ->
  flatten_region outer_body = [rectangle_reset inner; frontend_counted_loop inner inner_bound body] ->
  normal_statement outer_body = true.
Proof.
  intros QUIET FLAT; apply flatten_normal_certificate; rewrite FLAT.
  constructor; [reflexivity|constructor; [|constructor]].
  cbn [normal_statement frontend_counted_loop quiet_statement counter_increment].
  rewrite QUIET; reflexivity.
Qed.
Lemma rectangle_outer_writes inner inner_bound body outer_body : writes_only [] body ->
  flatten_region outer_body = [rectangle_reset inner; frontend_counted_loop inner inner_bound body] ->
  writes_only [inner] outer_body.
Proof.
  intros BODY FLAT; assert (W : writes_only [inner] body).
  { apply (@writes_only_weaken [] [inner] body); [cbn; tauto|exact BODY]. }
  apply flatten_writes_certificate; rewrite FLAT.
  constructor; [constructor; cbn; auto|constructor; [|constructor]].
  unfold frontend_counted_loop, counter_increment; repeat constructor; auto.
Qed.

Section RECTANGLE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable outer outer_bound inner inner_bound : ident.
Variable body outer_body : statement.
Variable point : Z -> Z -> mem -> mem -> Prop.
Variable rows columns : nat.
Hypothesis ON : outer <> outer_bound.
Hypothesis OI : outer <> inner.
Hypothesis NI : outer_bound <> inner.
Hypothesis OM : outer <> inner_bound.
Hypothesis IM : inner <> inner_bound.
Hypothesis ROWS : rows <> O.
Hypothesis RN : signed_range (Z.of_nat rows).
Hypothesis RM : signed_range (Z.of_nat columns).
Hypothesis NORMAL : normal_statement body = true.
Hypothesis QUIET : quiet_statement body = true.
Hypothesis WRITES : writes_only [] body.
Hypothesis OUTER : flatten_region outer_body =
  [rectangle_reset inner; frontend_counted_loop inner inner_bound body].

Lemma rectangle_row_decode
  (DECODE : forall i j le memory after final, 0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
    le ! outer = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
    exec_stmt fe ge locals le memory body E0 after final Out_normal ->
    point i j memory final /\ after = le) :
  forall i le memory after final, 0 <= i < Z.of_nat rows ->
  le ! outer = Some (Vint (Int.repr i)) -> le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  exec_stmt fe ge locals le memory outer_body E0 after final Out_normal ->
  counted_iterations (point i) columns 0 memory final /\
    after = PTree.set inner (Vint (Int.repr (Z.of_nat columns))) le.
Proof.
  intros i le memory after final RI ITER BOUND RUN.
  apply (@flattened_pair_execution fe ge locals outer_body (rectangle_reset inner)
    (frontend_counted_loop inner inner_bound body) le memory after final OUTER) in RUN.
  destruct (sequence_normal_decode RUN) as [middle [m1 [RESET LOOP]]].
  destruct (rectangle_reset_decode RESET) as [_ [SET [MEM _]]]; subst middle m1.
  destruct (@frontend_parametric_decode fe ge locals inner inner_bound body None (point i) 0
    (Z.of_nat columns) [outer] (PTree.set inner (Vint Int.zero) le)
    IM ltac:(unfold settle_fresh, settle_names; cbn; tauto) ltac:(cbn [settle_fresh settle_names In]; intuition congruence) ltac:(cbn [settle_fresh settle_names In]; tauto)
    NORMAL WRITES RM
    ltac:(intros j temps before next after' RJ J M FRAME BODY; apply DECODE; auto;
      rewrite FRAME by (cbn; auto); rewrite PTree.gso by congruence; exact ITER)
    columns 0 (PTree.set inner (Vint Int.zero) le) memory after final
    ltac:(lia) ltac:(change (-2147483648 <= 0 <= 2147483647); lia) ltac:(lia)
    ltac:(change (Int.repr 0) with Int.zero; apply PTree.gss)
    ltac:(rewrite PTree.gso by congruence; exact BOUND)
    (temp_agree_refl [outer] _) LOOP) as [EXEC EXIT].
  split; [exact EXEC|]. rewrite EXIT; unfold loop_exit; destruct columns; cbn [loop_settle];
    rewrite PTree.set2; reflexivity.
Qed.

Theorem rectangle_source_decode
  (DECODE : forall i j le memory after final, 0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
    le ! outer = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
    exec_stmt fe ge locals le memory body E0 after final Out_normal ->
    point i j memory final /\ after = le) :
  forall le memory after final,
  le ! outer = Some (Vint Int.zero) -> le ! outer_bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  exec_stmt fe ge locals le memory (frontend_counted_loop outer outer_bound outer_body) E0 after final Out_normal ->
  rectangular_iterations point rows columns memory final /\
    after = PTree.set outer (Vint (Int.repr (Z.of_nat rows)))
      (PTree.set inner (Vint (Int.repr (Z.of_nat columns))) le).
Proof.
  intros le memory after final ZERO BOUND INNER RUN.
  destruct (@frontend_parametric_decode fe ge locals outer outer_bound outer_body
    (Some (inner,Vint (Int.repr (Z.of_nat columns))))
    (fun i => counted_iterations (point i) columns 0) 0 (Z.of_nat rows) [inner_bound] le
    ON ltac:(unfold settle_fresh, settle_names; cbn; intuition congruence) ltac:(cbn [settle_fresh settle_names In]; intuition congruence) ltac:(cbn [settle_fresh settle_names In]; intuition congruence)
    (@rectangle_outer_normal inner inner_bound body outer_body QUIET OUTER)
    (@rectangle_outer_writes inner inner_bound body outer_body WRITES OUTER) RN
    ltac:(intros i temps before next after' RI I N FRAME BODY;
      apply rectangle_row_decode with (DECODE := DECODE); auto; rewrite FRAME by (cbn; auto); exact INNER)
    rows 0 le memory after final ltac:(lia)
    ltac:(change (-2147483648 <= 0 <= 2147483647); lia) ltac:(lia)
    ZERO BOUND (temp_agree_refl [inner_bound] le) RUN) as [EXEC EXIT].
  split; [exact EXEC|]. rewrite EXIT; unfold loop_exit; destruct rows; [contradiction|reflexivity].
Qed.

Lemma rectangle_row_encode
  (ENCODE : forall i j le memory final, 0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
    le ! outer = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
    point i j memory final -> exec_stmt fe ge locals le memory body E0 le final Out_normal) :
  forall i le memory final, 0 <= i < Z.of_nat rows ->
  le ! outer = Some (Vint (Int.repr i)) -> le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  counted_iterations (point i) columns 0 memory final ->
  exec_stmt fe ge locals le memory (rectangle_outer_body inner inner_bound body) E0
    (PTree.set inner (Vint (Int.repr (Z.of_nat columns))) le) final Out_normal.
Proof.
  intros i le memory final RI ITER BOUND SOURCE.
  assert (LOOP : exec_stmt fe ge locals (PTree.set inner (Vint Int.zero) le) memory
    (frontend_counted_loop inner inner_bound body) E0
    (loop_exit None inner (PTree.set inner (Vint Int.zero) le) columns (Z.of_nat columns)) final Out_normal).
  { eapply (@frontend_parametric_encode fe ge locals inner inner_bound body None (point i) 0
      (Z.of_nat columns) [outer] (PTree.set inner (Vint Int.zero) le)
      IM ltac:(unfold settle_fresh, settle_names; cbn; tauto) ltac:(cbn [settle_fresh settle_names In]; intuition congruence) ltac:(cbn [settle_fresh settle_names In]; tauto) RM).
    - intros j temps before after RJ J M FRAME STEP; apply (ENCODE i j); auto.
      rewrite FRAME by (cbn; auto); rewrite PTree.gso by congruence; exact ITER.
    - exact SOURCE.
    - lia.
    - change (-2147483648 <= 0 <= 2147483647); lia.
    - lia.
    - change (Int.repr 0) with Int.zero; apply PTree.gss.
    - rewrite PTree.gso by congruence; exact BOUND.
    - apply temp_agree_refl. }
  unfold loop_exit in LOOP; destruct columns; cbn [loop_settle] in LOOP; rewrite PTree.set2 in LOOP.
  all: unfold rectangle_outer_body, rectangle_reset; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
    [constructor; constructor|exact LOOP].
Qed.

Theorem rectangle_target_encode
  (ENCODE : forall i j le memory final, 0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
    le ! outer = Some (Vint (Int.repr i)) -> le ! inner = Some (Vint (Int.repr j)) ->
    point i j memory final -> exec_stmt fe ge locals le memory body E0 le final Out_normal) :
  forall le memory final,
  le ! outer = Some (Vint Int.zero) -> le ! outer_bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  le ! inner_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  rectangular_iterations point rows columns memory final ->
  exec_stmt fe ge locals le memory
    (frontend_counted_loop outer outer_bound (rectangle_outer_body inner inner_bound body)) E0
    (PTree.set outer (Vint (Int.repr (Z.of_nat rows)))
      (PTree.set inner (Vint (Int.repr (Z.of_nat columns))) le)) final Out_normal.
Proof.
  intros le memory final ZERO BOUND INNER SOURCE.
  assert (LOOP : exec_stmt fe ge locals le memory
    (frontend_counted_loop outer outer_bound (rectangle_outer_body inner inner_bound body)) E0
    (loop_exit (Some (inner,Vint (Int.repr (Z.of_nat columns)))) outer le rows (Z.of_nat rows)) final Out_normal).
  { eapply (@frontend_parametric_encode fe ge locals outer outer_bound
      (rectangle_outer_body inner inner_bound body) (Some (inner,Vint (Int.repr (Z.of_nat columns))))
      (fun i => counted_iterations (point i) columns 0) 0 (Z.of_nat rows) [inner_bound] le
      ON ltac:(unfold settle_fresh, settle_names; cbn; intuition congruence) ltac:(cbn [settle_fresh settle_names In]; intuition congruence) ltac:(cbn [settle_fresh settle_names In]; intuition congruence) RN).
    - intros i temps before after RI I N FRAME STEP; apply rectangle_row_encode with (ENCODE := ENCODE) (i := i); auto.
      rewrite FRAME by (cbn; auto); exact INNER.
    - exact SOURCE.
    - lia.
    - change (-2147483648 <= 0 <= 2147483647); lia.
    - lia.
    - exact ZERO.
    - exact BOUND.
    - apply temp_agree_refl. }
  unfold loop_exit in LOOP; destruct rows; [contradiction|exact LOOP].
Qed.
End RECTANGLE.

Print Assumptions rectangle_source_decode.
Print Assumptions rectangle_target_encode.
