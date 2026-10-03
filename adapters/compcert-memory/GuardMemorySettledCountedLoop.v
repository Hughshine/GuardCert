From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFramedLoop ClightTempFrame
  ClightCountedProtocol ClightLoopExecution ClightLoopSyntax ClightFrontendLoopProtocol ClightFrontendRegion.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A body may settle any finite collection of control temporaries.  The
    counted-loop proof consumes only its frame, idempotence and commutation
    laws; it does not inspect the body or its memory semantics. *)
Definition settled_exit (settle : temp_env -> temp_env) iterator le count upper :=
  PTree.set iterator (Vint (Int.repr upper))
    (match count with O => le | S _ => settle le end).
Lemma settled_exit_next settle iterator le count x upper :
  (forall le, settle (settle le) = settle le) ->
  (forall le value, settle (PTree.set iterator value le) = PTree.set iterator value (settle le)) ->
  settled_exit settle iterator (PTree.set iterator (Vint (Int.repr (x+1))) (settle le)) count upper =
  settled_exit settle iterator le (S count) upper.
Proof.
  intros IDEMPOTENT COMMUTES; destruct count; unfold settled_exit; cbn; [apply PTree.set2|].
  rewrite COMMUTES,IDEMPOTENT,PTree.set2; reflexivity.
Qed.

Section CORRESPONDENCE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable iterator bound : ident.
Variable body : statement.
Variable written : list ident.
Variable settle : temp_env -> temp_env.
Hypothesis SETTLE_FRAME : forall le key, ~ In key written -> (settle le) ! key = le ! key.
Hypothesis SETTLE_IDEMPOTENT : forall le, settle (settle le) = settle le.
Hypothesis SETTLE_COMMUTES : forall le value, settle (PTree.set iterator value le) = PTree.set iterator value (settle le).
Variable body_sem : Z -> mem -> mem -> Prop.
Variable floor upper : Z.
Variable stable : list ident.
Variable base : temp_env.
Hypothesis DISTINCT : iterator <> bound.
Hypothesis FRESH : ~ In iterator written /\ ~ In bound written.
Hypothesis ITER_STABLE : ~ In iterator stable.
Hypothesis EXTRA_STABLE : forall id, In id stable -> ~ In id (written).
Hypothesis NORMAL : normal_statement body = true.
Hypothesis WRITES : writes_only (written) body.
Hypothesis UPPER : signed_range upper.

Lemma settled_body_frame before memory trace after memory' :
  exec_stmt fe ge locals before memory body trace after memory' Out_normal ->
  temp_agree [iterator;bound] before after.
Proof.
  intro RUN; eapply structured_temp_frame; [exact WRITES| |exact RUN].
  intros key MEMBER; cbn in MEMBER; destruct MEMBER as [EQ|[EQ|BAD]];
    [subst; exact (proj1 FRESH)|subst; exact (proj2 FRESH)|contradiction].
Qed.

Lemma settled_next_frame le x : temp_agree stable base le ->
  temp_agree stable base (PTree.set iterator (Vint (Int.repr (x + 1))) (settle le)).
Proof.
  intro FRAME; eapply temp_agree_trans; [exact FRAME|].
  apply temp_agree_trans with (le1 := settle le).
  - intros key MEMBER; apply SETTLE_FRAME; apply EXTRA_STABLE; exact MEMBER.
  -
  apply temp_agree_set; exact ITER_STABLE.
Qed.

Theorem frontend_settled_decode
  (DECODE : forall x le memory after memory', floor <= x < upper ->
    le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable base le ->
    exec_stmt fe ge locals le memory body E0 after memory' Out_normal ->
    body_sem x memory memory' /\ after = settle le) :
  forall count x le memory after memory', upper = x + Z.of_nat count -> signed_range x -> floor <= x ->
    le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable base le ->
    exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound body) E0 after memory' Out_normal ->
    counted_iterations body_sem count x memory memory' /\ after = settled_exit settle iterator le count upper.
Proof.
  induction count as [|count IH]; intros x le memory after memory' LENGTH RANGE FLOOR ITER BOUND FRAME RUN.
  - cbn in LENGTH; assert (SAME : upper = x) by lia; clear LENGTH; subst upper.
    pose proof (@counter_condition_at ge locals le memory iterator bound x x
      DISTINCT ITER BOUND RANGE UPPER) as TEST; rewrite Z.ltb_irrefl in TEST.
    destruct (frontend_zero_trip_result RUN TEST) as [TEMPS MEMORY]; subst.
    split; [constructor|]. cbn [settled_exit]. symmetry; apply counter_temps_same; exact ITER.
  - assert (LT : x < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    pose proof (@counter_condition_at ge locals le memory iterator bound x upper
      DISTINCT ITER BOUND RANGE UPPER) as TEST.
    assert (TRUE : (x <? upper) = true) by (apply Z.ltb_lt; exact LT); rewrite TRUE in TEST.
    destruct (frontend_iteration_decode TEST (@normal_statement_execution fe ge locals body NORMAL) settled_body_frame RUN)
      as [middle [m1 [BODY REST]]].
    destruct (DECODE x le memory middle m1 ltac:(lia) ITER BOUND FRAME BODY) as [STEP SETTLED]; subst middle.
    assert (I1 : (settle le) ! iterator = Some (Vint (Int.repr x))).
    { rewrite SETTLE_FRAME by exact (proj1 FRESH); exact ITER. }
    rewrite (@counter_increment_small iterator (settle le) x I1) in REST.
    assert (N1 : (PTree.set iterator (Vint (Int.repr (x + 1))) (settle le)) ! bound =
      Some (Vint (Int.repr upper))).
    { rewrite PTree.gso by congruence; rewrite SETTLE_FRAME by exact (proj2 FRESH); exact BOUND. }
    destruct (IH (x + 1) (PTree.set iterator (Vint (Int.repr (x + 1))) (settle le))
      m1 after memory') as [TAIL EXIT];
      [rewrite Nat2Z.inj_succ in LENGTH; lia|unfold signed_range in *; lia|lia|apply PTree.gss|exact N1|
       apply settled_next_frame; exact FRAME|exact REST|].
    split; [econstructor; eauto|rewrite EXIT, settled_exit_next by (exact SETTLE_IDEMPOTENT || exact SETTLE_COMMUTES); reflexivity].
Qed.

Theorem frontend_settled_encode
  (ENCODE : forall x le memory memory', floor <= x < upper ->
    le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable base le ->
    body_sem x memory memory' ->
    exec_stmt fe ge locals le memory body E0 (settle le) memory' Out_normal) :
  forall count x memory memory', counted_iterations body_sem count x memory memory' ->
  forall le, upper = x + Z.of_nat count -> signed_range x -> floor <= x ->
    le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable base le ->
    exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound body) E0
      (settled_exit settle iterator le count upper) memory' Out_normal.
Proof.
  intros count x memory memory' SOURCE; induction SOURCE;
    intros le LENGTH RANGE FLOOR ITER BOUND FRAME.
  - cbn in LENGTH; assert (SAME : upper = x) by lia; clear LENGTH; subst upper.
    assert (EXIT : settled_exit settle iterator le O x = le).
    { unfold settled_exit; apply counter_temps_same; exact ITER. }
    rewrite EXIT.
    apply frontend_zero_trip_encode.
    pose proof (@counter_condition_at ge locals le s iterator bound x x
      DISTINCT ITER BOUND RANGE UPPER) as TEST; rewrite Z.ltb_irrefl in TEST; exact TEST.
  - assert (LT : x < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    pose proof (@counter_condition_at ge locals le s0 iterator bound x upper
      DISTINCT ITER BOUND RANGE UPPER) as TEST.
    assert (TRUE : (x <? upper) = true) by (apply Z.ltb_lt; exact LT); rewrite TRUE in TEST.
    assert (I1 : (settle le) ! iterator = Some (Vint (Int.repr x))).
    { rewrite SETTLE_FRAME by exact (proj1 FRESH); exact ITER. }
    assert (N1 : (settle le) ! bound = Some (Vint (Int.repr upper))).
    { rewrite SETTLE_FRAME by exact (proj2 FRESH); exact BOUND. }
    pose proof (@counter_condition_at ge locals (settle le) s1 iterator bound x upper
      DISTINCT I1 N1 RANGE UPPER) as ACTIVE_TEST; rewrite TRUE in ACTIVE_TEST.
    change (exec_stmt fe ge locals le s0 (frontend_counted_loop iterator bound body) E0
      (settled_exit settle iterator le (S n) upper) s2 Out_normal).
    rewrite <- (@settled_exit_next settle iterator le n x upper SETTLE_IDEMPOTENT SETTLE_COMMUTES).
    eapply frontend_iteration_encode; [exact TEST|eapply counter_condition_active; exact ACTIVE_TEST| |].
    + eapply ENCODE; eauto; lia.
    + rewrite (@counter_increment_small iterator (settle le) x I1).
      apply IHSOURCE; [rewrite Nat2Z.inj_succ in LENGTH; lia|unfold signed_range in *; lia|lia|apply PTree.gss| |].
      * rewrite PTree.gso by congruence; exact N1.
      * apply settled_next_frame; exact FRAME.
Qed.
End CORRESPONDENCE.

Print Assumptions frontend_settled_decode.
Print Assumptions frontend_settled_encode.
