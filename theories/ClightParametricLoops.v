From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightFramedLoop ClightTempFrame
  ClightCountedProtocol ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightLoopSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loop_settle (extra : option (ident * val)) (le : temp_env) :=
  match extra with None => le | Some (id,value) => PTree.set id value le end.
Definition settle_names (extra : option (ident * val)) : list ident :=
  match extra with None => [] | Some (id,_) => [id] end.
Definition settle_fresh extra iterator bound :=
  ~ In iterator (settle_names extra) /\ ~ In bound (settle_names extra).
Definition loop_exit extra iterator le count upper :=
  PTree.set iterator (Vint (Int.repr upper))
    (match count with O => le | S _ => loop_settle extra le end).

Lemma loop_settle_lookup extra le key : ~ In key (settle_names extra) ->
  (loop_settle extra le) ! key = le ! key.
Proof. destruct extra as [[id value]|]; cbn; auto. intros NE; rewrite PTree.gso; intuition. Qed.
Lemma loop_settle_idempotent extra le : loop_settle extra (loop_settle extra le) = loop_settle extra le.
Proof. destruct extra as [[id value]|]; cbn; auto using PTree.set2. Qed.
Lemma loop_settle_frame extra live le :
  (forall id, In id live -> ~ In id (settle_names extra)) -> temp_agree live le (loop_settle extra le).
Proof. intros FREE id IN; apply loop_settle_lookup, FREE; exact IN. Qed.
Lemma loop_settle_commutes extra le iterator value : ~ In iterator (settle_names extra) ->
  loop_settle extra (PTree.set iterator value le) = PTree.set iterator value (loop_settle extra le).
Proof.
  destruct extra as [[id v]|]; cbn; [|reflexivity]. intro NE.
  apply PTree.extensionality; intro key; rewrite !PTree.gsspec.
  destruct (peq key id), (peq key iterator); subst; intuition congruence.
Qed.
Lemma loop_exit_next extra iterator le count x upper : ~ In iterator (settle_names extra) ->
  loop_exit extra iterator (PTree.set iterator (Vint (Int.repr (x + 1))) (loop_settle extra le)) count upper =
  loop_exit extra iterator le (S count) upper.
Proof.
  intro FRESH; destruct count; unfold loop_exit; cbn -[loop_settle]; [apply PTree.set2|].
  rewrite loop_settle_commutes by exact FRESH; rewrite loop_settle_idempotent, PTree.set2; reflexivity.
Qed.

Section CORRESPONDENCE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable iterator bound : ident.
Variable body : statement.
Variable extra : option (ident * val).
Variable body_sem : Z -> mem -> mem -> Prop.
Variable floor upper : Z.
Variable stable : list ident.
Variable base : temp_env.
Hypothesis DISTINCT : iterator <> bound.
Hypothesis FRESH : settle_fresh extra iterator bound.
Hypothesis ITER_STABLE : ~ In iterator stable.
Hypothesis EXTRA_STABLE : forall id, In id stable -> ~ In id (settle_names extra).
Hypothesis NORMAL : normal_statement body = true.
Hypothesis WRITES : writes_only (settle_names extra) body.
Hypothesis UPPER : signed_range upper.

Lemma parametric_body_frame before memory trace after memory' :
  exec_stmt fe ge locals before memory body trace after memory' Out_normal ->
  temp_agree [iterator;bound] before after.
Proof.
  intro RUN; eapply structured_temp_frame; [exact WRITES| |exact RUN].
  intros key MEMBER; cbn in MEMBER; destruct MEMBER as [EQ|[EQ|BAD]];
    [subst; exact (proj1 FRESH)|subst; exact (proj2 FRESH)|contradiction].
Qed.

Lemma parametric_next_frame le x : temp_agree stable base le ->
  temp_agree stable base (PTree.set iterator (Vint (Int.repr (x + 1))) (loop_settle extra le)).
Proof.
  intro FRAME; eapply temp_agree_trans; [exact FRAME|].
  eapply temp_agree_trans; [apply loop_settle_frame; exact EXTRA_STABLE|].
  apply temp_agree_set; exact ITER_STABLE.
Qed.

Theorem frontend_parametric_decode
  (DECODE : forall x le memory after memory', floor <= x < upper ->
    le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable base le ->
    exec_stmt fe ge locals le memory body E0 after memory' Out_normal ->
    body_sem x memory memory' /\ after = loop_settle extra le) :
  forall count x le memory after memory', upper = x + Z.of_nat count -> signed_range x -> floor <= x ->
    le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable base le ->
    exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound body) E0 after memory' Out_normal ->
    counted_iterations body_sem count x memory memory' /\ after = loop_exit extra iterator le count upper.
Proof.
  induction count as [|count IH]; intros x le memory after memory' LENGTH RANGE FLOOR ITER BOUND FRAME RUN.
  - cbn in LENGTH; assert (SAME : upper = x) by lia; clear LENGTH; subst upper.
    pose proof (@counter_condition_at ge locals le memory iterator bound x x
      DISTINCT ITER BOUND RANGE UPPER) as TEST; rewrite Z.ltb_irrefl in TEST.
    destruct (frontend_zero_trip_result RUN TEST) as [TEMPS MEMORY]; subst.
    split; [constructor|]. cbn [loop_exit]. symmetry; apply counter_temps_same; exact ITER.
  - assert (LT : x < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    pose proof (@counter_condition_at ge locals le memory iterator bound x upper
      DISTINCT ITER BOUND RANGE UPPER) as TEST.
    assert (TRUE : (x <? upper) = true) by (apply Z.ltb_lt; exact LT); rewrite TRUE in TEST.
    destruct (frontend_iteration_decode TEST (@normal_statement_execution fe ge locals body NORMAL) parametric_body_frame RUN)
      as [middle [m1 [BODY REST]]].
    destruct (DECODE x le memory middle m1 ltac:(lia) ITER BOUND FRAME BODY) as [STEP SETTLED]; subst middle.
    assert (I1 : (loop_settle extra le) ! iterator = Some (Vint (Int.repr x))).
    { rewrite loop_settle_lookup by exact (proj1 FRESH); exact ITER. }
    rewrite (@counter_increment_small iterator (loop_settle extra le) x I1) in REST.
    assert (N1 : (PTree.set iterator (Vint (Int.repr (x + 1))) (loop_settle extra le)) ! bound =
      Some (Vint (Int.repr upper))).
    { rewrite PTree.gso by congruence; rewrite loop_settle_lookup by exact (proj2 FRESH); exact BOUND. }
    destruct (IH (x + 1) (PTree.set iterator (Vint (Int.repr (x + 1))) (loop_settle extra le))
      m1 after memory') as [TAIL EXIT];
      [rewrite Nat2Z.inj_succ in LENGTH; lia|unfold signed_range in *; lia|lia|apply PTree.gss|exact N1|
       apply parametric_next_frame; exact FRAME|exact REST|].
    split; [econstructor; eauto|rewrite EXIT, loop_exit_next by exact (proj1 FRESH); reflexivity].
Qed.

Theorem frontend_parametric_encode
  (ENCODE : forall x le memory memory', floor <= x < upper ->
    le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable base le ->
    body_sem x memory memory' ->
    exec_stmt fe ge locals le memory body E0 (loop_settle extra le) memory' Out_normal) :
  forall count x memory memory', counted_iterations body_sem count x memory memory' ->
  forall le, upper = x + Z.of_nat count -> signed_range x -> floor <= x ->
    le ! iterator = Some (Vint (Int.repr x)) -> le ! bound = Some (Vint (Int.repr upper)) ->
    temp_agree stable base le ->
    exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound body) E0
      (loop_exit extra iterator le count upper) memory' Out_normal.
Proof.
  intros count x memory memory' SOURCE; induction SOURCE;
    intros le LENGTH RANGE FLOOR ITER BOUND FRAME.
  - cbn in LENGTH; assert (SAME : upper = x) by lia; clear LENGTH; subst upper.
    assert (EXIT : loop_exit extra iterator le O x = le).
    { unfold loop_exit; apply counter_temps_same; exact ITER. }
    rewrite EXIT.
    apply frontend_zero_trip_encode.
    pose proof (@counter_condition_at ge locals le s iterator bound x x
      DISTINCT ITER BOUND RANGE UPPER) as TEST; rewrite Z.ltb_irrefl in TEST; exact TEST.
  - assert (LT : x < upper) by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    pose proof (@counter_condition_at ge locals le s0 iterator bound x upper
      DISTINCT ITER BOUND RANGE UPPER) as TEST.
    assert (TRUE : (x <? upper) = true) by (apply Z.ltb_lt; exact LT); rewrite TRUE in TEST.
    assert (I1 : (loop_settle extra le) ! iterator = Some (Vint (Int.repr x))).
    { rewrite loop_settle_lookup by exact (proj1 FRESH); exact ITER. }
    assert (N1 : (loop_settle extra le) ! bound = Some (Vint (Int.repr upper))).
    { rewrite loop_settle_lookup by exact (proj2 FRESH); exact BOUND. }
    pose proof (@counter_condition_at ge locals (loop_settle extra le) s1 iterator bound x upper
      DISTINCT I1 N1 RANGE UPPER) as ACTIVE_TEST; rewrite TRUE in ACTIVE_TEST.
    change (exec_stmt fe ge locals le s0 (frontend_counted_loop iterator bound body) E0
      (loop_exit extra iterator le (S n) upper) s2 Out_normal).
    rewrite <- (@loop_exit_next extra iterator le n x upper (proj1 FRESH)).
    eapply frontend_iteration_encode; [exact TEST|eapply counter_condition_active; exact ACTIVE_TEST| |].
    + eapply ENCODE; eauto; lia.
    + rewrite (@counter_increment_small iterator (loop_settle extra le) x I1).
      apply IHSOURCE; [rewrite Nat2Z.inj_succ in LENGTH; lia|unfold signed_range in *; lia|lia|apply PTree.gss| |].
      * rewrite PTree.gso by congruence; exact N1.
      * apply parametric_next_frame; exact FRAME.
Qed.
End CORRESPONDENCE.

Print Assumptions frontend_parametric_decode.
Print Assumptions frontend_parametric_encode.
