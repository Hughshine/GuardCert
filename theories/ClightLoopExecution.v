From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightCountedLoop ClightCountedProtocol
  ClightZeroTrip ClightFrontendLoopProtocol ClightFrontendRegion ClightRegionProgress ClightTempFrame.
Import ListNotations.
Set Implicit Arguments.

Lemma quiet_execution_no_return fe ge locals le m source trace le' m' outcome :
  exec_stmt fe ge locals le m source trace le' m' outcome ->
  quiet_statement source = true -> forall value, outcome <> Out_return value.
Proof.
  intro RUN; induction RUN; intro QUIET; cbn [quiet_statement] in QUIET; try discriminate;
    try apply andb_true_iff in QUIET as [LEFT RIGHT];
    intros value RETURN; try discriminate.
  - eapply IHRUN2; eauto.
  - eapply IHRUN; eauto.
  - eapply IHRUN; [destruct b; assumption|exact RETURN].
  - subst out; match goal with STOP : out_break_or_return _ (Out_return _) |- _ => inversion STOP; subst end;
      try discriminate; eapply IHRUN; eauto.
  - subst out; match goal with STOP : out_break_or_return _ (Out_return _) |- _ => inversion STOP; subst end;
      try discriminate; eapply IHRUN2; eauto.
  - eapply IHRUN3; [cbn [quiet_statement]; rewrite LEFT, RIGHT; reflexivity|exact RETURN].
Qed.

Lemma quiet_loop_normal fe ge locals le m first second trace le' m' outcome :
  quiet_statement (Sloop first second) = true ->
  exec_stmt fe ge locals le m (Sloop first second) trace le' m' outcome -> outcome = Out_normal.
Proof.
  intros QUIET RUN; pose proof (@quiet_execution_no_return fe ge locals le m
    (Sloop first second) trace le' m' outcome RUN QUIET) as NORETURN.
  remember (Sloop first second) as source eqn:SOURCE in RUN.
  induction RUN; inversion SOURCE; subst; clear SOURCE.
  - match goal with STOP : out_break_or_return _ _ |- _ => inversion STOP; subst end;
      [reflexivity|exfalso; eapply NORETURN; reflexivity].
  - match goal with STOP : out_break_or_return _ _ |- _ => inversion STOP; subst end;
      [reflexivity|exfalso; eapply NORETURN; reflexivity].
  - apply IHRUN3; [reflexivity|exact NORETURN].
Qed.

Lemma frontend_true_prelude fe ge locals le m iterator bound trace le' m' outcome :
  exec_stmt fe ge locals le m
    (Ssequence Sskip (Sifthenelse (counter_condition iterator bound) Sskip Sbreak))
    trace le' m' outcome ->
  expression_test (counter_condition iterator bound) (Entry ge locals le m) true ->
  trace = E0 /\ le' = le /\ m' = m /\ outcome = Out_normal.
Proof.
  intros RUN TEST; apply skip_prefix_exec in RUN; inversion RUN; subst.
  assert (TEST' : expression_test (counter_condition iterator bound) (Entry ge locals le m) b)
    by (eexists; split; eassumption).
  pose proof (pure_test_determinate (counter_condition_pure iterator bound) TEST' TEST) as FLAG; subst b.
  match goal with SKIP : exec_stmt _ _ _ _ _ Sskip _ _ _ _ |- _ => inversion SKIP; subst end.
  repeat split; reflexivity.
Qed.

Lemma frontend_true_header fe ge locals le m iterator bound body trace le' m' outcome :
  exec_stmt fe ge locals le m
    (Ssequence (Ssequence Sskip (Sifthenelse (counter_condition iterator bound) Sskip Sbreak)) body)
    trace le' m' outcome ->
  expression_test (counter_condition iterator bound) (Entry ge locals le m) true ->
  exec_stmt fe ge locals le m body trace le' m' outcome.
Proof.
  intros RUN TEST; inversion RUN; subst.
  all: match goal with PRE : exec_stmt _ _ _ _ _ (Ssequence Sskip _) ?tr ?lp ?mp ?op |- _ =>
    pose proof (@frontend_true_prelude fe ge locals le m iterator bound tr lp mp op PRE TEST)
      as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst
  end; cbn in *; try contradiction; assumption.
Qed.

Lemma increment_execution_exact fe ge locals le m iterator bound trace le' m' outcome :
  counter_active iterator bound le ->
  exec_stmt fe ge locals le m (Ssequence Sskip (counter_increment iterator)) trace le' m' outcome ->
  trace = E0 /\ le' = increment_temps iterator le /\ m' = m /\ outcome = Out_normal.
Proof.
  intros ACTIVE RUN; apply skip_prefix_exec in RUN.
  destruct (@counter_increment_evaluation ge locals iterator bound le m ACTIVE) as [v' [EVAL SET]].
  inversion RUN; subst.
  assert (PURE : pure_scalar (Ebinop Oadd (Etempvar iterator type_int32s)
    (Econst_int Int.one type_int32s) type_int32s)) by repeat constructor.
  match goal with SOURCE : eval_expr _ _ _ _ _ ?v |- _ =>
    pose proof (@pure_scalar_determinate _ PURE ge locals le _ v v' SOURCE EVAL) as VALUE; subst v
  end.
  repeat split; auto.
Qed.

(** Decode one actual frontend iteration. Normality and the frame are explicit
    language properties of the body, independent of its representation. *)
Lemma frontend_iteration_decode fe ge locals le m iterator bound body le' m' :
  expression_test (counter_condition iterator bound) (Entry ge locals le m) true ->
  (forall before memory tr after memory' outcome,
    exec_stmt fe ge locals before memory body tr after memory' outcome -> outcome = Out_normal) ->
  (forall before memory tr after memory',
    exec_stmt fe ge locals before memory body tr after memory' Out_normal ->
    temp_agree [iterator; bound] before after) ->
  exec_stmt fe ge locals le m (frontend_counted_loop iterator bound body) E0 le' m' Out_normal ->
  exists body_temps body_memory,
    exec_stmt fe ge locals le m body E0 body_temps body_memory Out_normal /\
    exec_stmt fe ge locals (increment_temps iterator body_temps) body_memory
      (frontend_counted_loop iterator bound body) E0 le' m' Out_normal.
Proof.
  intros TEST NORMAL FRAME RUN; inversion RUN; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _ (Ssequence (Ssequence Sskip _) ?body_code) _ _ _ _ |- _ =>
    pose proof (frontend_true_header HEADER TEST) as BODY_EXEC; clear HEADER;
    pose proof (NORMAL _ _ _ _ _ _ BODY_EXEC) as OUTCOME; subst
  end.
  - match goal with BAD : out_break_or_return Out_normal _ |- _ => inversion BAD end.
  - match goal with BODY_RUN : exec_stmt _ _ _ _ _ body _ ?bl ?bm Out_normal,
      INC : exec_stmt _ _ _ _ _ (Ssequence Sskip (counter_increment iterator)) ?tr ?al ?am ?out |- _ =>
      pose proof (FRAME _ _ _ _ _ BODY_RUN) as SAME;
      pose proof (@counter_condition_active ge locals le m iterator bound TEST) as ACTIVE;
      assert (ACTIVE_BODY : counter_active iterator bound bl)
        by (destruct ACTIVE as [x [upper [X [UP LT]]]]; exists x,upper;
          rewrite (SAME iterator (or_introl eq_refl)), (SAME bound (or_intror (or_introl eq_refl))); auto);
      pose proof (@increment_execution_exact fe ge locals bl bm iterator bound tr al am out ACTIVE_BODY INC)
        as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst
    end.
    match goal with BAD : out_break_or_return Out_normal _ |- _ => inversion BAD end.
  - match goal with BODY_RUN : exec_stmt _ _ _ _ _ body _ ?bl ?bm Out_normal,
      INC : exec_stmt _ _ _ _ _ (Ssequence Sskip (counter_increment iterator)) ?tr ?al ?am ?out |- _ =>
      pose proof (FRAME _ _ _ _ _ BODY_RUN) as SAME;
      pose proof (@counter_condition_active ge locals le m iterator bound TEST) as ACTIVE;
      assert (ACTIVE_BODY : counter_active iterator bound bl)
        by (destruct ACTIVE as [x [upper [X [UP LT]]]]; exists x,upper;
          rewrite (SAME iterator (or_introl eq_refl)), (SAME bound (or_intror (or_introl eq_refl))); auto);
      pose proof (@increment_execution_exact fe ge locals bl bm iterator bound tr al am out ACTIVE_BODY INC)
        as [TRACE [TEMPS [MEMORY OUTCOME]]]; subst
    end.
    match goal with EMPTY : _ ** _ ** _ = E0 |- _ =>
      apply Eapp_E0_inv in EMPTY as [FIRST REST]; apply Eapp_E0_inv in REST as [SECOND THIRD]; subst
    end.
    do 2 eexists; split; eassumption.
Qed.

Print Assumptions frontend_iteration_decode.

Lemma frontend_iteration_encode fe ge locals le m iterator bound body body_temps body_memory le' m' :
  expression_test (counter_condition iterator bound) (Entry ge locals le m) true ->
  counter_active iterator bound body_temps ->
  exec_stmt fe ge locals le m body E0 body_temps body_memory Out_normal ->
  exec_stmt fe ge locals (increment_temps iterator body_temps) body_memory
    (frontend_counted_loop iterator bound body) E0 le' m' Out_normal ->
  exec_stmt fe ge locals le m (frontend_counted_loop iterator bound body) E0 le' m' Out_normal.
Proof.
  intros [value [EVAL BOOL]] ACTIVE BODY REST.
  eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0)
    (out1 := Out_normal).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|exact BODY].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
  - constructor.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
    apply counter_increment_normal with (bound := bound); exact ACTIVE.
  - exact REST.
Qed.

Lemma frontend_zero_trip_encode fe ge locals le m iterator bound body :
  expression_test (counter_condition iterator bound) (Entry ge locals le m) false ->
  exec_stmt fe ge locals le m (frontend_counted_loop iterator bound body) E0 le m Out_normal.
Proof.
  intros [value [EVAL BOOL]]. eapply exec_Sloop_stop1 with (out' := Out_break).
  - eapply exec_Sseq_2 with (out := Out_break); [|discriminate].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|].
    eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor].
  - constructor.
Qed.

Lemma counter_test_small ge locals le m iterator bound index :
  (0 <= index <= 2)%Z ->
  le ! iterator = Some (Vint (Int.repr index)) -> le ! bound = Some (Vint (Int.repr 2)) ->
  expression_test (counter_condition iterator bound) (Entry ge locals le m) (index <? 2)%Z.
Proof.
  intros SMALL ITERATOR BOUND. exists (Val.of_bool (Int.lt (Int.repr index) (Int.repr 2))); split.
  - eapply eval_Ebinop; [constructor; exact ITERATOR|constructor; exact BOUND|reflexivity].
  - rewrite bool_of_bool. unfold Int.lt.
    rewrite (Int.signed_repr index) by (change (-2147483648 <= index <= 2147483647)%Z; lia).
    change (Int.signed (Int.repr 2)) with 2%Z.
    f_equal; destruct (zlt index 2); [symmetry; apply Z.ltb_lt|symmetry; apply Z.ltb_ge]; lia.
Qed.

Lemma counter_increment_small iterator le index :
  le ! iterator = Some (Vint (Int.repr index)) ->
  increment_temps iterator le = PTree.set iterator (Vint (Int.repr (index + 1))) le.
Proof.
  intro LOOKUP; unfold increment_temps; rewrite LOOKUP.
  assert (ADD : Int.add (Int.repr index) Int.one = Int.repr (index + 1)).
  { change (Int.add (Int.repr index) (Int.repr 1) = Int.repr (index + 1)).
    unfold Int.add; apply Int.eqm_samerepr; apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr. }
  rewrite ADD; reflexivity.
Qed.

Lemma frontend_two_trip_decode fe ge locals le m iterator bound body le' m' :
  iterator <> bound ->
  le ! iterator = Some (Vint (Int.repr 0)) -> le ! bound = Some (Vint (Int.repr 2)) ->
  (forall before memory tr after memory' outcome,
    exec_stmt fe ge locals before memory body tr after memory' outcome -> outcome = Out_normal) ->
  (forall before memory tr after memory',
    exec_stmt fe ge locals before memory body tr after memory' Out_normal ->
    temp_agree [iterator; bound] before after) ->
  exec_stmt fe ge locals le m (frontend_counted_loop iterator bound body) E0 le' m' Out_normal ->
  exists first_temps first_memory second_temps,
    exec_stmt fe ge locals le m body E0 first_temps first_memory Out_normal /\
    exec_stmt fe ge locals (PTree.set iterator (Vint (Int.repr 1)) first_temps) first_memory
      body E0 second_temps m' Out_normal /\
    le' = PTree.set iterator (Vint (Int.repr 2)) second_temps.
Proof.
  intros DISTINCT ZERO TWO NORMAL FRAME RUN.
  assert (TEST0 := @counter_test_small ge locals le m iterator bound 0 ltac:(lia) ZERO TWO).
  destruct (frontend_iteration_decode TEST0 NORMAL FRAME RUN) as [l1 [m1 [BODY1 REST1]]].
  pose proof (FRAME _ _ _ _ _ BODY1) as FRAME1.
  assert (I0 : l1 ! iterator = Some (Vint (Int.repr 0))) by
    (rewrite (FRAME1 iterator (or_introl eq_refl)); exact ZERO).
  assert (N1 : l1 ! bound = Some (Vint (Int.repr 2))) by
    (rewrite (FRAME1 bound (or_intror (or_introl eq_refl))); exact TWO).
  rewrite (@counter_increment_small iterator l1 0 I0) in REST1; change (0 + 1)%Z with 1%Z in REST1.
  assert (I1 : (PTree.set iterator (Vint (Int.repr 1)) l1) ! iterator = Some (Vint (Int.repr 1)))
    by apply PTree.gss.
  assert (N1' : (PTree.set iterator (Vint (Int.repr 1)) l1) ! bound = Some (Vint (Int.repr 2)))
    by (rewrite PTree.gso by congruence; exact N1).
  assert (TEST1 := @counter_test_small ge locals _ m1 iterator bound 1 ltac:(lia) I1 N1').
  destruct (frontend_iteration_decode TEST1 NORMAL FRAME REST1) as [l2 [m2 [BODY2 REST2]]].
  pose proof (FRAME _ _ _ _ _ BODY2) as FRAME2.
  assert (I1' : l2 ! iterator = Some (Vint (Int.repr 1))) by
    (rewrite (FRAME2 iterator (or_introl eq_refl)); exact I1).
  assert (N2 : l2 ! bound = Some (Vint (Int.repr 2))) by
    (rewrite (FRAME2 bound (or_intror (or_introl eq_refl))); exact N1').
  rewrite (@counter_increment_small iterator l2 1 I1') in REST2; change (1 + 1)%Z with 2%Z in REST2.
  assert (I2 : (PTree.set iterator (Vint (Int.repr 2)) l2) ! iterator = Some (Vint (Int.repr 2)))
    by apply PTree.gss.
  assert (N2' : (PTree.set iterator (Vint (Int.repr 2)) l2) ! bound = Some (Vint (Int.repr 2)))
    by (rewrite PTree.gso by congruence; exact N2).
  assert (TEST2 := @counter_test_small ge locals _ m2 iterator bound 2 ltac:(lia) I2 N2').
  destruct (frontend_zero_trip_result REST2 TEST2) as [TEMPS MEMORY]; subst.
  do 3 eexists; repeat split; eauto.
Qed.

Print Assumptions frontend_two_trip_decode.

Lemma memory_body_temporaries_exact fe ge locals le m code trace le' m' outcome :
  writes_only [] code -> exec_stmt fe ge locals le m code trace le' m' outcome -> le' = le.
Proof.
  intros WRITES RUN; apply PTree.extensionality; intro key.
  eapply writes_only_frame; [exact RUN|exact WRITES|intro IN; inversion IN].
Qed.

Lemma frontend_two_trip_memory_decode fe ge locals le m iterator bound body le' m' :
  iterator <> bound ->
  le ! iterator = Some (Vint (Int.repr 0)) -> le ! bound = Some (Vint (Int.repr 2)) ->
  (forall before memory tr after memory' outcome,
    exec_stmt fe ge locals before memory body tr after memory' outcome -> outcome = Out_normal) ->
  writes_only [] body ->
  exec_stmt fe ge locals le m (frontend_counted_loop iterator bound body) E0 le' m' Out_normal ->
  exists middle,
    exec_stmt fe ge locals le m body E0 le middle Out_normal /\
    exec_stmt fe ge locals (PTree.set iterator (Vint (Int.repr 1)) le) middle
      body E0 (PTree.set iterator (Vint (Int.repr 1)) le) m' Out_normal /\
    le' = PTree.set iterator (Vint (Int.repr 2)) le.
Proof.
  intros DISTINCT ZERO TWO NORMAL WRITES RUN.
  assert (FRAME : forall before memory tr after memory',
    exec_stmt fe ge locals before memory body tr after memory' Out_normal ->
    temp_agree [iterator; bound] before after).
  { intros; eapply structured_temp_frame; [exact WRITES|cbn; tauto|eassumption]. }
  destruct (frontend_two_trip_decode DISTINCT ZERO TWO NORMAL FRAME RUN)
    as [l1 [middle [l2 [FIRST [SECOND EXIT]]]]].
  pose proof (memory_body_temporaries_exact WRITES FIRST) as SAME1; subst l1.
  pose proof (memory_body_temporaries_exact WRITES SECOND) as SAME2; subst l2.
  rewrite PTree.set2 in EXIT; eauto.
Qed.

Lemma frontend_two_trip_memory_encode fe ge locals le m iterator bound body middle final :
  iterator <> bound ->
  le ! iterator = Some (Vint (Int.repr 0)) -> le ! bound = Some (Vint (Int.repr 2)) ->
  exec_stmt fe ge locals le m body E0 le middle Out_normal ->
  exec_stmt fe ge locals (PTree.set iterator (Vint (Int.repr 1)) le) middle body E0
    (PTree.set iterator (Vint (Int.repr 1)) le) final Out_normal ->
  exec_stmt fe ge locals le m (frontend_counted_loop iterator bound body) E0
    (PTree.set iterator (Vint (Int.repr 2)) le) final Out_normal.
Proof.
  intros DISTINCT ZERO TWO FIRST SECOND.
  assert (TEST0 := @counter_test_small ge locals le m iterator bound 0 ltac:(lia) ZERO TWO).
  assert (ACTIVE0 := @counter_condition_active ge locals le m iterator bound TEST0).
  eapply frontend_iteration_encode; [exact TEST0|exact ACTIVE0|exact FIRST|].
  rewrite (@counter_increment_small iterator le 0 ZERO); change (0 + 1)%Z with 1%Z.
  assert (I1 : (PTree.set iterator (Vint (Int.repr 1)) le) ! iterator = Some (Vint (Int.repr 1)))
    by apply PTree.gss.
  assert (N1 : (PTree.set iterator (Vint (Int.repr 1)) le) ! bound = Some (Vint (Int.repr 2)))
    by (rewrite PTree.gso by congruence; exact TWO).
  assert (TEST1 := @counter_test_small ge locals _ middle iterator bound 1 ltac:(lia) I1 N1).
  assert (ACTIVE1 := @counter_condition_active ge locals _ middle iterator bound TEST1).
  eapply frontend_iteration_encode; [exact TEST1|exact ACTIVE1|exact SECOND|].
  rewrite (@counter_increment_small iterator _ 1 I1), PTree.set2; change (1 + 1)%Z with 2%Z.
  apply frontend_zero_trip_encode.
  apply (@counter_test_small ge locals _ final iterator bound 2); [lia|apply PTree.gss|].
  rewrite PTree.gso by congruence; exact TWO.
Qed.

Print Assumptions frontend_two_trip_memory_decode.
Print Assumptions frontend_two_trip_memory_encode.
