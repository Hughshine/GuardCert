From Stdlib Require Import List Bool ZArith Arith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightGuard ClightCondition ClightCountedLoop ClightCountedProtocol
  ClightPureExpr ClightRegionProgress ClightFragmentProgress ClightSequenceProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope nat_scope.

Definition maximum_counter_distance := Z.to_nat (Int.max_signed - Int.min_signed).
Lemma counter_distance_bounded iterator bound le :
  counter_remaining iterator bound le <= maximum_counter_distance.
Proof.
  unfold counter_remaining, maximum_counter_distance.
  destruct (le ! iterator) as [x|]; [destruct x|]; try lia;
    destruct (le ! bound) as [upper|]; [destruct upper|]; try lia.
  pose proof (Int.signed_range i); pose proof (Int.signed_range i0).
  destruct (zle 0 (Int.signed i0 - Int.signed i)).
  - apply Z2Nat.inj_le; lia.
  - destruct (Int.signed i0 - Int.signed i)%Z; simpl; lia.
Qed.

Lemma counter_frame_distance iterator bound protected before after :
  preserves_temporaries (iterator :: bound :: protected) before after ->
  counter_remaining iterator bound after = counter_remaining iterator bound before.
Proof.
  intro FRAME; unfold counter_remaining.
  rewrite (FRAME iterator (or_introl eq_refl)),
    (FRAME bound (or_intror (or_introl eq_refl))); reflexivity.
Qed.
Lemma counter_frame_active iterator bound protected before after :
  preserves_temporaries (iterator :: bound :: protected) before after ->
  counter_active iterator bound before -> counter_active iterator bound after.
Proof.
  intros FRAME [x [upper [X [UP LT]]]]. exists x, upper.
  rewrite (FRAME iterator (or_introl eq_refl)),
    (FRAME bound (or_intror (or_introl eq_refl))); auto.
Qed.

Section NESTED_LOOP.
Variables iterator bound : ident.
Hypothesis DISTINCT : iterator <> bound.
Variable protected : list ident.
Hypothesis NOT_WRITTEN : ~ In iterator protected.
Variable body : statement.
Variable F : framed_progress body (iterator :: bound :: protected).
Variable temps : bool.
Variable ge : genv.
Variable fn : function.
Variable outside : cont.
Variable locals : env.
Let header := Sifthenelse (counter_condition iterator bound) body Sbreak.
Let increment := counter_increment iterator.
Let loop := counted_loop iterator bound body.
Let body_cont := Kloop1 header increment outside.
Let P := framed_protocol F temps ge fn body_cont locals.
Let E := framed_entry F temps ge fn body_cont locals.
Let V := framed_view F temps ge fn body_cont locals.
Let stride := framed_bound F + 5.

Inductive nested_cursor :=
| nl_start (input : temp_env * mem)
| nl_header (input : temp_env * mem)
| nl_body (c : cursor P) (ACTIVE : counter_active iterator bound (fst (V c)))
| nl_increment (input : temp_env * mem) (ACTIVE : counter_active iterator bound (fst input))
| nl_latch (input : temp_env * mem)
| nl_break (input : temp_env * mem)
| nl_done (input : temp_env * mem).
Definition nl_view c := match c with
  | nl_start input | nl_header input | nl_increment input _ | nl_latch input
  | nl_break input | nl_done input => input
  | nl_body c _ => V c end.
Definition nl_state c := match c with
  | nl_start input => State fn loop outside locals (fst input) (snd input)
  | nl_header input => State fn header body_cont locals (fst input) (snd input)
  | nl_body c _ => cursor_state P c
  | nl_increment input _ => State fn increment (Kloop2 header increment outside) locals (fst input) (snd input)
  | nl_latch input => State fn Sskip (Kloop2 header increment outside) locals (fst input) (snd input)
  | nl_break input => State fn Sbreak body_cont locals (fst input) (snd input)
  | nl_done input => State fn Sskip outside locals (fst input) (snd input) end.
Definition nl_rank c := match c with
  | nl_start input => counter_remaining iterator bound (fst input) * stride + 3
  | nl_header input => counter_remaining iterator bound (fst input) * stride + 2
  | nl_body c _ => Nat.pred (counter_remaining iterator bound (fst (V c))) * stride + cursor_rank P c + 6
  | nl_increment input _ => Nat.pred (counter_remaining iterator bound (fst input)) * stride + 5
  | nl_latch input => counter_remaining iterator bound (fst input) * stride + 4
  | nl_break _ => 1 | nl_done _ => 0 end.
Definition nl_done_result c := match c with nl_done input => Some input | _ => None end.

Inductive nl_step : nested_cursor -> nested_cursor -> Prop :=
| nl_step_start input : nl_step (nl_start input) (nl_header input)
| nl_step_true input ACTIVE : expression_test (counter_condition iterator bound)
    (Entry ge locals (fst input) (snd input)) true ->
    nl_step (nl_header input) (nl_body (begin_cursor E input) ACTIVE)
| nl_step_false input : expression_test (counter_condition iterator bound)
    (Entry ge locals (fst input) (snd input)) false -> nl_step (nl_header input) (nl_break input)
| nl_step_body c next ACTIVE ACTIVE' : cursor_step P c next ->
    nl_step (nl_body c ACTIVE) (nl_body next ACTIVE')
| nl_step_body_done c result ACTIVE ACTIVE' : cursor_done P c = Some result ->
    nl_step (nl_body c ACTIVE) (nl_increment result ACTIVE')
| nl_step_increment input ACTIVE : nl_step (nl_increment input ACTIVE)
    (nl_latch (increment_temps iterator (fst input), snd input))
| nl_step_latch input : nl_step (nl_latch input) (nl_start input)
| nl_step_break input : nl_step (nl_break input) (nl_done input).

Lemma nl_sound c next : nl_step c next -> adapter_step temps ge (nl_state c) E0 (nl_state next).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [nl_state].
  - constructor.
  - rewrite (begin_state E); destruct H as [v [EVAL BOOL]];
      eapply step_ifthenelse with (b := true); eauto.
  - destruct H as [v [EVAL BOOL]]; eapply step_ifthenelse with (b := false); eauto.
  - exact (cursor_step_sound P _ _ H).
  - rewrite (cursor_done_state P _ H); apply step_skip_or_continue_loop1; left; reflexivity.
  - destruct (@counter_increment_evaluation ge locals iterator bound (fst input) (snd input) ACTIVE)
      as [v [EVAL SET]]. rewrite <- SET; constructor; exact EVAL.
  - constructor.
  - constructor.
Qed.
Lemma nl_active c next : nl_step c next -> nl_done_result c = None.
Proof. intro MOVE; inversion MOVE; reflexivity. Qed.
Lemma nl_decreases c next : nl_step c next -> nl_rank next < nl_rank c.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [nl_rank]; try lia.
  - unfold V, E in *. rewrite framed_begin_view in *.
    pose proof (framed_begin_bound F temps ge fn body_cont locals input) as BOUND.
    pose proof (@counter_condition_active ge locals (fst input) (snd input) iterator bound H) as ACTIVE_INPUT.
    pose proof (@counter_active_positive iterator bound (fst input) ACTIVE_INPUT) as POS.
    unfold P, stride in *; destruct (counter_remaining iterator bound (fst input)); [lia|]; simpl; nia.
  - pose proof (framed_step_frame F temps ge fn body_cont locals _ _ H) as FRAME.
    pose proof (@counter_frame_distance iterator bound protected _ _ FRAME) as SAME.
    pose proof (cursor_step_decreases P _ _ H) as DEC.
    unfold V in *; rewrite SAME; lia.
  - pose proof (framed_done_view F temps ge fn body_cont locals _ H) as VIEW.
    pose proof (framed_done_rank F temps ge fn body_cont locals _ H) as RANK.
    unfold V, P in *; rewrite VIEW, RANK; lia.
  - rewrite (@counter_increment_distance iterator bound (fst input) DISTINCT ACTIVE); simpl; lia.
Qed.

Lemma nl_closed c events next_state : nl_done_result c = None ->
  adapter_step temps ge (nl_state c) events next_state ->
  exists next, events = E0 /\ next_state = nl_state next /\ nl_step c next.
Proof.
  destruct c as [input|input|c ACTIVE|input ACTIVE|input|input|input]; cbn [nl_state nl_done_result]; intros DONE STEP.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (nl_header input); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    assert (TEST : expression_test (counter_condition iterator bound)
      (Entry ge locals (fst input) (snd input)) b) by (eexists; split; eassumption).
    destruct b.
    + assert (ACTIVE : counter_active iterator bound (fst (V (begin_cursor E input)))).
      { unfold V, E; rewrite framed_begin_view; eapply counter_condition_active; exact TEST. }
      exists (nl_body (begin_cursor E input) ACTIVE); split; [reflexivity|split].
      * cbn [nl_state]; rewrite (begin_state E); reflexivity.
      * constructor; exact TEST.
    + exists (nl_break input); repeat split; auto; constructor; exact TEST.
  - destruct (cursor_done P c) as [result|] eqn:BODY_DONE.
    + rewrite (cursor_done_state P c BODY_DONE) in STEP.
      pose proof (framed_done_view F temps ge fn body_cont locals c BODY_DONE) as VIEW.
      assert (ACTIVE' : counter_active iterator bound (fst result)) by (unfold V in ACTIVE; rewrite VIEW in ACTIVE; exact ACTIVE).
      inversion STEP; subst; try contradiction;
        try match goal with BAD : is_call_cont (Kloop1 _ _ _) |- _ => contradiction end;
        try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
      exists (nl_increment (V c) ACTIVE); repeat split; auto; constructor; exact BODY_DONE.
    + destruct (cursor_step_closed P c _ _ BODY_DONE STEP) as [next [TRACE [STATE MOVE]]].
      assert (ACTIVE' : counter_active iterator bound (fst (V next))).
      { eapply counter_frame_active; [eapply framed_step_frame; exact MOVE|exact ACTIVE]. }
      exists (nl_body next ACTIVE'); repeat split; auto; constructor; exact MOVE.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    match goal with SOURCE : eval_expr _ _ _ _ _ _ |- _ => rename SOURCE into SOURCE_VALUE end.
    destruct (@counter_increment_evaluation ge locals iterator bound (fst input) (snd input) ACTIVE)
      as [v' [EVAL SET]].
    assert (PURE : pure_scalar (Ebinop Oadd (Etempvar iterator type_int32s)
      (Econst_int Int.one type_int32s) type_int32s)) by repeat constructor.
    match type of SOURCE_VALUE with eval_expr _ _ _ _ _ ?v =>
      pose proof (@pure_scalar_determinate _ PURE ge locals (fst input) (snd input) v v' SOURCE_VALUE EVAL);
      subst v
    end.
    exists (nl_latch (increment_temps iterator (fst input), snd input)); split; [reflexivity|split].
    + cbn [nl_state]; rewrite SET; reflexivity.
    + constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kloop2 _ _ _) |- _ => contradiction end.
    exists (nl_start input); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (nl_done input); repeat split; constructor.
  - discriminate DONE.
Qed.

Definition nl_run input result := exec_stmt (adapter_entry temps) ge locals (fst input) (snd input)
  loop E0 (fst result) (snd result) Out_normal.
Definition nl_tail input result := exists middle,
  exec_stmt (adapter_entry temps) ge locals (fst input) (snd input) increment E0
    (fst middle) (snd middle) Out_normal /\ nl_run middle result.
Definition nl_header_completion input result :=
  exec_stmt (adapter_entry temps) ge locals (fst input) (snd input) header E0
    (fst result) (snd result) Out_break \/ exists middle,
  exec_stmt (adapter_entry temps) ge locals (fst input) (snd input) header E0
    (fst middle) (snd middle) Out_normal /\ nl_tail middle result.
Definition nl_completion c result := match c with
  | nl_start input | nl_latch input => nl_run input result
  | nl_header input => nl_header_completion input result
  | nl_body c _ => exists middle, cursor_completion P c middle /\ nl_tail middle result
  | nl_increment input _ => nl_tail input result
  | nl_break input | nl_done input => result = input end.
Lemma nl_prepend c next result : nl_step c next -> nl_completion next result -> nl_completion c result.
Proof.
  intros MOVE RUN; inversion MOVE; subst; cbn [nl_completion] in RUN |- *.
  - destruct RUN as [STOP|[middle [HEADER [last [INC TAIL]]]]]; unfold nl_run.
    + eapply exec_Sloop_stop1 with (out' := Out_break); [exact STOP|constructor].
    + eapply exec_Sloop_loop with (out1 := Out_normal) (t1 := E0) (t2 := E0) (t3 := E0);
        [exact HEADER|constructor|exact INC|exact TAIL].
  - destruct RUN as [middle [BODY TAIL]]. right; exists middle; split; [|exact TAIL].
    destruct H as [v [EVAL BOOL]]. eapply exec_Sifthenelse with (b := true); eauto.
    apply (begin_completion E); exact BODY.
  - subst result; left; destruct H as [v [EVAL BOOL]]; eapply exec_Sifthenelse with (b := false); eauto; constructor.
  - destruct RUN as [middle [BODY TAIL]]. exists middle; split; [|exact TAIL].
    eapply cursor_completion_prepend; eauto.
  - exists result0; split; [eapply cursor_done_completion; exact H|exact RUN].
  - exists (increment_temps iterator (fst input), snd input); split;
      [apply counter_increment_normal with (bound := bound); exact ACTIVE|exact RUN].
  - exact RUN.
  - exact RUN.
Qed.
Lemma nl_done_state c result : nl_done_result c = Some result ->
  nl_state c = progress_exit_state fn outside locals result.
Proof. destruct c; cbn [nl_done_result]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.
Lemma nl_done_completion c result : nl_done_result c = Some result -> nl_completion c result.
Proof. destruct c; cbn [nl_done_result]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.
Definition nested_counted_protocol :=
  {| cursor := nested_cursor; cursor_state := nl_state; cursor_rank := nl_rank;
     cursor_done := nl_done_result; cursor_completion := nl_completion; cursor_step := nl_step;
     cursor_step_sound := nl_sound; cursor_step_active := nl_active;
     cursor_step_decreases := nl_decreases; cursor_step_closed := nl_closed;
     cursor_completion_prepend := nl_prepend; cursor_done_state := nl_done_state;
     cursor_done_completion := nl_done_completion |}.
Definition nested_counted_entry : protocol_entry nested_counted_protocol (temp_env * mem)
  (fun input => State fn loop outside locals (fst input) (snd input)) nl_run.
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (adapter_step temps ge)
    (progress_exit_state fn outside locals) nested_counted_protocol (temp_env * mem) _ _ nl_start _ _);
    intros; auto.
Defined.
Lemma nl_frame c next : nl_step c next ->
  preserves_temporaries protected (fst (nl_view c)) (fst (nl_view next)).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [nl_view]; try solve [intros id IN; reflexivity].
  - unfold V, E; rewrite framed_begin_view; intros id IN; reflexivity.
  - intros id IN. eapply framed_step_frame; [exact H|right; right; exact IN].
  - unfold V; rewrite (framed_done_view F temps ge fn body_cont locals _ H); intros id IN; reflexivity.
  - intros id IN; change ((increment_temps iterator (fst input)) ! id = (fst input) ! id).
    unfold increment_temps; destruct ((fst input) ! iterator) as [v|]; [destruct v|];
      try reflexivity. rewrite PTree.gso; [reflexivity|]. intro EQ; subst id; contradiction.
Qed.
End NESTED_LOOP.

Definition counted_framed_progress iterator bound (DISTINCT : iterator <> bound) protected
  (NOT_WRITTEN : ~ In iterator protected) body
  (F : framed_progress body (iterator :: bound :: protected)) :
  framed_progress (counted_loop iterator bound body) protected.
Proof.
  refine {| framed_quiet := _;
    framed_protocol := fun temps ge fn outside locals => @nested_counted_protocol iterator bound DISTINCT protected body F temps ge fn outside locals;
    framed_entry := fun temps ge fn outside locals => @nested_counted_entry iterator bound DISTINCT protected body F temps ge fn outside locals;
    framed_view := fun temps ge fn outside locals => @nl_view iterator bound protected body F temps ge fn outside locals;
    framed_bound := maximum_counter_distance * (framed_bound F + 5) + 3 |}.
  - unfold counted_loop, counter_increment; cbn [quiet_statement]; rewrite (framed_quiet F); reflexivity.
  - intros temps ge fn outside locals c; destruct c; cbn [cursor_state nested_counted_protocol nl_state nl_view];
      try (repeat eexists; reflexivity). apply (framed_shape F).
  - intros; reflexivity.
  - intros temps ge fn outside locals input; cbn [cursor_rank nested_counted_protocol begin_cursor nested_counted_entry nl_rank].
    pose proof (counter_distance_bounded iterator bound (fst input)); nia.
  - intros temps ge fn outside locals c result DONE; destruct c; cbn [cursor_done nested_counted_protocol nl_done_result] in DONE;
      try discriminate; reflexivity.
  - intros; apply nl_frame; [exact NOT_WRITTEN|assumption].
Defined.

Print Assumptions counted_framed_progress.
