From Stdlib Require Import List Bool ZArith Arith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightGuard ClightFiniteRegion ClightCountedLoop
  ClightCondition ClightPureExpr ClightCountedProtocol ClightRegionProgress
  ClightFragmentProgress ClightSequenceProgress ClightNestedProgress ClightFrontendLoopProtocol.
Import ListNotations.
Set Implicit Arguments.


Section FRONTEND_LOOP_PROTOCOL.
Variable temps : bool.
Variable ge : genv.
Variable locals : env.
Variable fn : function.
Variable outside : cont.
Variable iterator bound : ident.
Hypothesis DISTINCT : iterator <> bound.
Variable body : statement.
Variable protected : list ident.
Hypothesis NOT_WRITTEN : ~ In iterator protected.
Variable F : framed_progress body (iterator :: bound :: protected).
Local Open Scope nat_scope.


Definition nf_check := Sifthenelse (counter_condition iterator bound) Sskip Sbreak.
Definition nf_prelude := Ssequence Sskip nf_check.
Definition nf_header := Ssequence nf_prelude body.
Definition nf_increment := Ssequence Sskip (counter_increment iterator).
Definition nf_code := frontend_counted_loop iterator bound body.
Definition nf_stride := framed_bound F + 11.
Let body_cont := Kloop1 nf_header nf_increment outside.
Let P := framed_protocol F temps ge fn body_cont locals.
Let E := framed_entry F temps ge fn body_cont locals.
Let V := framed_view F temps ge fn body_cont locals.

Inductive nested_frontend_cursor : Type :=
| nf_start (le : temp_env) (m : mem)
| nf_outer (le : temp_env) (m : mem)
| nf_inner (le : temp_env) (m : mem)
| nf_head_skip (le : temp_env) (m : mem)
| nf_condition (le : temp_env) (m : mem)
| nf_true_skip (le : temp_env) (m : mem) (ACTIVE : counter_active iterator bound le)
| nf_body (c : cursor P) (ACTIVE : counter_active iterator bound (fst (V c)))
| nf_increment_seq (le : temp_env) (m : mem) (ACTIVE : counter_active iterator bound le)
| nf_increment_skip (le : temp_env) (m : mem) (ACTIVE : counter_active iterator bound le)
| nf_increment_set (le : temp_env) (m : mem) (ACTIVE : counter_active iterator bound le)
| nf_latch (le : temp_env) (m : mem)
| nf_break_seq (le : temp_env) (m : mem)
| nf_break (le : temp_env) (m : mem)
| nf_done (le : temp_env) (m : mem).

Definition nested_frontend_cursor_state c : state :=
  match c with
  | nf_start le m => State fn nf_code outside locals le m
  | nf_outer le m => State fn nf_header (Kloop1 nf_header nf_increment outside) locals le m
  | nf_inner le m => State fn nf_prelude
      (Kseq body (Kloop1 nf_header nf_increment outside)) locals le m
  | nf_head_skip le m => State fn Sskip
      (Kseq nf_check (Kseq body (Kloop1 nf_header nf_increment outside))) locals le m
  | nf_condition le m => State fn nf_check
      (Kseq body (Kloop1 nf_header nf_increment outside)) locals le m
  | @nf_true_skip le m _ => State fn Sskip
      (Kseq body (Kloop1 nf_header nf_increment outside)) locals le m
  | @nf_body c _ => cursor_state P c
  | @nf_increment_seq le m _ => State fn nf_increment
      (Kloop2 nf_header nf_increment outside) locals le m
  | @nf_increment_skip le m _ => State fn Sskip
      (Kseq (counter_increment iterator) (Kloop2 nf_header nf_increment outside)) locals le m
  | @nf_increment_set le m _ => State fn (counter_increment iterator)
      (Kloop2 nf_header nf_increment outside) locals le m
  | nf_latch le m => State fn Sskip (Kloop2 nf_header nf_increment outside) locals le m
  | nf_break_seq le m => State fn Sbreak
      (Kseq body (Kloop1 nf_header nf_increment outside)) locals le m
  | nf_break le m => State fn Sbreak (Kloop1 nf_header nf_increment outside) locals le m
  | nf_done le m => State fn Sskip outside locals le m
  end.

Definition nested_frontend_cursor_rank c : nat :=
  match c with
  | nf_start le _ => counter_remaining iterator bound le * nf_stride + 7
  | nf_outer le _ => counter_remaining iterator bound le * nf_stride + 6
  | nf_inner le _ => counter_remaining iterator bound le * nf_stride + 5
  | nf_head_skip le _ => counter_remaining iterator bound le * nf_stride + 4
  | nf_condition le _ => counter_remaining iterator bound le * nf_stride + 3
  | @nf_true_skip le _ _ => counter_remaining iterator bound le * nf_stride + 2
  | @nf_body c _ => Nat.pred (counter_remaining iterator bound (fst (V c))) * nf_stride +
      cursor_rank P c + 12
  | @nf_increment_seq le _ _ => Nat.pred (counter_remaining iterator bound le) * nf_stride + 11
  | @nf_increment_skip le _ _ => Nat.pred (counter_remaining iterator bound le) * nf_stride + 10
  | @nf_increment_set le _ _ => Nat.pred (counter_remaining iterator bound le) * nf_stride + 9
  | nf_latch le _ => counter_remaining iterator bound le * nf_stride + 8
  | nf_break_seq _ _ => 2
  | nf_break _ _ => 1
  | nf_done _ _ => 0
  end.

Definition nested_frontend_cursor_done c : option (temp_env * mem) :=
  match c with nf_done le m => Some (le,m) | _ => None end.

Inductive nested_frontend_cursor_step : nested_frontend_cursor -> nested_frontend_cursor -> Prop :=
| nf_step_start : forall le m, nested_frontend_cursor_step (nf_start le m) (nf_outer le m)
| nf_step_outer : forall le m, nested_frontend_cursor_step (nf_outer le m) (nf_inner le m)
| nf_step_inner : forall le m, nested_frontend_cursor_step (nf_inner le m) (nf_head_skip le m)
| nf_step_head_skip : forall le m, nested_frontend_cursor_step (nf_head_skip le m) (nf_condition le m)
| nf_step_true : forall le m ACTIVE,
    expression_test (counter_condition iterator bound) (Entry ge locals le m) true ->
    nested_frontend_cursor_step (nf_condition le m) (@nf_true_skip le m ACTIVE)
| nf_step_false : forall le m,
    expression_test (counter_condition iterator bound) (Entry ge locals le m) false ->
    nested_frontend_cursor_step (nf_condition le m) (nf_break_seq le m)
| nf_step_true_skip : forall le m ACTIVE ACTIVE',
    nested_frontend_cursor_step (@nf_true_skip le m ACTIVE)
      (@nf_body (begin_cursor E (le,m)) ACTIVE')
| nf_step_body : forall c next ACTIVE ACTIVE', cursor_step P c next ->
    nested_frontend_cursor_step (@nf_body c ACTIVE) (@nf_body next ACTIVE')
| nf_step_body_done : forall c result ACTIVE ACTIVE', cursor_done P c = Some result ->
    nested_frontend_cursor_step (@nf_body c ACTIVE) (@nf_increment_seq (fst result) (snd result) ACTIVE')
| nf_step_increment_seq : forall le m ACTIVE,
    nested_frontend_cursor_step (@nf_increment_seq le m ACTIVE) (@nf_increment_skip le m ACTIVE)
| nf_step_increment_skip : forall le m ACTIVE,
    nested_frontend_cursor_step (@nf_increment_skip le m ACTIVE) (@nf_increment_set le m ACTIVE)
| nf_step_increment_set : forall le m ACTIVE,
    nested_frontend_cursor_step (@nf_increment_set le m ACTIVE) (nf_latch (increment_temps iterator le) m)
| nf_step_latch : forall le m, nested_frontend_cursor_step (nf_latch le m) (nf_start le m)
| nf_step_break_seq : forall le m, nested_frontend_cursor_step (nf_break_seq le m) (nf_break le m)
| nf_step_break : forall le m, nested_frontend_cursor_step (nf_break le m) (nf_done le m).

Lemma nested_frontend_step_sound c n : nested_frontend_cursor_step c n ->
  adapter_step temps ge (nested_frontend_cursor_state c) E0 (nested_frontend_cursor_state n).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [nested_frontend_cursor_state].
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct H as [v [EVAL BOOL]]. eapply step_ifthenelse with (b := true); eauto.
  - destruct H as [v [EVAL BOOL]]. eapply step_ifthenelse with (b := false); eauto.
  - rewrite (begin_state E); constructor.
  - exact (cursor_step_sound P _ _ H).
  - rewrite (cursor_done_state P _ H); apply step_skip_or_continue_loop1; left; reflexivity.
  - constructor.
  - constructor.
  - destruct (@counter_increment_evaluation ge locals iterator bound le m ACTIVE)
      as [v [EVAL TEMPS]]. rewrite <- TEMPS. constructor; exact EVAL.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma nested_frontend_step_active c n : nested_frontend_cursor_step c n -> nested_frontend_cursor_done c = None.
Proof. intro MOVE; inversion MOVE; reflexivity. Qed.

Lemma nested_frontend_step_decreases c n : nested_frontend_cursor_step c n ->
  nested_frontend_cursor_rank n < nested_frontend_cursor_rank c.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [nested_frontend_cursor_rank]; try lia.
  - unfold V, E in *. rewrite framed_begin_view in *.
    pose proof (framed_begin_bound F temps ge fn body_cont locals (le,m)) as BOUND.
    pose proof (@counter_active_positive iterator bound le ACTIVE) as POS.
    unfold P, nf_stride in *; cbn [fst snd]; destruct (counter_remaining iterator bound le); [lia|]; simpl; nia.
  - pose proof (framed_step_frame F temps ge fn body_cont locals _ _ H) as FRAME.
    pose proof (@counter_frame_distance iterator bound protected _ _ FRAME) as SAME.
    pose proof (cursor_step_decreases P _ _ H) as DEC.
    unfold V in *; rewrite SAME; lia.
  - pose proof (framed_done_view F temps ge fn body_cont locals _ H) as VIEW.
    pose proof (framed_done_rank F temps ge fn body_cont locals _ H) as RANK.
    unfold V, P in *; rewrite VIEW, RANK; lia.
  - rewrite (@counter_increment_distance iterator bound le DISTINCT ACTIVE); simpl; lia.
Qed.

Lemma nested_frontend_step_closed c events next_state : nested_frontend_cursor_done c = None ->
  adapter_step temps ge (nested_frontend_cursor_state c) events next_state ->
  exists n, events = E0 /\ next_state = nested_frontend_cursor_state n /\ nested_frontend_cursor_step c n.
Proof.
  destruct c; cbn [nested_frontend_cursor_state nested_frontend_cursor_done]; intros DONE STEP.
  - inversion STEP; subst; try discriminate;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (nf_outer le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (nf_inner le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (nf_head_skip le m); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (nf_condition le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    assert (TEST : expression_test (counter_condition iterator bound) (Entry ge locals le m) b)
      by (eexists; split; eassumption).
    destruct b.
    + pose proof (@counter_condition_active ge locals le m iterator bound TEST) as ACTIVE.
      exists (@nf_true_skip le m ACTIVE); repeat split; auto. constructor; exact TEST.
    + exists (nf_break_seq le m); repeat split; auto. constructor; exact TEST.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    assert (ACTIVE' : counter_active iterator bound (fst (V (begin_cursor E (le,m))))).
    { unfold V, E; rewrite framed_begin_view; exact ACTIVE. }
    exists (@nf_body (begin_cursor E (le,m)) ACTIVE'); split; [reflexivity|split].
    + cbn [nested_frontend_cursor_state]; rewrite (begin_state E); reflexivity.
    + constructor.
  - destruct (cursor_done P c) as [result|] eqn:BODY_DONE.
    + rewrite (cursor_done_state P c BODY_DONE) in STEP.
      inversion STEP; subst; try contradiction;
        try match goal with BAD : is_call_cont (Kloop1 _ _ _) |- _ => contradiction end;
        try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
      pose proof (framed_done_view F temps ge fn body_cont locals c BODY_DONE) as VIEW.
      exists (@nf_increment_seq (fst (V c)) (snd (V c)) ACTIVE); split; [reflexivity|split].
      * cbn [nested_frontend_cursor_state]; unfold V; rewrite VIEW; reflexivity.
      * rewrite <- VIEW in BODY_DONE. constructor; exact BODY_DONE.
    + destruct (cursor_step_closed P c _ _ BODY_DONE STEP) as [next [TRACE [STATE MOVE]]].
      assert (ACTIVE' : counter_active iterator bound (fst (V next))).
      { eapply counter_frame_active; [eapply framed_step_frame; exact MOVE|exact ACTIVE]. }
      exists (@nf_body next ACTIVE'); repeat split; auto; constructor; exact MOVE.

  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (@nf_increment_skip le m ACTIVE); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (@nf_increment_set le m ACTIVE); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    match goal with SOURCE : eval_expr _ _ _ _ _ _ |- _ => rename SOURCE into SOURCE_VALUE end.
    destruct (@counter_increment_evaluation ge locals iterator bound le m ACTIVE)
      as [v' [EVAL TEMPS]].
    assert (PURE : pure_scalar
      (Ebinop Oadd (Etempvar iterator type_int32s) (Econst_int Int.one type_int32s) type_int32s))
      by repeat constructor.
    match type of SOURCE_VALUE with eval_expr _ _ _ _ _ ?v =>
      pose proof (@pure_scalar_determinate _ PURE ge locals le m v v' SOURCE_VALUE EVAL) as VALUE;
      subst v
    end.
    exists (nf_latch (increment_temps iterator le) m); split; [reflexivity|split].
    + cbn [nested_frontend_cursor_state]; rewrite TEMPS; reflexivity.
    + constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kloop2 _ _ _) |- _ => contradiction end.
    exists (nf_start le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (nf_break le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (nf_done le m); repeat split; constructor.
  - discriminate DONE.
Qed.

Definition nf_run le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m nf_code E0 (fst result) (snd result) Out_normal.
Definition nf_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m nf_increment E0 le1 m1 Out_normal /\ nf_run le1 m1 result.
Definition nf_raw_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m (counter_increment iterator) E0 le1 m1 Out_normal /\ nf_run le1 m1 result.
Definition nf_body_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m body E0 le1 m1 Out_normal /\ nf_increment_tail le1 m1 result.
Definition nf_check_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m nf_check E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m nf_check E0 le1 m1 Out_normal /\ nf_body_tail le1 m1 result.
Definition nf_prelude_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m nf_prelude E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m nf_prelude E0 le1 m1 Out_normal /\ nf_body_tail le1 m1 result.
Definition nf_header_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m nf_header E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m nf_header E0 le1 m1 Out_normal /\ nf_increment_tail le1 m1 result.
Definition nested_frontend_cursor_completion c (result : temp_env * mem) : Prop :=
  match c with
  | nf_start le m | nf_latch le m => nf_run le m result
  | nf_outer le m => nf_header_completion le m result
  | nf_inner le m => nf_prelude_completion le m result
  | nf_head_skip le m | nf_condition le m => nf_check_completion le m result
  | @nf_true_skip le m _ => nf_body_tail le m result
  | @nf_body c _ => exists middle,
      cursor_completion P c middle /\ nf_increment_tail (fst middle) (snd middle) result
  | @nf_increment_seq le m _ => nf_increment_tail le m result
  | @nf_increment_skip le m _ | @nf_increment_set le m _ => nf_raw_increment_tail le m result
  | nf_break_seq le m | nf_break le m | nf_done le m => result = (le,m)
  end.

Lemma nested_frontend_completion_prepend c n result : nested_frontend_cursor_step c n ->
  nested_frontend_cursor_completion n result -> nested_frontend_cursor_completion c result.
Proof.
  intros MOVE RUN; inversion MOVE; subst; cbn [nested_frontend_cursor_completion] in RUN |- *.
  - destruct RUN as [STOP | [le1 [m1 [HEADER [le2 [m2 [INC TAIL]]]]]]]; unfold nf_run.
    + eapply exec_Sloop_stop1 with (out' := Out_break); [exact STOP|constructor].
    + eapply exec_Sloop_loop with (out1 := Out_normal) (t1 := E0) (t2 := E0) (t3 := E0);
        [exact HEADER|constructor|exact INC|exact TAIL].
  - destruct RUN as [STOP | [le1 [m1 [CHECK [le2 [m2 [BODY_RUN TAIL]]]]]]].
    + left. eapply exec_Sseq_2; [exact STOP|discriminate].
    + right. exists le2,m2; split; [|exact TAIL].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eauto.
  - destruct RUN as [STOP | [le1 [m1 [CHECK TAIL]]]].
    + left. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|exact STOP].
    + right. exists le1,m1; split; [|exact TAIL].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|exact CHECK].
  - exact RUN.
  - right. exists le,m; split; [|exact RUN].
    destruct H as [v [EVAL BOOL]]. eapply exec_Sifthenelse with (b := true); eauto. constructor.
  - subst result; left. destruct H as [v [EVAL BOOL]].
    eapply exec_Sifthenelse with (b := false); eauto. constructor.
  - destruct RUN as [[le1 m1] [RUN TAIL]]. exists le1,m1; split; [|exact TAIL].
    apply (begin_completion E) in RUN; exact RUN.
  - destruct RUN as [middle [RUN TAIL]]. exists middle; split; [|exact TAIL].
    eapply cursor_completion_prepend; eauto.
  - exists result0; split; [eapply cursor_done_completion; exact H|exact RUN].
  - destruct RUN as [le1 [m1 [INC TAIL]]]. exists le1,m1; split; [|exact TAIL].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|exact INC].
  - exact RUN.
  - exists (increment_temps iterator le),m; split;
      [apply counter_increment_normal with (bound := bound); exact ACTIVE|exact RUN].
  - exact RUN.
  - exact RUN.
  - exact RUN.
Qed.

Definition nested_frontend_exit_state (result : temp_env * mem) : state :=
  State fn Sskip outside locals (fst result) (snd result).
Lemma nested_frontend_done_state c result : nested_frontend_cursor_done c = Some result ->
  nested_frontend_cursor_state c = nested_frontend_exit_state result.
Proof. destruct c; cbn [nested_frontend_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.
Lemma nested_frontend_done_completion c result : nested_frontend_cursor_done c = Some result ->
  nested_frontend_cursor_completion c result.
Proof. destruct c; cbn [nested_frontend_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.

Definition nested_frontend_region_protocol :
  silent_protocol state event (temp_env * mem) (adapter_step temps ge) nested_frontend_exit_state :=
  {| cursor := nested_frontend_cursor; cursor_state := nested_frontend_cursor_state;
     cursor_rank := nested_frontend_cursor_rank; cursor_done := nested_frontend_cursor_done;
     cursor_completion := nested_frontend_cursor_completion; cursor_step := nested_frontend_cursor_step;
     cursor_step_sound := nested_frontend_step_sound; cursor_step_active := nested_frontend_step_active;
     cursor_step_decreases := nested_frontend_step_decreases; cursor_step_closed := nested_frontend_step_closed;
     cursor_completion_prepend := nested_frontend_completion_prepend;
     cursor_done_state := nested_frontend_done_state; cursor_done_completion := nested_frontend_done_completion |}.
Definition nested_frontend_entry_state (input : temp_env * mem) : state :=
  State fn nf_code outside locals (fst input) (snd input).
Definition nested_frontend_entry_result (input result : temp_env * mem) : Prop := nf_run (fst input) (snd input) result.
Definition nested_frontend_region_entry : protocol_entry nested_frontend_region_protocol
  (temp_env * mem) nested_frontend_entry_state nested_frontend_entry_result.
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (adapter_step temps ge) nested_frontend_exit_state
    nested_frontend_region_protocol (temp_env * mem) nested_frontend_entry_state nested_frontend_entry_result
    (fun input => nf_start (fst input) (snd input)) _ _); intros; auto.
Defined.
Definition nf_view c := match c with
  | nf_start le m | nf_outer le m | nf_inner le m | nf_head_skip le m | nf_condition le m
  | @nf_true_skip le m _ | @nf_increment_seq le m _ | @nf_increment_skip le m _
  | @nf_increment_set le m _ | nf_latch le m | nf_break_seq le m | nf_break le m | nf_done le m => (le,m)
  | @nf_body c _ => V c end.
Lemma nf_frame c next : nested_frontend_cursor_step c next ->
  preserves_temporaries protected (fst (nf_view c)) (fst (nf_view next)).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [nf_view]; try solve [intros id IN; reflexivity].
  - unfold V, E; rewrite framed_begin_view; intros id IN; reflexivity.
  - intros id IN; eapply framed_step_frame; [exact H|right; right; exact IN].
  - unfold V; rewrite (framed_done_view F temps ge fn body_cont locals _ H); intros id IN; reflexivity.
  - intros id IN; change ((increment_temps iterator le) ! id = le ! id).
    unfold increment_temps; destruct (le ! iterator) as [v|]; [destruct v|]; try reflexivity.
    rewrite PTree.gso; [reflexivity|]. intro EQ; subst id; contradiction.
Qed.
End FRONTEND_LOOP_PROTOCOL.

Definition frontend_framed_progress iterator bound (DISTINCT : iterator <> bound) protected
  (NOT_WRITTEN : ~ In iterator protected) body
  (F : framed_progress body (iterator :: bound :: protected)) :
  framed_progress (frontend_counted_loop iterator bound body) protected.
Proof.
  refine {| framed_quiet := _;
    framed_protocol := fun temps ge fn outside locals => @nested_frontend_region_protocol temps ge locals fn outside iterator bound DISTINCT body protected F;
    framed_entry := fun temps ge fn outside locals => @nested_frontend_region_entry temps ge locals fn outside iterator bound DISTINCT body protected F;
    framed_view := fun temps ge fn outside locals => @nf_view temps ge locals fn outside iterator bound body protected F;
    framed_bound := maximum_counter_distance * (framed_bound F + 11) + 7 |}.
  - unfold nf_code, frontend_counted_loop, counter_increment; cbn [quiet_statement]; rewrite (framed_quiet F); reflexivity.
  - intros temps ge fn outside locals c; destruct c; cbn [cursor_state nested_frontend_region_protocol nested_frontend_cursor_state nf_view];
      try (repeat eexists; reflexivity). apply (framed_shape F).
  - intros temps ge fn outside locals [le m]; reflexivity.
  - intros temps ge fn outside locals input.
    change (counter_remaining iterator bound (fst input) * (framed_bound F + 11) + 7 <=
      maximum_counter_distance * (framed_bound F + 11) + 7)%nat.
    pose proof (counter_distance_bounded iterator bound (fst input)); nia.
  - intros temps ge fn outside locals c result DONE; destruct c; cbn [cursor_done nested_frontend_region_protocol nested_frontend_cursor_done] in DONE;
      try discriminate; reflexivity.
  - intros; apply nf_frame; [exact NOT_WRITTEN|assumption].
Defined.
Definition frontend_nested_region_progress iterator bound (DISTINCT : iterator <> bound) protected
  (NOT_WRITTEN : ~ In iterator protected) body
  (F : framed_progress body (iterator :: bound :: protected)) :
  region_progress (frontend_counted_loop iterator bound body).
Proof.
  apply (framed_region_progress (@frontend_framed_progress iterator bound DISTINCT protected NOT_WRITTEN body F));
    intros; reflexivity.
Defined.
Print Assumptions frontend_framed_progress.
Print Assumptions frontend_nested_region_progress.
