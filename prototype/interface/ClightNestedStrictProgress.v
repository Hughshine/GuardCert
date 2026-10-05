From Stdlib Require Import List Bool ZArith Arith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightGuard ClightFiniteRegion ClightCountedLoop
  ClightCondition ClightPureExpr ClightCountedProtocol ClightRegionProgress
  ClightFragmentProgress ClightSequenceProgress ClightNestedProgress ClightFrontendLoopProtocol.
From GuardInterface Require Import ClightStrictLoopProgress.
Import ListNotations.
Set Implicit Arguments.


(** The body may contain its own certified loops and may change memory.
    Only the outer iterator is protected; no load-stability assumption is
    needed to rule out silent divergence of the source. *)
Lemma strict_distance_bounded iterator le :
  (strict_remaining iterator le <= maximum_counter_distance)%nat.
Proof.
  unfold strict_remaining, maximum_counter_distance.
  destruct (le ! iterator) as [word|]; [destruct word|]; try lia.
  apply Z2Nat.inj_le; pose proof (Int.signed_range i); lia.
Qed.
Lemma strict_frame_distance iterator protected before after :
  preserves_temporaries (iterator :: protected) before after ->
  strict_remaining iterator after = strict_remaining iterator before.
Proof. intro FRAME; unfold strict_remaining; rewrite (FRAME iterator (or_introl eq_refl)); reflexivity. Qed.
Lemma strict_frame_active iterator protected before after :
  preserves_temporaries (iterator :: protected) before after ->
  strict_counter_active iterator before -> strict_counter_active iterator after.
Proof. intros FRAME [word [LOOK RANGE]]; exists word; rewrite (FRAME iterator (or_introl eq_refl)); auto. Qed.

Section FRONTEND_LOOP_PROTOCOL.
Variable temps : bool.
Variable ge : genv.
Variable locals : env.
Variable fn : function.
Variable outside : cont.
Variable iterator : ident.
Variable condition : expr.
Hypothesis HEAD : forall le memory, expression_test condition (Entry ge locals le memory) true ->
  strict_counter_active iterator le.
Variable body : statement.
Variable protected : list ident.
Hypothesis NOT_WRITTEN : ~ In iterator protected.
Variable F : framed_progress body (iterator :: protected).
Local Open Scope nat_scope.


Definition ns_check := Sifthenelse condition Sskip Sbreak.
Definition ns_prelude := Ssequence Sskip ns_check.
Definition ns_header := Ssequence ns_prelude body.
Definition ns_increment := Ssequence Sskip (counter_increment iterator).
Definition ns_code := strict_frontend_loop iterator condition body.
Definition ns_stride := framed_bound F + 11.
Let body_cont := Kloop1 ns_header ns_increment outside.
Let P := framed_protocol F temps ge fn body_cont locals.
Let E := framed_entry F temps ge fn body_cont locals.
Let V := framed_view F temps ge fn body_cont locals.

Inductive nested_strict_cursor : Type :=
| ns_start (le : temp_env) (m : mem)
| ns_outer (le : temp_env) (m : mem)
| ns_inner (le : temp_env) (m : mem)
| ns_head_skip (le : temp_env) (m : mem)
| ns_condition (le : temp_env) (m : mem)
| ns_true_skip (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| ns_body (c : cursor P) (ACTIVE : strict_counter_active iterator (fst (V c)))
| ns_increment_seq (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| ns_increment_skip (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| ns_increment_set (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| ns_latch (le : temp_env) (m : mem)
| ns_break_seq (le : temp_env) (m : mem)
| ns_break (le : temp_env) (m : mem)
| ns_done (le : temp_env) (m : mem).

Definition nested_strict_cursor_state c : state :=
  match c with
  | ns_start le m => State fn ns_code outside locals le m
  | ns_outer le m => State fn ns_header (Kloop1 ns_header ns_increment outside) locals le m
  | ns_inner le m => State fn ns_prelude
      (Kseq body (Kloop1 ns_header ns_increment outside)) locals le m
  | ns_head_skip le m => State fn Sskip
      (Kseq ns_check (Kseq body (Kloop1 ns_header ns_increment outside))) locals le m
  | ns_condition le m => State fn ns_check
      (Kseq body (Kloop1 ns_header ns_increment outside)) locals le m
  | @ns_true_skip le m _ => State fn Sskip
      (Kseq body (Kloop1 ns_header ns_increment outside)) locals le m
  | @ns_body c _ => cursor_state P c
  | @ns_increment_seq le m _ => State fn ns_increment
      (Kloop2 ns_header ns_increment outside) locals le m
  | @ns_increment_skip le m _ => State fn Sskip
      (Kseq (counter_increment iterator) (Kloop2 ns_header ns_increment outside)) locals le m
  | @ns_increment_set le m _ => State fn (counter_increment iterator)
      (Kloop2 ns_header ns_increment outside) locals le m
  | ns_latch le m => State fn Sskip (Kloop2 ns_header ns_increment outside) locals le m
  | ns_break_seq le m => State fn Sbreak
      (Kseq body (Kloop1 ns_header ns_increment outside)) locals le m
  | ns_break le m => State fn Sbreak (Kloop1 ns_header ns_increment outside) locals le m
  | ns_done le m => State fn Sskip outside locals le m
  end.

Definition nested_strict_cursor_rank c : nat :=
  match c with
  | ns_start le _ => strict_remaining iterator le * ns_stride + 7
  | ns_outer le _ => strict_remaining iterator le * ns_stride + 6
  | ns_inner le _ => strict_remaining iterator le * ns_stride + 5
  | ns_head_skip le _ => strict_remaining iterator le * ns_stride + 4
  | ns_condition le _ => strict_remaining iterator le * ns_stride + 3
  | @ns_true_skip le _ _ => strict_remaining iterator le * ns_stride + 2
  | @ns_body c _ => Nat.pred (strict_remaining iterator (fst (V c))) * ns_stride +
      cursor_rank P c + 12
  | @ns_increment_seq le _ _ => Nat.pred (strict_remaining iterator le) * ns_stride + 11
  | @ns_increment_skip le _ _ => Nat.pred (strict_remaining iterator le) * ns_stride + 10
  | @ns_increment_set le _ _ => Nat.pred (strict_remaining iterator le) * ns_stride + 9
  | ns_latch le _ => strict_remaining iterator le * ns_stride + 8
  | ns_break_seq _ _ => 2
  | ns_break _ _ => 1
  | ns_done _ _ => 0
  end.

Definition nested_strict_cursor_done c : option (temp_env * mem) :=
  match c with ns_done le m => Some (le,m) | _ => None end.

Inductive nested_strict_cursor_step : nested_strict_cursor -> nested_strict_cursor -> Prop :=
| ns_step_start : forall le m, nested_strict_cursor_step (ns_start le m) (ns_outer le m)
| ns_step_outer : forall le m, nested_strict_cursor_step (ns_outer le m) (ns_inner le m)
| ns_step_inner : forall le m, nested_strict_cursor_step (ns_inner le m) (ns_head_skip le m)
| ns_step_head_skip : forall le m, nested_strict_cursor_step (ns_head_skip le m) (ns_condition le m)
| ns_step_true : forall le m ACTIVE,
    expression_test condition (Entry ge locals le m) true ->
    nested_strict_cursor_step (ns_condition le m) (@ns_true_skip le m ACTIVE)
| ns_step_false : forall le m,
    expression_test condition (Entry ge locals le m) false ->
    nested_strict_cursor_step (ns_condition le m) (ns_break_seq le m)
| ns_step_true_skip : forall le m ACTIVE ACTIVE',
    nested_strict_cursor_step (@ns_true_skip le m ACTIVE)
      (@ns_body (begin_cursor E (le,m)) ACTIVE')
| ns_step_body : forall c next ACTIVE ACTIVE', cursor_step P c next ->
    nested_strict_cursor_step (@ns_body c ACTIVE) (@ns_body next ACTIVE')
| ns_step_body_done : forall c result ACTIVE ACTIVE', cursor_done P c = Some result ->
    nested_strict_cursor_step (@ns_body c ACTIVE) (@ns_increment_seq (fst result) (snd result) ACTIVE')
| ns_step_increment_seq : forall le m ACTIVE,
    nested_strict_cursor_step (@ns_increment_seq le m ACTIVE) (@ns_increment_skip le m ACTIVE)
| ns_step_increment_skip : forall le m ACTIVE,
    nested_strict_cursor_step (@ns_increment_skip le m ACTIVE) (@ns_increment_set le m ACTIVE)
| ns_step_increment_set : forall le m ACTIVE,
    nested_strict_cursor_step (@ns_increment_set le m ACTIVE) (ns_latch (increment_temps iterator le) m)
| ns_step_latch : forall le m, nested_strict_cursor_step (ns_latch le m) (ns_start le m)
| ns_step_break_seq : forall le m, nested_strict_cursor_step (ns_break_seq le m) (ns_break le m)
| ns_step_break : forall le m, nested_strict_cursor_step (ns_break le m) (ns_done le m).

Lemma nested_strict_step_sound c n : nested_strict_cursor_step c n ->
  adapter_step temps ge (nested_strict_cursor_state c) E0 (nested_strict_cursor_state n).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [nested_strict_cursor_state].
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
  - destruct (@strict_increment_evaluation ge locals iterator le m ACTIVE)
      as [v [EVAL TEMPS]]. rewrite <- TEMPS. constructor; exact EVAL.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma nested_strict_step_active c n : nested_strict_cursor_step c n -> nested_strict_cursor_done c = None.
Proof. intro MOVE; inversion MOVE; reflexivity. Qed.

Lemma nested_strict_step_decreases c n : nested_strict_cursor_step c n ->
  nested_strict_cursor_rank n < nested_strict_cursor_rank c.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [nested_strict_cursor_rank]; try lia.
  - unfold V, E in *. rewrite framed_begin_view in *.
    pose proof (framed_begin_bound F temps ge fn body_cont locals (le,m)) as BOUND.
    pose proof (@strict_active_positive iterator le ACTIVE) as POS.
    unfold P, ns_stride in *; cbn [fst snd]; destruct (strict_remaining iterator le); [lia|]; simpl; nia.
  - pose proof (framed_step_frame F temps ge fn body_cont locals _ _ H) as FRAME.
    pose proof (@strict_frame_distance iterator protected _ _ FRAME) as SAME.
    pose proof (cursor_step_decreases P _ _ H) as DEC.
    unfold V in *; rewrite SAME; lia.
  - pose proof (framed_done_view F temps ge fn body_cont locals _ H) as VIEW.
    pose proof (framed_done_rank F temps ge fn body_cont locals _ H) as RANK.
    unfold V, P in *; rewrite VIEW, RANK; lia.
  - rewrite (@strict_increment_distance iterator le ACTIVE); simpl; lia.
Qed.

Lemma nested_strict_step_closed c events next_state : nested_strict_cursor_done c = None ->
  adapter_step temps ge (nested_strict_cursor_state c) events next_state ->
  exists n, events = E0 /\ next_state = nested_strict_cursor_state n /\ nested_strict_cursor_step c n.
Proof.
  destruct c; cbn [nested_strict_cursor_state nested_strict_cursor_done]; intros DONE STEP.
  - inversion STEP; subst; try discriminate;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (ns_outer le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (ns_inner le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (ns_head_skip le m); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (ns_condition le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    assert (TEST : expression_test condition (Entry ge locals le m) b)
      by (eexists; split; eassumption).
    destruct b.
    + pose proof (HEAD TEST) as ACTIVE.
      exists (@ns_true_skip le m ACTIVE); repeat split; auto. constructor; exact TEST.
    + exists (ns_break_seq le m); repeat split; auto. constructor; exact TEST.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    assert (ACTIVE' : strict_counter_active iterator (fst (V (begin_cursor E (le,m))))).
    { unfold V, E; rewrite framed_begin_view; exact ACTIVE. }
    exists (@ns_body (begin_cursor E (le,m)) ACTIVE'); split; [reflexivity|split].
    + cbn [nested_strict_cursor_state]; rewrite (begin_state E); reflexivity.
    + constructor.
  - destruct (cursor_done P c) as [result|] eqn:BODY_DONE.
    + rewrite (cursor_done_state P c BODY_DONE) in STEP.
      inversion STEP; subst; try contradiction;
        try match goal with BAD : is_call_cont (Kloop1 _ _ _) |- _ => contradiction end;
        try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
      pose proof (framed_done_view F temps ge fn body_cont locals c BODY_DONE) as VIEW.
      exists (@ns_increment_seq (fst (V c)) (snd (V c)) ACTIVE); split; [reflexivity|split].
      * cbn [nested_strict_cursor_state]; unfold V; rewrite VIEW; reflexivity.
      * rewrite <- VIEW in BODY_DONE. constructor; exact BODY_DONE.
    + destruct (cursor_step_closed P c _ _ BODY_DONE STEP) as [next [TRACE [STATE MOVE]]].
      assert (ACTIVE' : strict_counter_active iterator (fst (V next))).
      { eapply strict_frame_active; [eapply framed_step_frame; exact MOVE|exact ACTIVE]. }
      exists (@ns_body next ACTIVE'); repeat split; auto; constructor; exact MOVE.

  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (@ns_increment_skip le m ACTIVE); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (@ns_increment_set le m ACTIVE); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    match goal with SOURCE : eval_expr _ _ _ _ _ _ |- _ => rename SOURCE into SOURCE_VALUE end.
    destruct (@strict_increment_evaluation ge locals iterator le m ACTIVE)
      as [v' [EVAL TEMPS]].
    assert (PURE : pure_scalar
      (Ebinop Oadd (Etempvar iterator type_int32s) (Econst_int Int.one type_int32s) type_int32s))
      by repeat constructor.
    match type of SOURCE_VALUE with eval_expr _ _ _ _ _ ?v =>
      pose proof (@pure_scalar_determinate _ PURE ge locals le m v v' SOURCE_VALUE EVAL) as VALUE;
      subst v
    end.
    exists (ns_latch (increment_temps iterator le) m); split; [reflexivity|split].
    + cbn [nested_strict_cursor_state]; rewrite TEMPS; reflexivity.
    + constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kloop2 _ _ _) |- _ => contradiction end.
    exists (ns_start le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (ns_break le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (ns_done le m); repeat split; constructor.
  - discriminate DONE.
Qed.

Definition ns_run le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m ns_code E0 (fst result) (snd result) Out_normal.
Definition ns_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m ns_increment E0 le1 m1 Out_normal /\ ns_run le1 m1 result.
Definition ns_raw_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m (counter_increment iterator) E0 le1 m1 Out_normal /\ ns_run le1 m1 result.
Definition ns_body_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m body E0 le1 m1 Out_normal /\ ns_increment_tail le1 m1 result.
Definition ns_check_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m ns_check E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m ns_check E0 le1 m1 Out_normal /\ ns_body_tail le1 m1 result.
Definition ns_prelude_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m ns_prelude E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m ns_prelude E0 le1 m1 Out_normal /\ ns_body_tail le1 m1 result.
Definition ns_header_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m ns_header E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m ns_header E0 le1 m1 Out_normal /\ ns_increment_tail le1 m1 result.
Definition nested_strict_cursor_completion c (result : temp_env * mem) : Prop :=
  match c with
  | ns_start le m | ns_latch le m => ns_run le m result
  | ns_outer le m => ns_header_completion le m result
  | ns_inner le m => ns_prelude_completion le m result
  | ns_head_skip le m | ns_condition le m => ns_check_completion le m result
  | @ns_true_skip le m _ => ns_body_tail le m result
  | @ns_body c _ => exists middle,
      cursor_completion P c middle /\ ns_increment_tail (fst middle) (snd middle) result
  | @ns_increment_seq le m _ => ns_increment_tail le m result
  | @ns_increment_skip le m _ | @ns_increment_set le m _ => ns_raw_increment_tail le m result
  | ns_break_seq le m | ns_break le m | ns_done le m => result = (le,m)
  end.

Lemma nested_strict_completion_prepend c n result : nested_strict_cursor_step c n ->
  nested_strict_cursor_completion n result -> nested_strict_cursor_completion c result.
Proof.
  intros MOVE RUN; inversion MOVE; subst; cbn [nested_strict_cursor_completion] in RUN |- *.
  - destruct RUN as [STOP | [le1 [m1 [HEADER [le2 [m2 [INC TAIL]]]]]]]; unfold ns_run.
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
      [apply strict_increment_normal; exact ACTIVE|exact RUN].
  - exact RUN.
  - exact RUN.
  - exact RUN.
Qed.

Definition nested_strict_exit_state (result : temp_env * mem) : state :=
  State fn Sskip outside locals (fst result) (snd result).
Lemma nested_strict_done_state c result : nested_strict_cursor_done c = Some result ->
  nested_strict_cursor_state c = nested_strict_exit_state result.
Proof. destruct c; cbn [nested_strict_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.
Lemma nested_strict_done_completion c result : nested_strict_cursor_done c = Some result ->
  nested_strict_cursor_completion c result.
Proof. destruct c; cbn [nested_strict_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.

Definition nested_strict_region_protocol :
  silent_protocol state event (temp_env * mem) (adapter_step temps ge) nested_strict_exit_state :=
  {| cursor := nested_strict_cursor; cursor_state := nested_strict_cursor_state;
     cursor_rank := nested_strict_cursor_rank; cursor_done := nested_strict_cursor_done;
     cursor_completion := nested_strict_cursor_completion; cursor_step := nested_strict_cursor_step;
     cursor_step_sound := nested_strict_step_sound; cursor_step_active := nested_strict_step_active;
     cursor_step_decreases := nested_strict_step_decreases; cursor_step_closed := nested_strict_step_closed;
     cursor_completion_prepend := nested_strict_completion_prepend;
     cursor_done_state := nested_strict_done_state; cursor_done_completion := nested_strict_done_completion |}.
Definition nested_strict_entry_state (input : temp_env * mem) : state :=
  State fn ns_code outside locals (fst input) (snd input).
Definition nested_strict_entry_result (input result : temp_env * mem) : Prop := ns_run (fst input) (snd input) result.
Definition nested_strict_region_entry : protocol_entry nested_strict_region_protocol
  (temp_env * mem) nested_strict_entry_state nested_strict_entry_result.
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (adapter_step temps ge) nested_strict_exit_state
    nested_strict_region_protocol (temp_env * mem) nested_strict_entry_state nested_strict_entry_result
    (fun input => ns_start (fst input) (snd input)) _ _); intros; auto.
Defined.
Definition ns_view c := match c with
  | ns_start le m | ns_outer le m | ns_inner le m | ns_head_skip le m | ns_condition le m
  | @ns_true_skip le m _ | @ns_increment_seq le m _ | @ns_increment_skip le m _
  | @ns_increment_set le m _ | ns_latch le m | ns_break_seq le m | ns_break le m | ns_done le m => (le,m)
  | @ns_body c _ => V c end.
Lemma ns_frame c next : nested_strict_cursor_step c next ->
  preserves_temporaries protected (fst (ns_view c)) (fst (ns_view next)).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [ns_view]; try solve [intros id IN; reflexivity].
  - unfold V, E; rewrite framed_begin_view; intros id IN; reflexivity.
  - intros id IN; eapply framed_step_frame; [exact H|right; exact IN].
  - unfold V; rewrite (framed_done_view F temps ge fn body_cont locals _ H); intros id IN; reflexivity.
  - intros id IN; change ((increment_temps iterator le) ! id = le ! id).
    unfold increment_temps; destruct (le ! iterator) as [v|]; [destruct v|]; try reflexivity.
    rewrite PTree.gso; [reflexivity|]. intro EQ; subst id; contradiction.
Qed.
End FRONTEND_LOOP_PROTOCOL.

Definition strict_framed_progress iterator condition
  (HEAD : forall ge locals le memory, expression_test condition (Entry ge locals le memory) true ->
    strict_counter_active iterator le) protected
  (NOT_WRITTEN : ~ In iterator protected) body (F : framed_progress body (iterator :: protected)) :
  framed_progress (strict_frontend_loop iterator condition body) protected.
Proof.
  refine {| framed_quiet := _;
    framed_protocol := fun temps ge fn outside locals => @nested_strict_region_protocol temps ge locals fn outside iterator condition (HEAD ge locals) body protected F;
    framed_entry := fun temps ge fn outside locals => @nested_strict_region_entry temps ge locals fn outside iterator condition (HEAD ge locals) body protected F;
    framed_view := fun temps ge fn outside locals => @ns_view temps ge locals fn outside iterator condition body protected F;
    framed_bound := maximum_counter_distance * (framed_bound F + 11) + 7 |}.
  - unfold ns_code, strict_frontend_loop, counter_increment; cbn [quiet_statement]; rewrite (framed_quiet F); reflexivity.
  - intros temps ge fn outside locals c; destruct c; cbn [cursor_state nested_strict_region_protocol nested_strict_cursor_state ns_view];
      try (repeat eexists; reflexivity). apply (framed_shape F).
  - intros temps ge fn outside locals [le m]; reflexivity.
  - intros temps ge fn outside locals input.
    change (strict_remaining iterator (fst input) * (framed_bound F + 11) + 7 <=
      maximum_counter_distance * (framed_bound F + 11) + 7)%nat.
    pose proof (strict_distance_bounded iterator (fst input)); nia.
  - intros temps ge fn outside locals c result DONE; destruct c; cbn [cursor_done nested_strict_region_protocol nested_strict_cursor_done] in DONE;
      try discriminate; reflexivity.
  - intros; apply ns_frame; [exact NOT_WRITTEN|assumption].
Defined.
Definition strict_nested_region_progress iterator condition
  (HEAD : forall ge locals le memory, expression_test condition (Entry ge locals le memory) true ->
    strict_counter_active iterator le) protected
  (NOT_WRITTEN : ~ In iterator protected) body (F : framed_progress body (iterator :: protected)) :
  region_progress (strict_frontend_loop iterator condition body).
Proof.
  apply (framed_region_progress (@strict_framed_progress iterator condition HEAD protected NOT_WRITTEN body F));
    intros; reflexivity.
Defined.
Print Assumptions nested_strict_step_closed.
Print Assumptions strict_framed_progress.
Print Assumptions strict_nested_region_progress.
