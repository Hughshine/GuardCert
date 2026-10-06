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


(** Strict signed progress uses the machine maximum, independently of the
    tested bound's stability. Body protocols may include nested loops and
    setup statements, but must frame the outer iterator at every step. *)
Lemma strict_distance_bounded iterator le :
  (strict_remaining iterator le <= maximum_counter_distance)%nat.
Proof.
  unfold strict_remaining,maximum_counter_distance.
  destruct (le ! iterator) as [x|]; [destruct x|]; try lia.
  pose proof (Int.signed_range i); apply Z2Nat.inj_le; lia.
Qed.
Lemma strict_frame_distance iterator protected before after :
  preserves_temporaries (iterator::protected) before after ->
  strict_remaining iterator after = strict_remaining iterator before.
Proof. intro FRAME; unfold strict_remaining; rewrite (FRAME iterator (or_introl eq_refl)); reflexivity. Qed.
Lemma strict_frame_active iterator protected before after :
  preserves_temporaries (iterator::protected) before after ->
  strict_counter_active iterator before -> strict_counter_active iterator after.
Proof. intros FRAME [word [WORD RANGE]]; exists word; rewrite (FRAME iterator (or_introl eq_refl)); auto. Qed.


Section STRICT_NESTED_PROTOCOL.
Variable temps : bool.
Variable ge : genv.
Variable locals : env.
Variable fn : function.
Variable outside : cont.
Variable iterator : ident.
Variable condition : expr.
Hypothesis HEAD : forall le memory,
  expression_test condition (Entry ge locals le memory) true -> strict_counter_active iterator le.
Variable body : statement.
Variable protected : list ident.
Hypothesis NOT_WRITTEN : ~ In iterator protected.
Variable F : framed_progress body (iterator :: protected).
Local Open Scope nat_scope.


Definition sn_check := Sifthenelse condition Sskip Sbreak.
Definition sn_prelude := Ssequence Sskip sn_check.
Definition sn_header := Ssequence sn_prelude body.
Definition sn_increment := Ssequence Sskip (counter_increment iterator).
Definition sn_code := strict_frontend_loop iterator condition body.
Definition sn_stride := framed_bound F + 11.
Let body_cont := Kloop1 sn_header sn_increment outside.
Let P := framed_protocol F temps ge fn body_cont locals.
Let E := framed_entry F temps ge fn body_cont locals.
Let V := framed_view F temps ge fn body_cont locals.

Inductive strict_nested_cursor : Type :=
| sn_start (le : temp_env) (m : mem)
| sn_outer (le : temp_env) (m : mem)
| sn_inner (le : temp_env) (m : mem)
| sn_head_skip (le : temp_env) (m : mem)
| sn_condition (le : temp_env) (m : mem)
| sn_true_skip (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| sn_body (c : cursor P) (ACTIVE : strict_counter_active iterator (fst (V c)))
| sn_increment_seq (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| sn_increment_skip (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| sn_increment_set (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| sn_latch (le : temp_env) (m : mem)
| sn_break_seq (le : temp_env) (m : mem)
| sn_break (le : temp_env) (m : mem)
| sn_done (le : temp_env) (m : mem).

Definition strict_nested_cursor_state c : state :=
  match c with
  | sn_start le m => State fn sn_code outside locals le m
  | sn_outer le m => State fn sn_header (Kloop1 sn_header sn_increment outside) locals le m
  | sn_inner le m => State fn sn_prelude
      (Kseq body (Kloop1 sn_header sn_increment outside)) locals le m
  | sn_head_skip le m => State fn Sskip
      (Kseq sn_check (Kseq body (Kloop1 sn_header sn_increment outside))) locals le m
  | sn_condition le m => State fn sn_check
      (Kseq body (Kloop1 sn_header sn_increment outside)) locals le m
  | @sn_true_skip le m _ => State fn Sskip
      (Kseq body (Kloop1 sn_header sn_increment outside)) locals le m
  | @sn_body c _ => cursor_state P c
  | @sn_increment_seq le m _ => State fn sn_increment
      (Kloop2 sn_header sn_increment outside) locals le m
  | @sn_increment_skip le m _ => State fn Sskip
      (Kseq (counter_increment iterator) (Kloop2 sn_header sn_increment outside)) locals le m
  | @sn_increment_set le m _ => State fn (counter_increment iterator)
      (Kloop2 sn_header sn_increment outside) locals le m
  | sn_latch le m => State fn Sskip (Kloop2 sn_header sn_increment outside) locals le m
  | sn_break_seq le m => State fn Sbreak
      (Kseq body (Kloop1 sn_header sn_increment outside)) locals le m
  | sn_break le m => State fn Sbreak (Kloop1 sn_header sn_increment outside) locals le m
  | sn_done le m => State fn Sskip outside locals le m
  end.

Definition strict_nested_cursor_rank c : nat :=
  match c with
  | sn_start le _ => strict_remaining iterator le * sn_stride + 7
  | sn_outer le _ => strict_remaining iterator le * sn_stride + 6
  | sn_inner le _ => strict_remaining iterator le * sn_stride + 5
  | sn_head_skip le _ => strict_remaining iterator le * sn_stride + 4
  | sn_condition le _ => strict_remaining iterator le * sn_stride + 3
  | @sn_true_skip le _ _ => strict_remaining iterator le * sn_stride + 2
  | @sn_body c _ => Nat.pred (strict_remaining iterator (fst (V c))) * sn_stride +
      cursor_rank P c + 12
  | @sn_increment_seq le _ _ => Nat.pred (strict_remaining iterator le) * sn_stride + 11
  | @sn_increment_skip le _ _ => Nat.pred (strict_remaining iterator le) * sn_stride + 10
  | @sn_increment_set le _ _ => Nat.pred (strict_remaining iterator le) * sn_stride + 9
  | sn_latch le _ => strict_remaining iterator le * sn_stride + 8
  | sn_break_seq _ _ => 2
  | sn_break _ _ => 1
  | sn_done _ _ => 0
  end.

Definition strict_nested_cursor_done c : option (temp_env * mem) :=
  match c with sn_done le m => Some (le,m) | _ => None end.

Inductive strict_nested_cursor_step : strict_nested_cursor -> strict_nested_cursor -> Prop :=
| sn_step_start : forall le m, strict_nested_cursor_step (sn_start le m) (sn_outer le m)
| sn_step_outer : forall le m, strict_nested_cursor_step (sn_outer le m) (sn_inner le m)
| sn_step_inner : forall le m, strict_nested_cursor_step (sn_inner le m) (sn_head_skip le m)
| sn_step_head_skip : forall le m, strict_nested_cursor_step (sn_head_skip le m) (sn_condition le m)
| sn_step_true : forall le m ACTIVE,
    expression_test condition (Entry ge locals le m) true ->
    strict_nested_cursor_step (sn_condition le m) (@sn_true_skip le m ACTIVE)
| sn_step_false : forall le m,
    expression_test condition (Entry ge locals le m) false ->
    strict_nested_cursor_step (sn_condition le m) (sn_break_seq le m)
| sn_step_true_skip : forall le m ACTIVE ACTIVE',
    strict_nested_cursor_step (@sn_true_skip le m ACTIVE)
      (@sn_body (begin_cursor E (le,m)) ACTIVE')
| sn_step_body : forall c next ACTIVE ACTIVE', cursor_step P c next ->
    strict_nested_cursor_step (@sn_body c ACTIVE) (@sn_body next ACTIVE')
| sn_step_body_done : forall c result ACTIVE ACTIVE', cursor_done P c = Some result ->
    strict_nested_cursor_step (@sn_body c ACTIVE) (@sn_increment_seq (fst result) (snd result) ACTIVE')
| sn_step_increment_seq : forall le m ACTIVE,
    strict_nested_cursor_step (@sn_increment_seq le m ACTIVE) (@sn_increment_skip le m ACTIVE)
| sn_step_increment_skip : forall le m ACTIVE,
    strict_nested_cursor_step (@sn_increment_skip le m ACTIVE) (@sn_increment_set le m ACTIVE)
| sn_step_increment_set : forall le m ACTIVE,
    strict_nested_cursor_step (@sn_increment_set le m ACTIVE) (sn_latch (increment_temps iterator le) m)
| sn_step_latch : forall le m, strict_nested_cursor_step (sn_latch le m) (sn_start le m)
| sn_step_break_seq : forall le m, strict_nested_cursor_step (sn_break_seq le m) (sn_break le m)
| sn_step_break : forall le m, strict_nested_cursor_step (sn_break le m) (sn_done le m).

Lemma strict_nested_step_sound c n : strict_nested_cursor_step c n ->
  adapter_step temps ge (strict_nested_cursor_state c) E0 (strict_nested_cursor_state n).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [strict_nested_cursor_state].
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

Lemma strict_nested_step_active c n : strict_nested_cursor_step c n -> strict_nested_cursor_done c = None.
Proof. intro MOVE; inversion MOVE; reflexivity. Qed.

Lemma strict_nested_step_decreases c n : strict_nested_cursor_step c n ->
  strict_nested_cursor_rank n < strict_nested_cursor_rank c.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [strict_nested_cursor_rank]; try lia.
  - unfold V, E in *. rewrite framed_begin_view in *.
    pose proof (framed_begin_bound F temps ge fn body_cont locals (le,m)) as BOUND.
    pose proof (@strict_active_positive iterator le ACTIVE) as POS.
    unfold P, sn_stride in *; cbn [fst snd]; destruct (strict_remaining iterator le); [lia|]; simpl; nia.
  - pose proof (framed_step_frame F temps ge fn body_cont locals _ _ H) as FRAME.
    pose proof (@strict_frame_distance iterator protected _ _ FRAME) as SAME.
    pose proof (cursor_step_decreases P _ _ H) as DEC.
    unfold V in *; rewrite SAME; lia.
  - pose proof (framed_done_view F temps ge fn body_cont locals _ H) as VIEW.
    pose proof (framed_done_rank F temps ge fn body_cont locals _ H) as RANK.
    unfold V, P in *; rewrite VIEW, RANK; lia.
  - rewrite (@strict_increment_distance iterator le ACTIVE); simpl; lia.
Qed.

Lemma strict_nested_step_closed c events next_state : strict_nested_cursor_done c = None ->
  adapter_step temps ge (strict_nested_cursor_state c) events next_state ->
  exists n, events = E0 /\ next_state = strict_nested_cursor_state n /\ strict_nested_cursor_step c n.
Proof.
  destruct c; cbn [strict_nested_cursor_state strict_nested_cursor_done]; intros DONE STEP.
  - inversion STEP; subst; try discriminate;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sn_outer le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sn_inner le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sn_head_skip le m); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (sn_condition le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    assert (TEST : expression_test condition (Entry ge locals le m) b)
      by (eexists; split; eassumption).
    destruct b.
    + pose proof (@HEAD le m TEST) as ACTIVE.
      exists (@sn_true_skip le m ACTIVE); repeat split; auto. constructor; exact TEST.
    + exists (sn_break_seq le m); repeat split; auto. constructor; exact TEST.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    assert (ACTIVE' : strict_counter_active iterator (fst (V (begin_cursor E (le,m))))).
    { unfold V, E; rewrite framed_begin_view; exact ACTIVE. }
    exists (@sn_body (begin_cursor E (le,m)) ACTIVE'); split; [reflexivity|split].
    + cbn [strict_nested_cursor_state]; rewrite (begin_state E); reflexivity.
    + constructor.
  - destruct (cursor_done P c) as [result|] eqn:BODY_DONE.
    + rewrite (cursor_done_state P c BODY_DONE) in STEP.
      inversion STEP; subst; try contradiction;
        try match goal with BAD : is_call_cont (Kloop1 _ _ _) |- _ => contradiction end;
        try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
      pose proof (framed_done_view F temps ge fn body_cont locals c BODY_DONE) as VIEW.
      exists (@sn_increment_seq (fst (V c)) (snd (V c)) ACTIVE); split; [reflexivity|split].
      * cbn [strict_nested_cursor_state]; unfold V; rewrite VIEW; reflexivity.
      * rewrite <- VIEW in BODY_DONE. constructor; exact BODY_DONE.
    + destruct (cursor_step_closed P c _ _ BODY_DONE STEP) as [next [TRACE [STATE MOVE]]].
      assert (ACTIVE' : strict_counter_active iterator (fst (V next))).
      { eapply strict_frame_active; [eapply framed_step_frame; exact MOVE|exact ACTIVE]. }
      exists (@sn_body next ACTIVE'); repeat split; auto; constructor; exact MOVE.

  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (@sn_increment_skip le m ACTIVE); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (@sn_increment_set le m ACTIVE); repeat split; constructor.
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
    exists (sn_latch (increment_temps iterator le) m); split; [reflexivity|split].
    + cbn [strict_nested_cursor_state]; rewrite TEMPS; reflexivity.
    + constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kloop2 _ _ _) |- _ => contradiction end.
    exists (sn_start le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sn_break le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sn_done le m); repeat split; constructor.
  - discriminate DONE.
Qed.

Definition sn_run le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m sn_code E0 (fst result) (snd result) Out_normal.
Definition sn_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m sn_increment E0 le1 m1 Out_normal /\ sn_run le1 m1 result.
Definition sn_raw_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m (counter_increment iterator) E0 le1 m1 Out_normal /\ sn_run le1 m1 result.
Definition sn_body_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m body E0 le1 m1 Out_normal /\ sn_increment_tail le1 m1 result.
Definition sn_check_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m sn_check E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m sn_check E0 le1 m1 Out_normal /\ sn_body_tail le1 m1 result.
Definition sn_prelude_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m sn_prelude E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m sn_prelude E0 le1 m1 Out_normal /\ sn_body_tail le1 m1 result.
Definition sn_header_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt (adapter_entry temps) ge locals le m sn_header E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt (adapter_entry temps) ge locals le m sn_header E0 le1 m1 Out_normal /\ sn_increment_tail le1 m1 result.
Definition strict_nested_cursor_completion c (result : temp_env * mem) : Prop :=
  match c with
  | sn_start le m | sn_latch le m => sn_run le m result
  | sn_outer le m => sn_header_completion le m result
  | sn_inner le m => sn_prelude_completion le m result
  | sn_head_skip le m | sn_condition le m => sn_check_completion le m result
  | @sn_true_skip le m _ => sn_body_tail le m result
  | @sn_body c _ => exists middle,
      cursor_completion P c middle /\ sn_increment_tail (fst middle) (snd middle) result
  | @sn_increment_seq le m _ => sn_increment_tail le m result
  | @sn_increment_skip le m _ | @sn_increment_set le m _ => sn_raw_increment_tail le m result
  | sn_break_seq le m | sn_break le m | sn_done le m => result = (le,m)
  end.

Lemma strict_nested_completion_prepend c n result : strict_nested_cursor_step c n ->
  strict_nested_cursor_completion n result -> strict_nested_cursor_completion c result.
Proof.
  intros MOVE RUN; inversion MOVE; subst; cbn [strict_nested_cursor_completion] in RUN |- *.
  - destruct RUN as [STOP | [le1 [m1 [HEADER [le2 [m2 [INC TAIL]]]]]]]; unfold sn_run.
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

Definition strict_nested_exit_state (result : temp_env * mem) : state :=
  State fn Sskip outside locals (fst result) (snd result).
Lemma strict_nested_done_state c result : strict_nested_cursor_done c = Some result ->
  strict_nested_cursor_state c = strict_nested_exit_state result.
Proof. destruct c; cbn [strict_nested_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.
Lemma strict_nested_done_completion c result : strict_nested_cursor_done c = Some result ->
  strict_nested_cursor_completion c result.
Proof. destruct c; cbn [strict_nested_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.

Definition strict_nested_region_protocol :
  silent_protocol state event (temp_env * mem) (adapter_step temps ge) strict_nested_exit_state :=
  {| cursor := strict_nested_cursor; cursor_state := strict_nested_cursor_state;
     cursor_rank := strict_nested_cursor_rank; cursor_done := strict_nested_cursor_done;
     cursor_completion := strict_nested_cursor_completion; cursor_step := strict_nested_cursor_step;
     cursor_step_sound := strict_nested_step_sound; cursor_step_active := strict_nested_step_active;
     cursor_step_decreases := strict_nested_step_decreases; cursor_step_closed := strict_nested_step_closed;
     cursor_completion_prepend := strict_nested_completion_prepend;
     cursor_done_state := strict_nested_done_state; cursor_done_completion := strict_nested_done_completion |}.
Definition strict_nested_entry_state (input : temp_env * mem) : state :=
  State fn sn_code outside locals (fst input) (snd input).
Definition strict_nested_entry_result (input result : temp_env * mem) : Prop := sn_run (fst input) (snd input) result.
Definition strict_nested_region_entry : protocol_entry strict_nested_region_protocol
  (temp_env * mem) strict_nested_entry_state strict_nested_entry_result.
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (adapter_step temps ge) strict_nested_exit_state
    strict_nested_region_protocol (temp_env * mem) strict_nested_entry_state strict_nested_entry_result
    (fun input => sn_start (fst input) (snd input)) _ _); intros; auto.
Defined.
Definition sn_view c := match c with
  | sn_start le m | sn_outer le m | sn_inner le m | sn_head_skip le m | sn_condition le m
  | @sn_true_skip le m _ | @sn_increment_seq le m _ | @sn_increment_skip le m _
  | @sn_increment_set le m _ | sn_latch le m | sn_break_seq le m | sn_break le m | sn_done le m => (le,m)
  | @sn_body c _ => V c end.
Lemma sn_frame c next : strict_nested_cursor_step c next ->
  preserves_temporaries protected (fst (sn_view c)) (fst (sn_view next)).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [sn_view]; try solve [intros id IN; reflexivity].
  - unfold V, E; rewrite framed_begin_view; intros id IN; reflexivity.
  - intros id IN; eapply framed_step_frame; [exact H|right; exact IN].
  - unfold V; rewrite (framed_done_view F temps ge fn body_cont locals _ H); intros id IN; reflexivity.
  - intros id IN; change ((increment_temps iterator le) ! id = le ! id).
    unfold increment_temps; destruct (le ! iterator) as [v|]; [destruct v|]; try reflexivity.
    rewrite PTree.gso; [reflexivity|]. intro EQ; subst id; contradiction.
Qed.
End STRICT_NESTED_PROTOCOL.

Definition strict_nested_framed_progress iterator condition protected
  (NOT_WRITTEN : ~ In iterator protected) body
  (F : framed_progress body (iterator::protected))
  (HEAD : forall ge locals le memory,
    expression_test condition (Entry ge locals le memory) true -> strict_counter_active iterator le) :
  framed_progress (strict_frontend_loop iterator condition body) protected.
Proof.
  refine {| framed_quiet := _;
    framed_protocol := fun temps ge fn outside locals => @strict_nested_region_protocol temps ge locals fn outside iterator condition (HEAD ge locals) body protected F;
    framed_entry := fun temps ge fn outside locals => @strict_nested_region_entry temps ge locals fn outside iterator condition (HEAD ge locals) body protected F;
    framed_view := fun temps ge fn outside locals => @sn_view temps ge locals fn outside iterator condition body protected F;
    framed_bound := maximum_counter_distance * (framed_bound F + 11) + 7 |}.
  - unfold sn_code,strict_frontend_loop,counter_increment; cbn [quiet_statement]; rewrite (framed_quiet F); reflexivity.
  - intros temps ge fn outside locals c; destruct c;
      cbn [cursor_state strict_nested_region_protocol strict_nested_cursor_state sn_view];
      try (repeat eexists; reflexivity); apply (framed_shape F).
  - intros temps ge fn outside locals [le m]; reflexivity.
  - intros temps ge fn outside locals input.
    change (strict_remaining iterator (fst input) * (framed_bound F + 11) + 7 <=
      maximum_counter_distance * (framed_bound F + 11) + 7)%nat.
    pose proof (strict_distance_bounded iterator (fst input)); nia.
  - intros temps ge fn outside locals c result DONE; destruct c;
      cbn [cursor_done strict_nested_region_protocol strict_nested_cursor_done] in DONE;
      try discriminate; reflexivity.
  - intros; apply sn_frame; [exact NOT_WRITTEN|assumption].
Defined.
Definition strict_nested_region_progress iterator condition body
  (F : framed_progress body [iterator])
  (HEAD : forall ge locals le memory,
    expression_test condition (Entry ge locals le memory) true -> strict_counter_active iterator le) :
  region_progress (strict_frontend_loop iterator condition body).
Proof.
  apply (framed_region_progress (@strict_nested_framed_progress iterator condition [] (fun BAD => BAD) body F HEAD));
    intros; reflexivity.
Defined.
Print Assumptions strict_distance_bounded.
Print Assumptions strict_nested_framed_progress.
Print Assumptions strict_nested_region_progress.
