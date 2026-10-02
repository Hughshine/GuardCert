From Stdlib Require Import List Bool ZArith Arith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightFiniteRegion ClightCountedLoop
  ClightCondition ClightPureExpr ClightCountedProtocol.
Import ListNotations.
Set Implicit Arguments.


(** Exact administrative shape produced by SimplExpr for a simple C for,
    followed by SimplLocals. No normalization is assumed. *)
Definition frontend_counted_loop iterator bound body :=
  Sloop (Ssequence (Ssequence Sskip
    (Sifthenelse (counter_condition iterator bound) Sskip Sbreak)) body)
    (Ssequence Sskip (counter_increment iterator)).

Section FRONTEND_LOOP_PROTOCOL.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable fn : function.
Variable outside : cont.
Variable iterator bound : ident.
Hypothesis DISTINCT : iterator <> bound.
Variable body : statement.
Hypothesis BODY : memory_body body = true.
Local Open Scope nat_scope.


Definition fl_check := Sifthenelse (counter_condition iterator bound) Sskip Sbreak.
Definition fl_prelude := Ssequence Sskip fl_check.
Definition fl_header := Ssequence fl_prelude body.
Definition fl_increment := Ssequence Sskip (counter_increment iterator).
Definition fl_code := frontend_counted_loop iterator bound body.
Definition fl_stride := statement_weight body + 11.

Inductive frontend_cursor : Type :=
| fl_start (le : temp_env) (m : mem)
| fl_outer (le : temp_env) (m : mem)
| fl_inner (le : temp_env) (m : mem)
| fl_head_skip (le : temp_env) (m : mem)
| fl_condition (le : temp_env) (m : mem)
| fl_true_skip (le : temp_env) (m : mem) (ACTIVE : counter_active iterator bound le)
| fl_body (code : statement) (stack : list statement) (le : temp_env) (m : mem)
    (CODE : memory_body code = true)
    (STACK : Forall (fun s => memory_body s = true) stack)
    (ACTIVE : counter_active iterator bound le)
| fl_increment_seq (le : temp_env) (m : mem) (ACTIVE : counter_active iterator bound le)
| fl_increment_skip (le : temp_env) (m : mem) (ACTIVE : counter_active iterator bound le)
| fl_increment_set (le : temp_env) (m : mem) (ACTIVE : counter_active iterator bound le)
| fl_latch (le : temp_env) (m : mem)
| fl_break_seq (le : temp_env) (m : mem)
| fl_break (le : temp_env) (m : mem)
| fl_done (le : temp_env) (m : mem).

Definition frontend_cursor_state c : state :=
  match c with
  | fl_start le m => State fn fl_code outside locals le m
  | fl_outer le m => State fn fl_header (Kloop1 fl_header fl_increment outside) locals le m
  | fl_inner le m => State fn fl_prelude
      (Kseq body (Kloop1 fl_header fl_increment outside)) locals le m
  | fl_head_skip le m => State fn Sskip
      (Kseq fl_check (Kseq body (Kloop1 fl_header fl_increment outside))) locals le m
  | fl_condition le m => State fn fl_check
      (Kseq body (Kloop1 fl_header fl_increment outside)) locals le m
  | @fl_true_skip le m _ => State fn Sskip
      (Kseq body (Kloop1 fl_header fl_increment outside)) locals le m
  | @fl_body code stack le m _ _ _ =>
      State fn code (region_cont stack (Kloop1 fl_header fl_increment outside)) locals le m
  | @fl_increment_seq le m _ => State fn fl_increment
      (Kloop2 fl_header fl_increment outside) locals le m
  | @fl_increment_skip le m _ => State fn Sskip
      (Kseq (counter_increment iterator) (Kloop2 fl_header fl_increment outside)) locals le m
  | @fl_increment_set le m _ => State fn (counter_increment iterator)
      (Kloop2 fl_header fl_increment outside) locals le m
  | fl_latch le m => State fn Sskip (Kloop2 fl_header fl_increment outside) locals le m
  | fl_break_seq le m => State fn Sbreak
      (Kseq body (Kloop1 fl_header fl_increment outside)) locals le m
  | fl_break le m => State fn Sbreak (Kloop1 fl_header fl_increment outside) locals le m
  | fl_done le m => State fn Sskip outside locals le m
  end.

Definition frontend_cursor_rank c : nat :=
  match c with
  | fl_start le _ => counter_remaining iterator bound le * fl_stride + 7
  | fl_outer le _ => counter_remaining iterator bound le * fl_stride + 6
  | fl_inner le _ => counter_remaining iterator bound le * fl_stride + 5
  | fl_head_skip le _ => counter_remaining iterator bound le * fl_stride + 4
  | fl_condition le _ => counter_remaining iterator bound le * fl_stride + 3
  | @fl_true_skip le _ _ => counter_remaining iterator bound le * fl_stride + 2
  | @fl_body code stack le m _ _ _ =>
      Nat.pred (counter_remaining iterator bound le) * fl_stride +
        state_weight (State fn code (region_cont stack Kstop) locals le m) + 12
  | @fl_increment_seq le _ _ => Nat.pred (counter_remaining iterator bound le) * fl_stride + 11
  | @fl_increment_skip le _ _ => Nat.pred (counter_remaining iterator bound le) * fl_stride + 10
  | @fl_increment_set le _ _ => Nat.pred (counter_remaining iterator bound le) * fl_stride + 9
  | fl_latch le _ => counter_remaining iterator bound le * fl_stride + 8
  | fl_break_seq _ _ => 2
  | fl_break _ _ => 1
  | fl_done _ _ => 0
  end.

Definition frontend_cursor_done c : option (temp_env * mem) :=
  match c with fl_done le m => Some (le,m) | _ => None end.

Inductive frontend_cursor_step : frontend_cursor -> frontend_cursor -> Prop :=
| fl_step_start : forall le m, frontend_cursor_step (fl_start le m) (fl_outer le m)
| fl_step_outer : forall le m, frontend_cursor_step (fl_outer le m) (fl_inner le m)
| fl_step_inner : forall le m, frontend_cursor_step (fl_inner le m) (fl_head_skip le m)
| fl_step_head_skip : forall le m, frontend_cursor_step (fl_head_skip le m) (fl_condition le m)
| fl_step_true : forall le m ACTIVE,
    expression_test (counter_condition iterator bound) (Entry ge locals le m) true ->
    frontend_cursor_step (fl_condition le m) (@fl_true_skip le m ACTIVE)
| fl_step_false : forall le m,
    expression_test (counter_condition iterator bound) (Entry ge locals le m) false ->
    frontend_cursor_step (fl_condition le m) (fl_break_seq le m)
| fl_step_true_skip : forall le m ACTIVE,
    frontend_cursor_step (@fl_true_skip le m ACTIVE) (@fl_body body [] le m BODY (Forall_nil _) ACTIVE)
| fl_step_body : forall code stack le m code' stack' m' CODE STACK CODE' STACK' ACTIVE,
    fragment_step ge locals code stack le m code' stack' le m' ->
    frontend_cursor_step (@fl_body code stack le m CODE STACK ACTIVE)
      (@fl_body code' stack' le m' CODE' STACK' ACTIVE)
| fl_step_body_done : forall le m CODE STACK ACTIVE,
    frontend_cursor_step (@fl_body Sskip [] le m CODE STACK ACTIVE) (@fl_increment_seq le m ACTIVE)
| fl_step_increment_seq : forall le m ACTIVE,
    frontend_cursor_step (@fl_increment_seq le m ACTIVE) (@fl_increment_skip le m ACTIVE)
| fl_step_increment_skip : forall le m ACTIVE,
    frontend_cursor_step (@fl_increment_skip le m ACTIVE) (@fl_increment_set le m ACTIVE)
| fl_step_increment_set : forall le m ACTIVE,
    frontend_cursor_step (@fl_increment_set le m ACTIVE) (fl_latch (increment_temps iterator le) m)
| fl_step_latch : forall le m, frontend_cursor_step (fl_latch le m) (fl_start le m)
| fl_step_break_seq : forall le m, frontend_cursor_step (fl_break_seq le m) (fl_break le m)
| fl_step_break : forall le m, frontend_cursor_step (fl_break le m) (fl_done le m).

Lemma frontend_step_sound c n : frontend_cursor_step c n ->
  step ge (fe ge) (frontend_cursor_state c) E0 (frontend_cursor_state n).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [frontend_cursor_state].
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct H as [v [EVAL BOOL]]. eapply step_ifthenelse with (b := true); eauto.
  - destruct H as [v [EVAL BOOL]]. eapply step_ifthenelse with (b := false); eauto.
  - constructor.
  - inversion H; subst; try discriminate CODE; cbn [region_cont];
      [eapply step_assign | apply step_seq | apply step_skip_seq | eapply step_ifthenelse]; eauto.
  - apply step_skip_or_continue_loop1; left; reflexivity.
  - constructor.
  - constructor.
  - destruct (@counter_increment_evaluation ge locals iterator bound le m ACTIVE)
      as [v [EVAL TEMPS]]. rewrite <- TEMPS. constructor; exact EVAL.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma frontend_step_active c n : frontend_cursor_step c n -> frontend_cursor_done c = None.
Proof. intro MOVE; inversion MOVE; reflexivity. Qed.

Lemma frontend_step_decreases c n : frontend_cursor_step c n -> frontend_cursor_rank n < frontend_cursor_rank c.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [frontend_cursor_rank]; try lia.
  - pose proof (@counter_active_positive iterator bound le ACTIVE) as POS.
    unfold fl_stride; cbn [state_weight region_cont continuation_weight].
    destruct (counter_remaining iterator bound le); [lia|]. simpl; nia.
  - pose proof (@fragment_step_decreases ge locals code stack le m code' stack' le m' H fn Kstop).
    lia.
  - rewrite (@counter_increment_distance iterator bound le DISTINCT ACTIVE); simpl; lia.
Qed.

Lemma frontend_step_closed c events next_state : frontend_cursor_done c = None ->
  step ge (fe ge) (frontend_cursor_state c) events next_state ->
  exists n, events = E0 /\ next_state = frontend_cursor_state n /\ frontend_cursor_step c n.
Proof.
  destruct c; cbn [frontend_cursor_state frontend_cursor_done]; intros DONE STEP.
  - inversion STEP; subst; try discriminate;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (fl_outer le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (fl_inner le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (fl_head_skip le m); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (fl_condition le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    assert (TEST : expression_test (counter_condition iterator bound) (Entry ge locals le m) b)
      by (eexists; split; eassumption).
    destruct b.
    + pose proof (@counter_condition_active ge locals le m iterator bound TEST) as ACTIVE.
      exists (@fl_true_skip le m ACTIVE); repeat split; auto. constructor; exact TEST.
    + exists (fl_break_seq le m); repeat split; auto. constructor; exact TEST.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (@fl_body body [] le m BODY (Forall_nil _) ACTIVE); repeat split; constructor.
  - destruct code; try (exfalso; discriminate CODE).
    { destruct stack as [|next rest].
      * simpl in STEP. inversion STEP; subst; try contradiction;
          try match goal with BAD : is_call_cont (Kloop1 _ _ _) |- _ => contradiction end;
          try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
        exists (@fl_increment_seq le m ACTIVE); repeat split; try reflexivity.
        constructor.
      * assert (FIN : finite_statement Sskip = true) by reflexivity.
        assert (FSTACK : Forall (fun s => finite_statement s = true) (next :: rest))
          by (eapply Forall_impl; [intros s M; apply memory_body_finite; exact M | exact STACK]).
        assert (ACTIVE_STACK : Sskip <> Sskip \/ (next :: rest) <> [])
          by (right; discriminate).
        destruct (@fragment_step_from_ambient fe ge locals fn Sskip (next :: rest)
          (Kloop1 fl_header fl_increment outside) le m events next_state FIN FSTACK
          ACTIVE_STACK STEP)
          as [code' [stack' [le' [m' [TRACE [STATE MOVE]]]]]].
        destruct (@memory_body_step ge locals Sskip (next :: rest) le m code' stack' le' m'
          MOVE CODE STACK) as [TEMPS [CODE' STACK']]; subst le'.
        exists (@fl_body code' stack' le m' CODE' STACK' ACTIVE); repeat split; auto.
        constructor; exact MOVE.
    }
    all: pose proof (memory_body_finite _ CODE) as FIN;
      assert (FSTACK : Forall (fun s => finite_statement s = true) stack)
        by (eapply Forall_impl; [intros s M; apply memory_body_finite; exact M | exact STACK]);
      match type of CODE with memory_body ?code = true =>
        assert (ACTIVE_CODE : code <> Sskip \/ stack <> []) by (left; discriminate)
      end;
      destruct (@fragment_step_from_ambient fe ge locals fn _ stack
        (Kloop1 fl_header fl_increment outside) le m events next_state FIN FSTACK
        ACTIVE_CODE STEP)
        as [code' [stack' [le' [m' [TRACE [STATE MOVE]]]]]];
      destruct (@memory_body_step ge locals _ stack le m code' stack' le' m' MOVE CODE STACK)
        as [TEMPS [CODE' STACK']]; subst le';
      exists (@fl_body code' stack' le m' CODE' STACK' ACTIVE); repeat split; auto;
      constructor; exact MOVE.

  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (@fl_increment_skip le m ACTIVE); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (@fl_increment_set le m ACTIVE); repeat split; constructor.
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
    exists (fl_latch (increment_temps iterator le) m); split; [reflexivity|split].
    + cbn [frontend_cursor_state]; rewrite TEMPS; reflexivity.
    + constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kloop2 _ _ _) |- _ => contradiction end.
    exists (fl_start le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (fl_break le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (fl_done le m); repeat split; constructor.
  - discriminate DONE.
Qed.

Definition fl_run le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m fl_code E0 (fst result) (snd result) Out_normal.
Definition fl_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt fe ge locals le m fl_increment E0 le1 m1 Out_normal /\ fl_run le1 m1 result.
Definition fl_raw_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt fe ge locals le m (counter_increment iterator) E0 le1 m1 Out_normal /\ fl_run le1 m1 result.
Definition fl_body_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt fe ge locals le m body E0 le1 m1 Out_normal /\ fl_increment_tail le1 m1 result.
Definition fl_check_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m fl_check E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt fe ge locals le m fl_check E0 le1 m1 Out_normal /\ fl_body_tail le1 m1 result.
Definition fl_prelude_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m fl_prelude E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt fe ge locals le m fl_prelude E0 le1 m1 Out_normal /\ fl_body_tail le1 m1 result.
Definition fl_header_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m fl_header E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt fe ge locals le m fl_header E0 le1 m1 Out_normal /\ fl_increment_tail le1 m1 result.
Definition frontend_cursor_completion c (result : temp_env * mem) : Prop :=
  match c with
  | fl_start le m | fl_latch le m => fl_run le m result
  | fl_outer le m => fl_header_completion le m result
  | fl_inner le m => fl_prelude_completion le m result
  | fl_head_skip le m | fl_condition le m => fl_check_completion le m result
  | @fl_true_skip le m _ => fl_body_tail le m result
  | @fl_body code stack le m _ _ _ => exists le1 m1,
      resumed_execution fe ge locals code stack le m le1 m1 /\ fl_increment_tail le1 m1 result
  | @fl_increment_seq le m _ => fl_increment_tail le m result
  | @fl_increment_skip le m _ | @fl_increment_set le m _ => fl_raw_increment_tail le m result
  | fl_break_seq le m | fl_break le m | fl_done le m => result = (le,m)
  end.

Lemma frontend_completion_prepend c n result : frontend_cursor_step c n ->
  frontend_cursor_completion n result -> frontend_cursor_completion c result.
Proof.
  intros MOVE RUN; inversion MOVE; subst; cbn [frontend_cursor_completion] in RUN |- *.
  - destruct RUN as [STOP | [le1 [m1 [HEADER [le2 [m2 [INC TAIL]]]]]]]; unfold fl_run.
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
  - destruct RUN as [le1 [m1 [RUN TAIL]]]. exists le1,m1; split; [|exact TAIL].
    apply initial_execution in RUN; exact RUN.
  - destruct RUN as [le1 [m1 [RUN TAIL]]]. exists le1,m1; split; [|exact TAIL].
    eapply fragment_step_prepend; eauto.
  - exists le,m; split; [apply completed_execution|exact RUN].
  - destruct RUN as [le1 [m1 [INC TAIL]]]. exists le1,m1; split; [|exact TAIL].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [constructor|exact INC].
  - exact RUN.
  - exists (increment_temps iterator le),m; split;
      [apply counter_increment_normal with (bound := bound); exact ACTIVE|exact RUN].
  - exact RUN.
  - exact RUN.
  - exact RUN.
Qed.

Definition frontend_exit_state (result : temp_env * mem) : state :=
  State fn Sskip outside locals (fst result) (snd result).
Lemma frontend_done_state c result : frontend_cursor_done c = Some result ->
  frontend_cursor_state c = frontend_exit_state result.
Proof. destruct c; cbn [frontend_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.
Lemma frontend_done_completion c result : frontend_cursor_done c = Some result ->
  frontend_cursor_completion c result.
Proof. destruct c; cbn [frontend_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.

Definition frontend_region_protocol :
  silent_protocol state event (temp_env * mem) (step ge (fe ge)) frontend_exit_state :=
  {| cursor := frontend_cursor; cursor_state := frontend_cursor_state;
     cursor_rank := frontend_cursor_rank; cursor_done := frontend_cursor_done;
     cursor_completion := frontend_cursor_completion; cursor_step := frontend_cursor_step;
     cursor_step_sound := frontend_step_sound; cursor_step_active := frontend_step_active;
     cursor_step_decreases := frontend_step_decreases; cursor_step_closed := frontend_step_closed;
     cursor_completion_prepend := frontend_completion_prepend;
     cursor_done_state := frontend_done_state; cursor_done_completion := frontend_done_completion |}.
Definition frontend_entry_state (input : temp_env * mem) : state :=
  State fn fl_code outside locals (fst input) (snd input).
Definition frontend_entry_result (input result : temp_env * mem) : Prop := fl_run (fst input) (snd input) result.
Definition frontend_region_entry : protocol_entry frontend_region_protocol
  (temp_env * mem) frontend_entry_state frontend_entry_result.
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (step ge (fe ge)) frontend_exit_state
    frontend_region_protocol (temp_env * mem) frontend_entry_state frontend_entry_result
    (fun input => fl_start (fst input) (snd input)) _ _); intros; auto.
Defined.
Theorem frontend_region_cannot_diverge c : ~ cursor_infinite frontend_region_protocol c.
Proof. apply cursor_cannot_diverge. Qed.
Theorem frontend_region_completed input length final result :
  cursor_path frontend_region_protocol (fl_start (fst input) (snd input)) length final ->
  frontend_cursor_done final = Some result ->
  exec_stmt fe ge locals (fst input) (snd input) fl_code E0 (fst result) (snd result) Out_normal /\
  length <= counter_remaining iterator bound (fst input) * fl_stride + 7.
Proof. apply (completed_entry frontend_region_entry). Qed.
End FRONTEND_LOOP_PROTOCOL.
Print Assumptions frontend_step_closed.
Print Assumptions frontend_region_completed.
