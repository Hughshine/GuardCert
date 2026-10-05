From Stdlib Require Import List Bool ZArith Arith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightFiniteRegion ClightCountedLoop
  ClightGuard SemanticFacts ClightCondition ClightPureExpr ClightCountedProtocol ClightRegionProgress.
Import ListNotations.
Set Implicit Arguments.

(** A strict signed counter may compare with a memory-dependent bound. Its
    ranking function uses the machine maximum, never presumed load stability.
    Undefined accesses may get stuck; this protocol excludes silent divergence. *)
Definition strict_frontend_loop iterator condition body :=
  Sloop (Ssequence (Ssequence Sskip (Sifthenelse condition Sskip Sbreak)) body)
    (Ssequence Sskip (counter_increment iterator)).
Definition strict_counter_active iterator (le : temp_env) :=
  exists x, le ! iterator = Some (Vint x) /\ (Int.signed x < Int.max_signed)%Z.
Definition strict_remaining iterator (le : temp_env) : nat :=
  match le ! iterator with
  | Some (Vint x) => Z.to_nat (Int.max_signed - Int.signed x)
  | _ => 0
  end.
Lemma strict_active_positive iterator le : strict_counter_active iterator le ->
  (0 < strict_remaining iterator le)%nat.
Proof.
  intros [x [X LT]]; unfold strict_remaining; rewrite X.
  pose proof (Z2Nat.id (Int.max_signed - Int.signed x) ltac:(lia)); lia.
Qed.
Lemma strict_increment_distance iterator le : strict_counter_active iterator le ->
  strict_remaining iterator le = S (strict_remaining iterator (increment_temps iterator le)).
Proof.
  intros [x [X LT]]; unfold increment_temps, strict_remaining; rewrite X, PTree.gss, Int.add_signed.
  change (Int.signed Int.one) with 1%Z.
  rewrite Int.signed_repr by (pose proof (Int.signed_range x); lia).
  rewrite <- Z2Nat.inj_succ by lia; f_equal; lia.
Qed.
Lemma strict_increment_evaluation ge locals iterator le m : strict_counter_active iterator le ->
  exists v, eval_expr ge locals le m
    (Ebinop Oadd (Etempvar iterator type_int32s) (Econst_int Int.one type_int32s) type_int32s) v /\
    PTree.set iterator v le = increment_temps iterator le.
Proof.
  intros [x [X LT]]; exists (Vint (Int.add x Int.one)); split.
  - eapply eval_Ebinop; [constructor; exact X|constructor|reflexivity].
  - unfold increment_temps; rewrite X; reflexivity.
Qed.
Lemma strict_increment_normal fe ge locals iterator le m : strict_counter_active iterator le ->
  exec_stmt fe ge locals le m (counter_increment iterator) E0 (increment_temps iterator le) m Out_normal.
Proof.
  intro ACTIVE; destruct (@strict_increment_evaluation ge locals iterator le m ACTIVE) as [v [EVAL TEMPS]].
  rewrite <- TEMPS; constructor; exact EVAL.
Qed.

Section STRICT_LOOP_PROTOCOL.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable fn : function.
Variable outside : cont.
Variable iterator : ident.
Variable condition : expr.
Hypothesis HEAD : forall le m,
  expression_test condition (Entry ge locals le m) true -> strict_counter_active iterator le.
Variable body : statement.
Hypothesis BODY : memory_body body = true.
Local Open Scope nat_scope.


Definition sl_check := Sifthenelse condition Sskip Sbreak.
Definition sl_prelude := Ssequence Sskip sl_check.
Definition sl_header := Ssequence sl_prelude body.
Definition sl_increment := Ssequence Sskip (counter_increment iterator).
Definition sl_code := strict_frontend_loop iterator condition body.
Definition sl_stride := statement_weight body + 11.

Inductive strict_cursor : Type :=
| sl_start (le : temp_env) (m : mem)
| sl_outer (le : temp_env) (m : mem)
| sl_inner (le : temp_env) (m : mem)
| sl_head_skip (le : temp_env) (m : mem)
| sl_condition (le : temp_env) (m : mem)
| sl_true_skip (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| sl_body (code : statement) (stack : list statement) (le : temp_env) (m : mem)
    (CODE : memory_body code = true)
    (STACK : Forall (fun s => memory_body s = true) stack)
    (ACTIVE : strict_counter_active iterator le)
| sl_increment_seq (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| sl_increment_skip (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| sl_increment_set (le : temp_env) (m : mem) (ACTIVE : strict_counter_active iterator le)
| sl_latch (le : temp_env) (m : mem)
| sl_break_seq (le : temp_env) (m : mem)
| sl_break (le : temp_env) (m : mem)
| sl_done (le : temp_env) (m : mem).

Definition strict_cursor_state c : state :=
  match c with
  | sl_start le m => State fn sl_code outside locals le m
  | sl_outer le m => State fn sl_header (Kloop1 sl_header sl_increment outside) locals le m
  | sl_inner le m => State fn sl_prelude
      (Kseq body (Kloop1 sl_header sl_increment outside)) locals le m
  | sl_head_skip le m => State fn Sskip
      (Kseq sl_check (Kseq body (Kloop1 sl_header sl_increment outside))) locals le m
  | sl_condition le m => State fn sl_check
      (Kseq body (Kloop1 sl_header sl_increment outside)) locals le m
  | @sl_true_skip le m _ => State fn Sskip
      (Kseq body (Kloop1 sl_header sl_increment outside)) locals le m
  | @sl_body code stack le m _ _ _ =>
      State fn code (region_cont stack (Kloop1 sl_header sl_increment outside)) locals le m
  | @sl_increment_seq le m _ => State fn sl_increment
      (Kloop2 sl_header sl_increment outside) locals le m
  | @sl_increment_skip le m _ => State fn Sskip
      (Kseq (counter_increment iterator) (Kloop2 sl_header sl_increment outside)) locals le m
  | @sl_increment_set le m _ => State fn (counter_increment iterator)
      (Kloop2 sl_header sl_increment outside) locals le m
  | sl_latch le m => State fn Sskip (Kloop2 sl_header sl_increment outside) locals le m
  | sl_break_seq le m => State fn Sbreak
      (Kseq body (Kloop1 sl_header sl_increment outside)) locals le m
  | sl_break le m => State fn Sbreak (Kloop1 sl_header sl_increment outside) locals le m
  | sl_done le m => State fn Sskip outside locals le m
  end.

Definition strict_cursor_rank c : nat :=
  match c with
  | sl_start le _ => strict_remaining iterator le * sl_stride + 7
  | sl_outer le _ => strict_remaining iterator le * sl_stride + 6
  | sl_inner le _ => strict_remaining iterator le * sl_stride + 5
  | sl_head_skip le _ => strict_remaining iterator le * sl_stride + 4
  | sl_condition le _ => strict_remaining iterator le * sl_stride + 3
  | @sl_true_skip le _ _ => strict_remaining iterator le * sl_stride + 2
  | @sl_body code stack le m _ _ _ =>
      Nat.pred (strict_remaining iterator le) * sl_stride +
        state_weight (State fn code (region_cont stack Kstop) locals le m) + 12
  | @sl_increment_seq le _ _ => Nat.pred (strict_remaining iterator le) * sl_stride + 11
  | @sl_increment_skip le _ _ => Nat.pred (strict_remaining iterator le) * sl_stride + 10
  | @sl_increment_set le _ _ => Nat.pred (strict_remaining iterator le) * sl_stride + 9
  | sl_latch le _ => strict_remaining iterator le * sl_stride + 8
  | sl_break_seq _ _ => 2
  | sl_break _ _ => 1
  | sl_done _ _ => 0
  end.

Definition strict_cursor_done c : option (temp_env * mem) :=
  match c with sl_done le m => Some (le,m) | _ => None end.

Inductive strict_cursor_step : strict_cursor -> strict_cursor -> Prop :=
| sl_step_start : forall le m, strict_cursor_step (sl_start le m) (sl_outer le m)
| sl_step_outer : forall le m, strict_cursor_step (sl_outer le m) (sl_inner le m)
| sl_step_inner : forall le m, strict_cursor_step (sl_inner le m) (sl_head_skip le m)
| sl_step_head_skip : forall le m, strict_cursor_step (sl_head_skip le m) (sl_condition le m)
| sl_step_true : forall le m ACTIVE,
    expression_test condition (Entry ge locals le m) true ->
    strict_cursor_step (sl_condition le m) (@sl_true_skip le m ACTIVE)
| sl_step_false : forall le m,
    expression_test condition (Entry ge locals le m) false ->
    strict_cursor_step (sl_condition le m) (sl_break_seq le m)
| sl_step_true_skip : forall le m ACTIVE,
    strict_cursor_step (@sl_true_skip le m ACTIVE) (@sl_body body [] le m BODY (Forall_nil _) ACTIVE)
| sl_step_body : forall code stack le m code' stack' m' CODE STACK CODE' STACK' ACTIVE,
    fragment_step ge locals code stack le m code' stack' le m' ->
    strict_cursor_step (@sl_body code stack le m CODE STACK ACTIVE)
      (@sl_body code' stack' le m' CODE' STACK' ACTIVE)
| sl_step_body_done : forall le m CODE STACK ACTIVE,
    strict_cursor_step (@sl_body Sskip [] le m CODE STACK ACTIVE) (@sl_increment_seq le m ACTIVE)
| sl_step_increment_seq : forall le m ACTIVE,
    strict_cursor_step (@sl_increment_seq le m ACTIVE) (@sl_increment_skip le m ACTIVE)
| sl_step_increment_skip : forall le m ACTIVE,
    strict_cursor_step (@sl_increment_skip le m ACTIVE) (@sl_increment_set le m ACTIVE)
| sl_step_increment_set : forall le m ACTIVE,
    strict_cursor_step (@sl_increment_set le m ACTIVE) (sl_latch (increment_temps iterator le) m)
| sl_step_latch : forall le m, strict_cursor_step (sl_latch le m) (sl_start le m)
| sl_step_break_seq : forall le m, strict_cursor_step (sl_break_seq le m) (sl_break le m)
| sl_step_break : forall le m, strict_cursor_step (sl_break le m) (sl_done le m).

Lemma strict_step_sound c n : strict_cursor_step c n ->
  step ge (fe ge) (strict_cursor_state c) E0 (strict_cursor_state n).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [strict_cursor_state].
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
  - destruct (@strict_increment_evaluation ge locals iterator le m ACTIVE)
      as [v [EVAL TEMPS]]. rewrite <- TEMPS. constructor; exact EVAL.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma strict_step_active c n : strict_cursor_step c n -> strict_cursor_done c = None.
Proof. intro MOVE; inversion MOVE; reflexivity. Qed.

Lemma strict_step_decreases c n : strict_cursor_step c n -> strict_cursor_rank n < strict_cursor_rank c.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [strict_cursor_rank]; try lia.
  - pose proof (@strict_active_positive iterator le ACTIVE) as POS.
    unfold sl_stride; cbn [state_weight region_cont continuation_weight].
    destruct (strict_remaining iterator le); [lia|]. simpl; nia.
  - pose proof (@fragment_step_decreases ge locals code stack le m code' stack' le m' H fn Kstop).
    lia.
  - rewrite (@strict_increment_distance iterator le ACTIVE); simpl; lia.
Qed.

Lemma strict_step_closed c events next_state : strict_cursor_done c = None ->
  step ge (fe ge) (strict_cursor_state c) events next_state ->
  exists n, events = E0 /\ next_state = strict_cursor_state n /\ strict_cursor_step c n.
Proof.
  destruct c; cbn [strict_cursor_state strict_cursor_done]; intros DONE STEP.
  - inversion STEP; subst; try discriminate;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sl_outer le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sl_inner le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sl_head_skip le m); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (sl_condition le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    assert (TEST : expression_test condition (Entry ge locals le m) b)
      by (eexists; split; eassumption).
    destruct b.
    + pose proof (HEAD TEST) as ACTIVE.
      exists (@sl_true_skip le m ACTIVE); repeat split; auto. constructor; exact TEST.
    + exists (sl_break_seq le m); repeat split; auto. constructor; exact TEST.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (@sl_body body [] le m BODY (Forall_nil _) ACTIVE); repeat split; constructor.
  - destruct code; try (exfalso; discriminate CODE).
    { destruct stack as [|next rest].
      * simpl in STEP. inversion STEP; subst; try contradiction;
          try match goal with BAD : is_call_cont (Kloop1 _ _ _) |- _ => contradiction end;
          try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
        exists (@sl_increment_seq le m ACTIVE); repeat split; try reflexivity.
        constructor.
      * assert (FIN : finite_statement Sskip = true) by reflexivity.
        assert (FSTACK : Forall (fun s => finite_statement s = true) (next :: rest))
          by (eapply Forall_impl; [intros s M; apply memory_body_finite; exact M | exact STACK]).
        assert (ACTIVE_STACK : Sskip <> Sskip \/ (next :: rest) <> [])
          by (right; discriminate).
        destruct (@fragment_step_from_ambient fe ge locals fn Sskip (next :: rest)
          (Kloop1 sl_header sl_increment outside) le m events next_state FIN FSTACK
          ACTIVE_STACK STEP)
          as [code' [stack' [le' [m' [TRACE [STATE MOVE]]]]]].
        destruct (@memory_body_step ge locals Sskip (next :: rest) le m code' stack' le' m'
          MOVE CODE STACK) as [TEMPS [CODE' STACK']]; subst le'.
        exists (@sl_body code' stack' le m' CODE' STACK' ACTIVE); repeat split; auto.
        constructor; exact MOVE.
    }
    all: pose proof (memory_body_finite _ CODE) as FIN;
      assert (FSTACK : Forall (fun s => finite_statement s = true) stack)
        by (eapply Forall_impl; [intros s M; apply memory_body_finite; exact M | exact STACK]);
      match type of CODE with memory_body ?code = true =>
        assert (ACTIVE_CODE : code <> Sskip \/ stack <> []) by (left; discriminate)
      end;
      destruct (@fragment_step_from_ambient fe ge locals fn _ stack
        (Kloop1 sl_header sl_increment outside) le m events next_state FIN FSTACK
        ACTIVE_CODE STEP)
        as [code' [stack' [le' [m' [TRACE [STATE MOVE]]]]]];
      destruct (@memory_body_step ge locals _ stack le m code' stack' le' m' MOVE CODE STACK)
        as [TEMPS [CODE' STACK']]; subst le';
      exists (@sl_body code' stack' le m' CODE' STACK' ACTIVE); repeat split; auto;
      constructor; exact MOVE.

  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (@sl_increment_skip le m ACTIVE); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (@sl_increment_set le m ACTIVE); repeat split; constructor.
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
    exists (sl_latch (increment_temps iterator le) m); split; [reflexivity|split].
    + cbn [strict_cursor_state]; rewrite TEMPS; reflexivity.
    + constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kloop2 _ _ _) |- _ => contradiction end.
    exists (sl_start le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sl_break le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (sl_done le m); repeat split; constructor.
  - discriminate DONE.
Qed.

Definition sl_run le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m sl_code E0 (fst result) (snd result) Out_normal.
Definition sl_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt fe ge locals le m sl_increment E0 le1 m1 Out_normal /\ sl_run le1 m1 result.
Definition sl_raw_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt fe ge locals le m (counter_increment iterator) E0 le1 m1 Out_normal /\ sl_run le1 m1 result.
Definition sl_body_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt fe ge locals le m body E0 le1 m1 Out_normal /\ sl_increment_tail le1 m1 result.
Definition sl_check_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m sl_check E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt fe ge locals le m sl_check E0 le1 m1 Out_normal /\ sl_body_tail le1 m1 result.
Definition sl_prelude_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m sl_prelude E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt fe ge locals le m sl_prelude E0 le1 m1 Out_normal /\ sl_body_tail le1 m1 result.
Definition sl_header_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m sl_header E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt fe ge locals le m sl_header E0 le1 m1 Out_normal /\ sl_increment_tail le1 m1 result.
Definition strict_cursor_completion c (result : temp_env * mem) : Prop :=
  match c with
  | sl_start le m | sl_latch le m => sl_run le m result
  | sl_outer le m => sl_header_completion le m result
  | sl_inner le m => sl_prelude_completion le m result
  | sl_head_skip le m | sl_condition le m => sl_check_completion le m result
  | @sl_true_skip le m _ => sl_body_tail le m result
  | @sl_body code stack le m _ _ _ => exists le1 m1,
      resumed_execution fe ge locals code stack le m le1 m1 /\ sl_increment_tail le1 m1 result
  | @sl_increment_seq le m _ => sl_increment_tail le m result
  | @sl_increment_skip le m _ | @sl_increment_set le m _ => sl_raw_increment_tail le m result
  | sl_break_seq le m | sl_break le m | sl_done le m => result = (le,m)
  end.

Lemma strict_completion_prepend c n result : strict_cursor_step c n ->
  strict_cursor_completion n result -> strict_cursor_completion c result.
Proof.
  intros MOVE RUN; inversion MOVE; subst; cbn [strict_cursor_completion] in RUN |- *.
  - destruct RUN as [STOP | [le1 [m1 [HEADER [le2 [m2 [INC TAIL]]]]]]]; unfold sl_run.
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
      [apply strict_increment_normal; exact ACTIVE|exact RUN].
  - exact RUN.
  - exact RUN.
  - exact RUN.
Qed.

Definition strict_exit_state (result : temp_env * mem) : state :=
  State fn Sskip outside locals (fst result) (snd result).
Lemma strict_done_state c result : strict_cursor_done c = Some result ->
  strict_cursor_state c = strict_exit_state result.
Proof. destruct c; cbn [strict_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.
Lemma strict_done_completion c result : strict_cursor_done c = Some result ->
  strict_cursor_completion c result.
Proof. destruct c; cbn [strict_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.

Definition strict_region_protocol :
  silent_protocol state event (temp_env * mem) (step ge (fe ge)) strict_exit_state :=
  {| cursor := strict_cursor; cursor_state := strict_cursor_state;
     cursor_rank := strict_cursor_rank; cursor_done := strict_cursor_done;
     cursor_completion := strict_cursor_completion; cursor_step := strict_cursor_step;
     cursor_step_sound := strict_step_sound; cursor_step_active := strict_step_active;
     cursor_step_decreases := strict_step_decreases; cursor_step_closed := strict_step_closed;
     cursor_completion_prepend := strict_completion_prepend;
     cursor_done_state := strict_done_state; cursor_done_completion := strict_done_completion |}.
Definition strict_entry_state (input : temp_env * mem) : state :=
  State fn sl_code outside locals (fst input) (snd input).
Definition strict_entry_result (input result : temp_env * mem) : Prop := sl_run (fst input) (snd input) result.
Definition strict_region_entry : protocol_entry strict_region_protocol
  (temp_env * mem) strict_entry_state strict_entry_result.
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (step ge (fe ge)) strict_exit_state
    strict_region_protocol (temp_env * mem) strict_entry_state strict_entry_result
    (fun input => sl_start (fst input) (snd input)) _ _); intros; auto.
Defined.
Theorem strict_region_cannot_diverge c : ~ cursor_infinite strict_region_protocol c.
Proof. apply cursor_cannot_diverge. Qed.
Theorem strict_region_completed input length final result :
  cursor_path strict_region_protocol (sl_start (fst input) (snd input)) length final ->
  strict_cursor_done final = Some result ->
  exec_stmt fe ge locals (fst input) (snd input) sl_code E0 (fst result) (snd result) Out_normal /\
  length <= strict_remaining iterator (fst input) * sl_stride + 7.
Proof. apply (completed_entry strict_region_entry). Qed.
End STRICT_LOOP_PROTOCOL.
Print Assumptions strict_step_closed.
Print Assumptions strict_region_completed.

Definition strict_frontend_progress iterator condition body
  (BODY : memory_body body = true)
  (HEAD : forall ge locals le m, expression_test condition (Entry ge locals le m) true ->
    strict_counter_active iterator le) : region_progress (strict_frontend_loop iterator condition body).
Proof.
  assert (QUIET : quiet_statement (strict_frontend_loop iterator condition body) = true).
  { cbn [strict_frontend_loop quiet_statement counter_increment].
    rewrite (finite_statement_quiet body (memory_body_finite body BODY)); reflexivity. }
  refine {| progress_label_free := quiet_statement_label_free _ QUIET;
    progress_protocol := fun temps ge fn outside locals =>
      @strict_region_protocol (adapter_entry temps) ge locals fn outside iterator condition (fun le m TEST => @HEAD ge locals le m TEST) body BODY;
    progress_entry := fun temps ge fn outside locals =>
      @strict_region_entry (adapter_entry temps) ge locals fn outside iterator condition (fun le m TEST => @HEAD ge locals le m TEST) body BODY |}.
  - intros; reflexivity.
  - intros temps ge fn outside locals c; destruct c; cbn [cursor_state strict_region_protocol strict_cursor_state];
      repeat eexists; reflexivity.
  - intros temps ge tge GLOBALS locals le m le' m' RUN.
    eapply quiet_execution_preserved; [exact GLOBALS|exact RUN|exact QUIET].
Defined.
Print Assumptions strict_frontend_progress.
