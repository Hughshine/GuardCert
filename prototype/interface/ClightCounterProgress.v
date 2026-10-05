From Stdlib Require Import List Bool Arith Lia.
From compcert.lib Require Import Maps Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightFiniteRegion ClightCountedLoop
  ClightGuard SemanticFacts ClightCondition ClightPureExpr ClightCountedProtocol ClightRegionProgress.
Import ListNotations.
Set Implicit Arguments.

(** A language-side source protocol parameterized by counter facts. The rank
    and increment need not be signed, monotone in integers, or non-wrapping. *)
Definition generic_frontend_loop iterator increment_expression condition body :=
  Sloop (Ssequence (Ssequence Sskip (Sifthenelse condition Sskip Sbreak)) body)
    (Ssequence Sskip (Sset iterator increment_expression)).
Record counter_progress_facts iterator increment_expression := CounterProgressFacts {
  counter_model_active : temp_env -> Prop;
  counter_model_remaining : temp_env -> nat;
  counter_model_next : temp_env -> temp_env;
  counter_model_positive : forall le, counter_model_active le -> (0 < counter_model_remaining le)%nat;
  counter_model_distance : forall le, counter_model_active le ->
    counter_model_remaining le = S (counter_model_remaining (counter_model_next le));
  counter_model_evaluation : forall ge locals le memory, counter_model_active le ->
    exists value, eval_expr ge locals le memory increment_expression value /\
      PTree.set iterator value le = counter_model_next le;
  counter_model_increment_pure : pure_scalar increment_expression
}.
Arguments counter_progress_facts iterator increment_expression.
Lemma generic_increment_normal fe ge locals iterator increment_expression
  (FACTS : counter_progress_facts iterator increment_expression) le memory :
  counter_model_active FACTS le ->
  exec_stmt fe ge locals le memory (Sset iterator increment_expression) E0 (counter_model_next FACTS le) memory Out_normal.
Proof.
  intro ACTIVE; destruct (@counter_model_evaluation iterator increment_expression FACTS ge locals le memory ACTIVE)
    as [value [EVAL TEMPS]]; rewrite <- TEMPS; constructor; exact EVAL.
Qed.

Section GENERIC_COUNTER_PROTOCOL.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable fn : function.
Variable outside : cont.
Variable iterator : ident.
Variable increment_expression : expr.
Variable FACTS : counter_progress_facts iterator increment_expression.
Variable condition : expr.
Hypothesis HEAD : forall le m,
  expression_test condition (Entry ge locals le m) true -> counter_model_active FACTS le.
Variable body : statement.
Hypothesis BODY : memory_body body = true.
Local Open Scope nat_scope.


Definition cp_check := Sifthenelse condition Sskip Sbreak.
Definition cp_prelude := Ssequence Sskip cp_check.
Definition cp_header := Ssequence cp_prelude body.
Definition cp_increment := Ssequence Sskip ((Sset iterator increment_expression)).
Definition cp_code := generic_frontend_loop iterator increment_expression condition body.
Definition cp_stride := statement_weight body + 11.

Inductive generic_cursor : Type :=
| cp_start (le : temp_env) (m : mem)
| cp_outer (le : temp_env) (m : mem)
| cp_inner (le : temp_env) (m : mem)
| cp_head_skip (le : temp_env) (m : mem)
| cp_condition (le : temp_env) (m : mem)
| cp_true_skip (le : temp_env) (m : mem) (ACTIVE : counter_model_active FACTS le)
| cp_body (code : statement) (stack : list statement) (le : temp_env) (m : mem)
    (CODE : memory_body code = true)
    (STACK : Forall (fun s => memory_body s = true) stack)
    (ACTIVE : counter_model_active FACTS le)
| cp_increment_seq (le : temp_env) (m : mem) (ACTIVE : counter_model_active FACTS le)
| cp_increment_skip (le : temp_env) (m : mem) (ACTIVE : counter_model_active FACTS le)
| cp_increment_set (le : temp_env) (m : mem) (ACTIVE : counter_model_active FACTS le)
| cp_latch (le : temp_env) (m : mem)
| cp_break_seq (le : temp_env) (m : mem)
| cp_break (le : temp_env) (m : mem)
| cp_done (le : temp_env) (m : mem).

Definition generic_cursor_state c : state :=
  match c with
  | cp_start le m => State fn cp_code outside locals le m
  | cp_outer le m => State fn cp_header (Kloop1 cp_header cp_increment outside) locals le m
  | cp_inner le m => State fn cp_prelude
      (Kseq body (Kloop1 cp_header cp_increment outside)) locals le m
  | cp_head_skip le m => State fn Sskip
      (Kseq cp_check (Kseq body (Kloop1 cp_header cp_increment outside))) locals le m
  | cp_condition le m => State fn cp_check
      (Kseq body (Kloop1 cp_header cp_increment outside)) locals le m
  | @cp_true_skip le m _ => State fn Sskip
      (Kseq body (Kloop1 cp_header cp_increment outside)) locals le m
  | @cp_body code stack le m _ _ _ =>
      State fn code (region_cont stack (Kloop1 cp_header cp_increment outside)) locals le m
  | @cp_increment_seq le m _ => State fn cp_increment
      (Kloop2 cp_header cp_increment outside) locals le m
  | @cp_increment_skip le m _ => State fn Sskip
      (Kseq ((Sset iterator increment_expression)) (Kloop2 cp_header cp_increment outside)) locals le m
  | @cp_increment_set le m _ => State fn ((Sset iterator increment_expression))
      (Kloop2 cp_header cp_increment outside) locals le m
  | cp_latch le m => State fn Sskip (Kloop2 cp_header cp_increment outside) locals le m
  | cp_break_seq le m => State fn Sbreak
      (Kseq body (Kloop1 cp_header cp_increment outside)) locals le m
  | cp_break le m => State fn Sbreak (Kloop1 cp_header cp_increment outside) locals le m
  | cp_done le m => State fn Sskip outside locals le m
  end.

Definition generic_cursor_rank c : nat :=
  match c with
  | cp_start le _ => counter_model_remaining FACTS le * cp_stride + 7
  | cp_outer le _ => counter_model_remaining FACTS le * cp_stride + 6
  | cp_inner le _ => counter_model_remaining FACTS le * cp_stride + 5
  | cp_head_skip le _ => counter_model_remaining FACTS le * cp_stride + 4
  | cp_condition le _ => counter_model_remaining FACTS le * cp_stride + 3
  | @cp_true_skip le _ _ => counter_model_remaining FACTS le * cp_stride + 2
  | @cp_body code stack le m _ _ _ =>
      Nat.pred (counter_model_remaining FACTS le) * cp_stride +
        state_weight (State fn code (region_cont stack Kstop) locals le m) + 12
  | @cp_increment_seq le _ _ => Nat.pred (counter_model_remaining FACTS le) * cp_stride + 11
  | @cp_increment_skip le _ _ => Nat.pred (counter_model_remaining FACTS le) * cp_stride + 10
  | @cp_increment_set le _ _ => Nat.pred (counter_model_remaining FACTS le) * cp_stride + 9
  | cp_latch le _ => counter_model_remaining FACTS le * cp_stride + 8
  | cp_break_seq _ _ => 2
  | cp_break _ _ => 1
  | cp_done _ _ => 0
  end.

Definition generic_cursor_done c : option (temp_env * mem) :=
  match c with cp_done le m => Some (le,m) | _ => None end.

Inductive generic_cursor_step : generic_cursor -> generic_cursor -> Prop :=
| cp_step_start : forall le m, generic_cursor_step (cp_start le m) (cp_outer le m)
| cp_step_outer : forall le m, generic_cursor_step (cp_outer le m) (cp_inner le m)
| cp_step_inner : forall le m, generic_cursor_step (cp_inner le m) (cp_head_skip le m)
| cp_step_head_skip : forall le m, generic_cursor_step (cp_head_skip le m) (cp_condition le m)
| cp_step_true : forall le m ACTIVE,
    expression_test condition (Entry ge locals le m) true ->
    generic_cursor_step (cp_condition le m) (@cp_true_skip le m ACTIVE)
| cp_step_false : forall le m,
    expression_test condition (Entry ge locals le m) false ->
    generic_cursor_step (cp_condition le m) (cp_break_seq le m)
| cp_step_true_skip : forall le m ACTIVE,
    generic_cursor_step (@cp_true_skip le m ACTIVE) (@cp_body body [] le m BODY (Forall_nil _) ACTIVE)
| cp_step_body : forall code stack le m code' stack' m' CODE STACK CODE' STACK' ACTIVE,
    fragment_step ge locals code stack le m code' stack' le m' ->
    generic_cursor_step (@cp_body code stack le m CODE STACK ACTIVE)
      (@cp_body code' stack' le m' CODE' STACK' ACTIVE)
| cp_step_body_done : forall le m CODE STACK ACTIVE,
    generic_cursor_step (@cp_body Sskip [] le m CODE STACK ACTIVE) (@cp_increment_seq le m ACTIVE)
| cp_step_increment_seq : forall le m ACTIVE,
    generic_cursor_step (@cp_increment_seq le m ACTIVE) (@cp_increment_skip le m ACTIVE)
| cp_step_increment_skip : forall le m ACTIVE,
    generic_cursor_step (@cp_increment_skip le m ACTIVE) (@cp_increment_set le m ACTIVE)
| cp_step_increment_set : forall le m ACTIVE,
    generic_cursor_step (@cp_increment_set le m ACTIVE) (cp_latch (counter_model_next FACTS le) m)
| cp_step_latch : forall le m, generic_cursor_step (cp_latch le m) (cp_start le m)
| cp_step_break_seq : forall le m, generic_cursor_step (cp_break_seq le m) (cp_break le m)
| cp_step_break : forall le m, generic_cursor_step (cp_break le m) (cp_done le m).

Lemma generic_step_sound c n : generic_cursor_step c n ->
  step ge (fe ge) (generic_cursor_state c) E0 (generic_cursor_state n).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [generic_cursor_state].
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
  - destruct (@counter_model_evaluation iterator increment_expression FACTS ge locals le m ACTIVE)
      as [v [EVAL TEMPS]]. rewrite <- TEMPS. constructor; exact EVAL.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma generic_step_active c n : generic_cursor_step c n -> generic_cursor_done c = None.
Proof. intro MOVE; inversion MOVE; reflexivity. Qed.

Lemma generic_step_decreases c n : generic_cursor_step c n -> generic_cursor_rank n < generic_cursor_rank c.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [generic_cursor_rank]; try lia.
  - pose proof (@counter_model_positive iterator increment_expression FACTS le ACTIVE) as POS.
    unfold cp_stride; cbn [state_weight region_cont continuation_weight].
    destruct (counter_model_remaining FACTS le); [lia|]. simpl; nia.
  - pose proof (@fragment_step_decreases ge locals code stack le m code' stack' le m' H fn Kstop).
    lia.
  - rewrite (@counter_model_distance iterator increment_expression FACTS le ACTIVE); simpl; lia.
Qed.

Lemma generic_step_closed c events next_state : generic_cursor_done c = None ->
  step ge (fe ge) (generic_cursor_state c) events next_state ->
  exists n, events = E0 /\ next_state = generic_cursor_state n /\ generic_cursor_step c n.
Proof.
  destruct c; cbn [generic_cursor_state generic_cursor_done]; intros DONE STEP.
  - inversion STEP; subst; try discriminate;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (cp_outer le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (cp_inner le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (cp_head_skip le m); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (cp_condition le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    assert (TEST : expression_test condition (Entry ge locals le m) b)
      by (eexists; split; eassumption).
    destruct b.
    + pose proof (HEAD TEST) as ACTIVE.
      exists (@cp_true_skip le m ACTIVE); repeat split; auto. constructor; exact TEST.
    + exists (cp_break_seq le m); repeat split; auto. constructor; exact TEST.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (@cp_body body [] le m BODY (Forall_nil _) ACTIVE); repeat split; constructor.
  - destruct code; try (exfalso; discriminate CODE).
    { destruct stack as [|next rest].
      * simpl in STEP. inversion STEP; subst; try contradiction;
          try match goal with BAD : is_call_cont (Kloop1 _ _ _) |- _ => contradiction end;
          try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
        exists (@cp_increment_seq le m ACTIVE); repeat split; try reflexivity.
        constructor.
      * assert (FIN : finite_statement Sskip = true) by reflexivity.
        assert (FSTACK : Forall (fun s => finite_statement s = true) (next :: rest))
          by (eapply Forall_impl; [intros s M; apply memory_body_finite; exact M | exact STACK]).
        assert (ACTIVE_STACK : Sskip <> Sskip \/ (next :: rest) <> [])
          by (right; discriminate).
        destruct (@fragment_step_from_ambient fe ge locals fn Sskip (next :: rest)
          (Kloop1 cp_header cp_increment outside) le m events next_state FIN FSTACK
          ACTIVE_STACK STEP)
          as [code' [stack' [le' [m' [TRACE [STATE MOVE]]]]]].
        destruct (@memory_body_step ge locals Sskip (next :: rest) le m code' stack' le' m'
          MOVE CODE STACK) as [TEMPS [CODE' STACK']]; subst le'.
        exists (@cp_body code' stack' le m' CODE' STACK' ACTIVE); repeat split; auto.
        constructor; exact MOVE.
    }
    all: pose proof (memory_body_finite _ CODE) as FIN;
      assert (FSTACK : Forall (fun s => finite_statement s = true) stack)
        by (eapply Forall_impl; [intros s M; apply memory_body_finite; exact M | exact STACK]);
      match type of CODE with memory_body ?code = true =>
        assert (ACTIVE_CODE : code <> Sskip \/ stack <> []) by (left; discriminate)
      end;
      destruct (@fragment_step_from_ambient fe ge locals fn _ stack
        (Kloop1 cp_header cp_increment outside) le m events next_state FIN FSTACK
        ACTIVE_CODE STEP)
        as [code' [stack' [le' [m' [TRACE [STATE MOVE]]]]]];
      destruct (@memory_body_step ge locals _ stack le m code' stack' le' m' MOVE CODE STACK)
        as [TEMPS [CODE' STACK']]; subst le';
      exists (@cp_body code' stack' le m' CODE' STACK' ACTIVE); repeat split; auto;
      constructor; exact MOVE.

  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (@cp_increment_skip le m ACTIVE); repeat split; constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    exists (@cp_increment_set le m ACTIVE); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    match goal with SOURCE : eval_expr _ _ _ _ _ _ |- _ => rename SOURCE into SOURCE_VALUE end.
    destruct (@counter_model_evaluation iterator increment_expression FACTS ge locals le m ACTIVE)
      as [v' [EVAL TEMPS]].
    pose proof (counter_model_increment_pure FACTS) as PURE.
    match type of SOURCE_VALUE with eval_expr _ _ _ _ _ ?v =>
      pose proof (@pure_scalar_determinate _ PURE ge locals le m v v' SOURCE_VALUE EVAL) as VALUE;
      subst v
    end.
    exists (cp_latch (counter_model_next FACTS le) m); split; [reflexivity|split].
    + cbn [generic_cursor_state]; rewrite TEMPS; reflexivity.
    + constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kloop2 _ _ _) |- _ => contradiction end.
    exists (cp_start le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (cp_break le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (cp_done le m); repeat split; constructor.
  - discriminate DONE.
Qed.

Definition cp_run le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m cp_code E0 (fst result) (snd result) Out_normal.
Definition cp_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt fe ge locals le m cp_increment E0 le1 m1 Out_normal /\ cp_run le1 m1 result.
Definition cp_raw_increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt fe ge locals le m ((Sset iterator increment_expression)) E0 le1 m1 Out_normal /\ cp_run le1 m1 result.
Definition cp_body_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt fe ge locals le m body E0 le1 m1 Out_normal /\ cp_increment_tail le1 m1 result.
Definition cp_check_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m cp_check E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt fe ge locals le m cp_check E0 le1 m1 Out_normal /\ cp_body_tail le1 m1 result.
Definition cp_prelude_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m cp_prelude E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt fe ge locals le m cp_prelude E0 le1 m1 Out_normal /\ cp_body_tail le1 m1 result.
Definition cp_header_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m cp_header E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt fe ge locals le m cp_header E0 le1 m1 Out_normal /\ cp_increment_tail le1 m1 result.
Definition generic_cursor_completion c (result : temp_env * mem) : Prop :=
  match c with
  | cp_start le m | cp_latch le m => cp_run le m result
  | cp_outer le m => cp_header_completion le m result
  | cp_inner le m => cp_prelude_completion le m result
  | cp_head_skip le m | cp_condition le m => cp_check_completion le m result
  | @cp_true_skip le m _ => cp_body_tail le m result
  | @cp_body code stack le m _ _ _ => exists le1 m1,
      resumed_execution fe ge locals code stack le m le1 m1 /\ cp_increment_tail le1 m1 result
  | @cp_increment_seq le m _ => cp_increment_tail le m result
  | @cp_increment_skip le m _ | @cp_increment_set le m _ => cp_raw_increment_tail le m result
  | cp_break_seq le m | cp_break le m | cp_done le m => result = (le,m)
  end.

Lemma generic_completion_prepend c n result : generic_cursor_step c n ->
  generic_cursor_completion n result -> generic_cursor_completion c result.
Proof.
  intros MOVE RUN; inversion MOVE; subst; cbn [generic_cursor_completion] in RUN |- *.
  - destruct RUN as [STOP | [le1 [m1 [HEADER [le2 [m2 [INC TAIL]]]]]]]; unfold cp_run.
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
  - exists (counter_model_next FACTS le),m; split;
      [apply generic_increment_normal; exact ACTIVE|exact RUN].
  - exact RUN.
  - exact RUN.
  - exact RUN.
Qed.

Definition generic_exit_state (result : temp_env * mem) : state :=
  State fn Sskip outside locals (fst result) (snd result).
Lemma generic_done_state c result : generic_cursor_done c = Some result ->
  generic_cursor_state c = generic_exit_state result.
Proof. destruct c; cbn [generic_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.
Lemma generic_done_completion c result : generic_cursor_done c = Some result ->
  generic_cursor_completion c result.
Proof. destruct c; cbn [generic_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.

Definition generic_region_protocol :
  silent_protocol state event (temp_env * mem) (step ge (fe ge)) generic_exit_state :=
  {| cursor := generic_cursor; cursor_state := generic_cursor_state;
     cursor_rank := generic_cursor_rank; cursor_done := generic_cursor_done;
     cursor_completion := generic_cursor_completion; cursor_step := generic_cursor_step;
     cursor_step_sound := generic_step_sound; cursor_step_active := generic_step_active;
     cursor_step_decreases := generic_step_decreases; cursor_step_closed := generic_step_closed;
     cursor_completion_prepend := generic_completion_prepend;
     cursor_done_state := generic_done_state; cursor_done_completion := generic_done_completion |}.
Definition generic_entry_state (input : temp_env * mem) : state :=
  State fn cp_code outside locals (fst input) (snd input).
Definition generic_entry_result (input result : temp_env * mem) : Prop := cp_run (fst input) (snd input) result.
Definition generic_region_entry : protocol_entry generic_region_protocol
  (temp_env * mem) generic_entry_state generic_entry_result.
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (step ge (fe ge)) generic_exit_state
    generic_region_protocol (temp_env * mem) generic_entry_state generic_entry_result
    (fun input => cp_start (fst input) (snd input)) _ _); intros; auto.
Defined.
Theorem generic_region_cannot_diverge c : ~ cursor_infinite generic_region_protocol c.
Proof. apply cursor_cannot_diverge. Qed.
Theorem generic_region_completed input length final result :
  cursor_path generic_region_protocol (cp_start (fst input) (snd input)) length final ->
  generic_cursor_done final = Some result ->
  exec_stmt fe ge locals (fst input) (snd input) cp_code E0 (fst result) (snd result) Out_normal /\
  length <= counter_model_remaining FACTS (fst input) * cp_stride + 7.
Proof. apply (completed_entry generic_region_entry). Qed.
End GENERIC_COUNTER_PROTOCOL.
Print Assumptions generic_step_closed.
Print Assumptions generic_region_completed.

Definition generic_frontend_progress iterator increment_expression (FACTS : counter_progress_facts iterator increment_expression) condition body
  (BODY : memory_body body = true)
  (HEAD : forall ge locals le m, expression_test condition (Entry ge locals le m) true ->
    counter_model_active FACTS le) : region_progress (generic_frontend_loop iterator increment_expression condition body).
Proof.
  assert (QUIET : quiet_statement (generic_frontend_loop iterator increment_expression condition body) = true).
  { cbn [generic_frontend_loop quiet_statement].
    rewrite (finite_statement_quiet body (memory_body_finite body BODY)); reflexivity. }
  refine {| progress_label_free := quiet_statement_label_free _ QUIET;
    progress_protocol := fun temps ge fn outside locals =>
      @generic_region_protocol (adapter_entry temps) ge locals fn outside iterator increment_expression FACTS condition (fun le m TEST => @HEAD ge locals le m TEST) body BODY;
    progress_entry := fun temps ge fn outside locals =>
      @generic_region_entry (adapter_entry temps) ge locals fn outside iterator increment_expression FACTS condition (fun le m TEST => @HEAD ge locals le m TEST) body BODY |}.
  - intros; reflexivity.
  - intros temps ge fn outside locals c; destruct c; cbn [cursor_state generic_region_protocol generic_cursor_state];
      repeat eexists; reflexivity.
  - intros temps ge tge GLOBALS locals le m le' m' RUN.
    eapply quiet_execution_preserved; [exact GLOBALS|exact RUN|exact QUIET].
Defined.
Print Assumptions generic_frontend_progress.
