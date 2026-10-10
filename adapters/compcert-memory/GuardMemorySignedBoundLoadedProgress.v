From Stdlib Require Import List Bool ZArith Arith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightGuard ClightCondition ClightPureExpr
  ClightRegionProgress ClightFragmentProgress ClightSequenceProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl GuardMemoryLongProgressControl GuardMemorySignedLongBoundControl.
Import ListNotations.
Set Implicit Arguments.

(** The actual normalized loaded-bound shape. The bound is evaluated on each
    test, may read memory, and need not be stable for this control protocol. *)
Definition signed_bound_loaded_loop iterator bound body :=
  Sloop (Ssequence (Sifthenelse (long_counter_condition iterator bound) Sskip Sbreak) body)
    (long_counter_increment iterator).
Definition signed_bound_initialized_loop iterator bound body :=
  Ssequence (Sset iterator memory_long_zero) (signed_bound_loaded_loop iterator bound body).

Section LONG_LOADED_PROTOCOL.
Variable temps : bool.
Variable ge : genv.
Variable locals : env.
Variable fn : function.
Variable outside : cont.
Variable iterator : ident.
Variable bound : expr.
Hypothesis BOUND_TYPE : signed_long_bound_type bound.
Variable body : statement.
Variable protected : list ident.
Hypothesis NOT_WRITTEN : ~ In iterator protected.
Variable F : framed_progress body (iterator::protected).
Local Open Scope nat_scope.

Definition ll_check := Sifthenelse (long_counter_condition iterator bound) Sskip Sbreak.
Definition ll_header := Ssequence ll_check body.
Definition ll_increment := long_counter_increment iterator.
Definition ll_code := signed_bound_loaded_loop iterator bound body.
Definition ll_stride := framed_bound F+7.
Let body_cont := Kloop1 ll_header ll_increment outside.
Let P := framed_protocol F temps ge fn body_cont locals.
Let E := framed_entry F temps ge fn body_cont locals.
Let V := framed_view F temps ge fn body_cont locals.

Inductive signed_bound_loaded_cursor : Type :=
| ll_start (le : temp_env) (m : mem)
| ll_outer (le : temp_env) (m : mem)
| ll_condition (le : temp_env) (m : mem)
| ll_true_skip (le : temp_env) (m : mem) (ACTIVE : long_counter_active iterator le)
| ll_body (c : cursor P) (ACTIVE : long_counter_active iterator (fst (V c)))
| ll_increment_set (le : temp_env) (m : mem) (ACTIVE : long_counter_active iterator le)
| ll_latch (le : temp_env) (m : mem)
| ll_break_seq (le : temp_env) (m : mem)
| ll_break (le : temp_env) (m : mem)
| ll_done (le : temp_env) (m : mem).
Definition ll_state c : state := match c with
  | ll_start le m => State fn ll_code outside locals le m
  | ll_outer le m => State fn ll_header body_cont locals le m
  | ll_condition le m => State fn ll_check (Kseq body body_cont) locals le m
  | @ll_true_skip le m _ => State fn Sskip (Kseq body body_cont) locals le m
  | @ll_body c _ => cursor_state P c
  | @ll_increment_set le m _ => State fn ll_increment (Kloop2 ll_header ll_increment outside) locals le m
  | ll_latch le m => State fn Sskip (Kloop2 ll_header ll_increment outside) locals le m
  | ll_break_seq le m => State fn Sbreak (Kseq body body_cont) locals le m
  | ll_break le m => State fn Sbreak body_cont locals le m
  | ll_done le m => State fn Sskip outside locals le m end.
Definition ll_rank c : nat := match c with
  | ll_start le _ => long_counter_remaining iterator le*ll_stride+5
  | ll_outer le _ => long_counter_remaining iterator le*ll_stride+4
  | ll_condition le _ => long_counter_remaining iterator le*ll_stride+3
  | @ll_true_skip le _ _ => long_counter_remaining iterator le*ll_stride+2
  | @ll_body c _ => Nat.pred (long_counter_remaining iterator (fst (V c)))*ll_stride+cursor_rank P c+8
  | @ll_increment_set le _ _ => Nat.pred (long_counter_remaining iterator le)*ll_stride+7
  | ll_latch le _ => long_counter_remaining iterator le*ll_stride+6
  | ll_break_seq _ _ => 2 | ll_break _ _ => 1 | ll_done _ _ => 0 end.
Definition ll_done_result c : option (temp_env*mem) := match c with ll_done le m => Some (le,m) | _ => None end.
Inductive ll_step : signed_bound_loaded_cursor -> signed_bound_loaded_cursor -> Prop :=
| ll_step_start le m : ll_step (ll_start le m) (ll_outer le m)
| ll_step_outer le m : ll_step (ll_outer le m) (ll_condition le m)
| ll_step_true le m ACTIVE : expression_test (long_counter_condition iterator bound) (Entry ge locals le m) true ->
    ll_step (ll_condition le m) (@ll_true_skip le m ACTIVE)
| ll_step_false le m : expression_test (long_counter_condition iterator bound) (Entry ge locals le m) false ->
    ll_step (ll_condition le m) (ll_break_seq le m)
| ll_step_true_skip le m ACTIVE ACTIVE' : ll_step (@ll_true_skip le m ACTIVE)
    (@ll_body (begin_cursor E (le,m)) ACTIVE')
| ll_step_body c next ACTIVE ACTIVE' : cursor_step P c next -> ll_step (@ll_body c ACTIVE) (@ll_body next ACTIVE')
| ll_step_body_done c result ACTIVE ACTIVE' : cursor_done P c=Some result ->
    ll_step (@ll_body c ACTIVE) (@ll_increment_set (fst result) (snd result) ACTIVE')
| ll_step_increment_set le m ACTIVE : ll_step (@ll_increment_set le m ACTIVE) (ll_latch (long_increment_temps iterator le) m)
| ll_step_latch le m : ll_step (ll_latch le m) (ll_start le m)
| ll_step_break_seq le m : ll_step (ll_break_seq le m) (ll_break le m)
| ll_step_break le m : ll_step (ll_break le m) (ll_done le m).

Lemma ll_sound c next : ll_step c next -> adapter_step temps ge (ll_state c) E0 (ll_state next).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [ll_state].
  - constructor.
  - constructor.
  - destruct H as [v [EVAL BOOL]]; eapply step_ifthenelse with (b:=true); eauto.
  - destruct H as [v [EVAL BOOL]]; eapply step_ifthenelse with (b:=false); eauto.
  - rewrite (begin_state E); constructor.
  - exact (cursor_step_sound P _ _ H).
  - rewrite (cursor_done_state P _ H); apply step_skip_or_continue_loop1; left; reflexivity.
  - destruct (@long_counter_increment_evaluation ge locals iterator le m ACTIVE) as [v [EVAL SET]].
    rewrite <- SET; constructor; exact EVAL.
  - constructor.
  - constructor.
  - constructor.
Qed.
Lemma ll_active c next : ll_step c next -> ll_done_result c=None.
Proof. intro MOVE; inversion MOVE; reflexivity. Qed.
Lemma ll_decreases c next : ll_step c next -> ll_rank next<ll_rank c.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [ll_rank]; try lia.
  - unfold V,E in *; rewrite framed_begin_view in *.
    pose proof (framed_begin_bound F temps ge fn body_cont locals (le,m)) as BOUND.
    pose proof (@long_counter_active_positive iterator le ACTIVE) as POS.
    unfold P,ll_stride in *; cbn [fst snd]; destruct (long_counter_remaining iterator le); [lia|]; cbn; nia.
  - pose proof (framed_step_frame F temps ge fn body_cont locals _ _ H) as FRAME.
    pose proof (@long_counter_frame_distance iterator protected _ _ FRAME) as SAME.
    pose proof (cursor_step_decreases P _ _ H) as DEC; unfold V in *; rewrite SAME; lia.
  - pose proof (framed_done_view F temps ge fn body_cont locals _ H) as VIEW.
    pose proof (framed_done_rank F temps ge fn body_cont locals _ H) as RANK.
    unfold V,P in *; rewrite VIEW,RANK; lia.
  - rewrite (@long_counter_increment_distance iterator le ACTIVE); cbn; lia.
Qed.
Lemma ll_closed c events next_state : ll_done_result c=None ->
  adapter_step temps ge (ll_state c) events next_state ->
  exists next, events=E0 /\ next_state=ll_state next /\ ll_step c next.
Proof.
  destruct c; cbn [ll_state ll_done_result]; intros DONE STEP.
  - inversion STEP; subst; try discriminate;
      try match goal with BAD : _=_ \/ _=_ |- _ => destruct BAD; discriminate end.
    exists (ll_outer le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _=_ \/ _=_ |- _ => destruct BAD; discriminate end.
    exists (ll_condition le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _=_ \/ _=_ |- _ => destruct BAD; discriminate end.
    assert (TEST : expression_test (long_counter_condition iterator bound) (Entry ge locals le m) b)
      by (eexists; split; eassumption).
    destruct b.
    + pose proof (@signed_long_bound_condition_active ge locals le m iterator bound BOUND_TYPE TEST) as ACTIVE.
      exists (@ll_true_skip le m ACTIVE); repeat split; auto; constructor; exact TEST.
    + exists (ll_break_seq le m); repeat split; auto; constructor; exact TEST.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kseq _ _) |- _ => contradiction end.
    assert (ACTIVE' : long_counter_active iterator (fst (V (begin_cursor E (le,m))))).
    { unfold V,E; rewrite framed_begin_view; exact ACTIVE. }
    exists (@ll_body (begin_cursor E (le,m)) ACTIVE'); split; [reflexivity|split].
    + cbn [ll_state]; rewrite (begin_state E); reflexivity.
    + constructor.
  - destruct (cursor_done P c) as [result|] eqn:BODY_DONE.
    + rewrite (cursor_done_state P c BODY_DONE) in STEP.
      inversion STEP; subst; try contradiction;
        try match goal with BAD : is_call_cont (Kloop1 _ _ _) |- _ => contradiction end;
        try match goal with BAD : _=_ \/ _=_ |- _ => destruct BAD; discriminate end.
      pose proof (framed_done_view F temps ge fn body_cont locals c BODY_DONE) as VIEW.
      exists (@ll_increment_set (fst (V c)) (snd (V c)) ACTIVE); split; [reflexivity|split].
      * cbn [ll_state]; unfold V; rewrite VIEW; reflexivity.
      * rewrite <- VIEW in BODY_DONE; constructor; exact BODY_DONE.
    + destruct (cursor_step_closed P c _ _ BODY_DONE STEP) as [next [TRACE [STATE MOVE]]].
      assert (ACTIVE' : long_counter_active iterator (fst (V next))).
      { eapply long_counter_frame_active; [eapply framed_step_frame; exact MOVE|exact ACTIVE]. }
      exists (@ll_body next ACTIVE'); repeat split; auto; constructor; exact MOVE.
  - inversion STEP; subst;
      try match goal with BAD : _=_ \/ _=_ |- _ => destruct BAD; discriminate end.
    match goal with SOURCE : eval_expr _ _ _ _ _ _ |- _ => rename SOURCE into SOURCE_VALUE end.
    destruct (@long_counter_increment_evaluation ge locals iterator le m ACTIVE) as [value [EVAL SET]].
    assert (PURE : pure_scalar (memory_long_plus_int (Etempvar iterator memory_long_type) 1))
      by (unfold memory_long_plus_int; repeat constructor).
    match type of SOURCE_VALUE with eval_expr _ _ _ _ _ ?v =>
      pose proof (@pure_scalar_determinate _ PURE ge locals le m v value SOURCE_VALUE EVAL) as SAME; subst v end.
    exists (ll_latch (long_increment_temps iterator le) m); split; [reflexivity|split].
    + cbn [ll_state]; rewrite SET; reflexivity.
    + constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kloop2 _ _ _) |- _ => contradiction end.
    exists (ll_start le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _=_ \/ _=_ |- _ => destruct BAD; discriminate end.
    exists (ll_break le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _=_ \/ _=_ |- _ => destruct BAD; discriminate end.
    exists (ll_done le m); repeat split; constructor.
  - discriminate DONE.
Qed.

Definition ll_run le m (result : temp_env*mem) :=
  exec_stmt (adapter_entry temps) ge locals le m ll_code E0 (fst result) (snd result) Out_normal.
Definition ll_increment_tail le m (result : temp_env*mem) := exists le1 m1,
  exec_stmt (adapter_entry temps) ge locals le m ll_increment E0 le1 m1 Out_normal /\ ll_run le1 m1 result.
Definition ll_body_tail le m (result : temp_env*mem) := exists le1 m1,
  exec_stmt (adapter_entry temps) ge locals le m body E0 le1 m1 Out_normal /\ ll_increment_tail le1 m1 result.
Definition ll_check_completion le m (result : temp_env*mem) :=
  exec_stmt (adapter_entry temps) ge locals le m ll_check E0 (fst result) (snd result) Out_break \/ exists le1 m1,
  exec_stmt (adapter_entry temps) ge locals le m ll_check E0 le1 m1 Out_normal /\ ll_body_tail le1 m1 result.
Definition ll_header_completion le m (result : temp_env*mem) :=
  exec_stmt (adapter_entry temps) ge locals le m ll_header E0 (fst result) (snd result) Out_break \/ exists le1 m1,
  exec_stmt (adapter_entry temps) ge locals le m ll_header E0 le1 m1 Out_normal /\ ll_increment_tail le1 m1 result.
Definition ll_completion c (result : temp_env*mem) := match c with
  | ll_start le m | ll_latch le m => ll_run le m result
  | ll_outer le m => ll_header_completion le m result
  | ll_condition le m => ll_check_completion le m result
  | @ll_true_skip le m _ => ll_body_tail le m result
  | @ll_body c _ => exists middle, cursor_completion P c middle /\ ll_increment_tail (fst middle) (snd middle) result
  | @ll_increment_set le m _ => ll_increment_tail le m result
  | ll_break_seq le m | ll_break le m | ll_done le m => result=(le,m) end.
Lemma ll_prepend c next result : ll_step c next -> ll_completion next result -> ll_completion c result.
Proof.
  intros MOVE RUN; inversion MOVE; subst; cbn [ll_completion] in RUN |- *.
  - destruct RUN as [STOP|[le1 [m1 [HEADER [le2 [m2 [INC TAIL]]]]]]]; unfold ll_run.
    + eapply exec_Sloop_stop1 with (out':=Out_break); [exact STOP|constructor].
    + eapply exec_Sloop_loop with (out1:=Out_normal) (t1:=E0) (t2:=E0) (t3:=E0);
        [exact HEADER|constructor|exact INC|exact TAIL].
  - destruct RUN as [STOP|[le1 [m1 [CHECK [le2 [m2 [BODY_RUN TAIL]]]]]]].
    + left; eapply exec_Sseq_2; [exact STOP|discriminate].
    + right; exists le2,m2; split; [|exact TAIL].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); eauto.
  - right; exists le,m; split; [|exact RUN].
    destruct H as [v [EVAL BOOL]]; eapply exec_Sifthenelse with (b:=true); eauto; constructor.
  - subst result; left; destruct H as [v [EVAL BOOL]]; eapply exec_Sifthenelse with (b:=false); eauto; constructor.
  - destruct RUN as [[le1 m1] [RUN TAIL]]; exists le1,m1; split; [|exact TAIL].
    apply (begin_completion E) in RUN; exact RUN.
  - destruct RUN as [middle [RUN TAIL]]; exists middle; split; [|exact TAIL]; eapply cursor_completion_prepend; eauto.
  - exists result0; split; [eapply cursor_done_completion; exact H|exact RUN].
  - exists (long_increment_temps iterator le),m; split; [apply long_counter_increment_normal; exact ACTIVE|exact RUN].
  - exact RUN.
  - exact RUN.
  - exact RUN.
Qed.
Lemma ll_done_state c result : ll_done_result c=Some result -> ll_state c=progress_exit_state fn outside locals result.
Proof. destruct c; cbn [ll_done_result]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.
Lemma ll_done_completion c result : ll_done_result c=Some result -> ll_completion c result.
Proof. destruct c; cbn [ll_done_result]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.
Definition signed_bound_loaded_protocol :=
  {| cursor:=signed_bound_loaded_cursor; cursor_state:=ll_state; cursor_rank:=ll_rank;
     cursor_done:=ll_done_result; cursor_completion:=ll_completion; cursor_step:=ll_step;
     cursor_step_sound:=ll_sound; cursor_step_active:=ll_active; cursor_step_decreases:=ll_decreases;
     cursor_step_closed:=ll_closed; cursor_completion_prepend:=ll_prepend;
     cursor_done_state:=ll_done_state; cursor_done_completion:=ll_done_completion |}.
Definition signed_bound_loaded_entry : protocol_entry signed_bound_loaded_protocol (temp_env*mem)
  (fun input => State fn ll_code outside locals (fst input) (snd input))
  (fun input result => ll_run (fst input) (snd input) result).
Proof.
  refine (@ProtocolEntry state event (temp_env*mem) (adapter_step temps ge)
    (progress_exit_state fn outside locals) signed_bound_loaded_protocol (temp_env*mem)
    _ _ (fun input => ll_start (fst input) (snd input)) _ _); intros; auto.
Defined.
Definition ll_view c := match c with
  | ll_start le m | ll_outer le m | ll_condition le m | @ll_true_skip le m _
  | @ll_increment_set le m _ | ll_latch le m | ll_break_seq le m | ll_break le m | ll_done le m => (le,m)
  | @ll_body c _ => V c end.
Lemma ll_frame c next : ll_step c next -> preserves_temporaries protected (fst (ll_view c)) (fst (ll_view next)).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [ll_view]; try solve [intros id IN; reflexivity].
  - unfold V,E; rewrite framed_begin_view; intros id IN; reflexivity.
  - intros id IN; eapply framed_step_frame; [exact H|right; exact IN].
  - unfold V; rewrite (framed_done_view F temps ge fn body_cont locals _ H); intros id IN; reflexivity.
  - intros id IN; change ((long_increment_temps iterator le) ! id=le ! id).
    unfold long_increment_temps; destruct (le ! iterator) as [v|]; [destruct v|]; try reflexivity.
    rewrite PTree.gso; [reflexivity|]; intro SAME; subst id; contradiction.
Qed.
End LONG_LOADED_PROTOCOL.

Definition signed_bound_loaded_framed_progress iterator bound (BOUND_TYPE : signed_long_bound_type bound) protected
  (NOT_WRITTEN : ~ In iterator protected) body (F : framed_progress body (iterator::protected)) :
  framed_progress (signed_bound_loaded_loop iterator bound body) protected.
Proof.
  refine {| framed_quiet:=_;
    framed_protocol:=fun temps ge fn outside locals => @signed_bound_loaded_protocol temps ge locals fn outside iterator bound BOUND_TYPE body protected F;
    framed_entry:=fun temps ge fn outside locals => @signed_bound_loaded_entry temps ge locals fn outside iterator bound BOUND_TYPE body protected F;
    framed_view:=fun temps ge fn outside locals => @ll_view temps ge locals fn outside iterator bound body protected F;
    framed_bound:=maximum_long_counter_distance*(framed_bound F+7)+5 |}.
  - change (quiet_statement (signed_bound_loaded_loop iterator bound body)=true).
    unfold signed_bound_loaded_loop,long_counter_increment; cbn [quiet_statement]; rewrite (framed_quiet F); reflexivity.
  - intros temps ge fn outside locals c; destruct c; cbn [cursor_state signed_bound_loaded_protocol ll_state ll_view];
      try (repeat eexists; reflexivity); apply (framed_shape F).
  - intros temps ge fn outside locals [le m]; reflexivity.
  - intros temps ge fn outside locals input.
    change (long_counter_remaining iterator (fst input)*(framed_bound F+7)+5 <=
      maximum_long_counter_distance*(framed_bound F+7)+5)%nat.
    pose proof (long_counter_distance_bounded iterator (fst input)); nia.
  - intros temps ge fn outside locals c result DONE; destruct c;
      cbn [cursor_done signed_bound_loaded_protocol ll_done_result] in DONE; try discriminate; reflexivity.
  - intros; apply ll_frame; [exact NOT_WRITTEN|assumption].
Defined.
Definition signed_bound_initialized_framed_progress iterator bound (BOUND_TYPE : signed_long_bound_type bound) protected
  (NOT_WRITTEN : ~ In iterator protected) body (F : framed_progress body (iterator::protected)) :
  framed_progress (signed_bound_initialized_loop iterator bound body) protected.
Proof.
  apply sequence_framed_progress.
  - apply finite_framed_progress; cbn [frame_statement].
    destruct (in_dec peq iterator protected); [contradiction|reflexivity].
  - apply signed_bound_loaded_framed_progress; assumption.
Defined.
Definition signed_bound_initialized_region_progress iterator bound (BOUND_TYPE : signed_long_bound_type bound) protected
  (NOT_WRITTEN : ~ In iterator protected) body (F : framed_progress body (iterator::protected)) :
  region_progress (signed_bound_initialized_loop iterator bound body).
Proof.
  apply sequence_region_progress with (protected:=protected).
  - apply finite_framed_progress; cbn [frame_statement].
    destruct (in_dec peq iterator protected); [contradiction|reflexivity].
  - apply signed_bound_loaded_framed_progress; assumption.
Defined.
Print Assumptions signed_bound_loaded_framed_progress.
Print Assumptions signed_bound_initialized_framed_progress.
Print Assumptions signed_bound_initialized_region_progress.
