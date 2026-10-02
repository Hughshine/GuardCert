From Stdlib Require Import List Bool ZArith Arith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightFiniteRegion ClightCountedLoop
  ClightCondition ClightPureExpr.
Import ListNotations.
Set Implicit Arguments.

(** The first loop protocol accepts a strict signed counter and a silent body
    that changes memory only. Invalid memory accesses can still get stuck;
    progress here excludes infinite internal stuttering, not stuckness. *)
Fixpoint memory_body (s : statement) : bool :=
  match s with
  | Sskip | Sassign _ _ => true
  | Ssequence l r | Sifthenelse _ l r => memory_body l && memory_body r
  | _ => false
  end.

Lemma memory_body_finite s : memory_body s = true -> finite_statement s = true.
Proof.
  induction s; simpl; try discriminate; auto;
    rewrite !andb_true_iff; intros [L R]; split; auto.
Qed.

Lemma memory_body_step ge locals code stack le m code' stack' le' m' :
  fragment_step ge locals code stack le m code' stack' le' m' ->
  memory_body code = true -> Forall (fun s => memory_body s = true) stack ->
  le' = le /\ memory_body code' = true /\
    Forall (fun s => memory_body s = true) stack'.
Proof.
  intros MOVE BODY STACK; inversion MOVE; subst; simpl in BODY; try discriminate.
  - auto.
  - apply andb_true_iff in BODY as [L R]; auto.
  - inversion STACK; subst; auto.
  - apply andb_true_iff in BODY as [L R]; destruct b; auto.
Qed.

Definition counter_remaining iterator bound (le : temp_env) : nat :=
  match le ! iterator, le ! bound with
  | Some (Vint x), Some (Vint upper) => Z.to_nat (Int.signed upper - Int.signed x)
  | _, _ => 0
  end.

Definition counter_active iterator bound (le : temp_env) : Prop :=
  exists x upper, le ! iterator = Some (Vint x) /\ le ! bound = Some (Vint upper) /\
    (Int.signed x < Int.signed upper)%Z.

Definition increment_temps iterator (le : temp_env) : temp_env :=
  match le ! iterator with
  | Some (Vint x) => PTree.set iterator (Vint (Int.add x Int.one)) le
  | _ => le
  end.

Lemma counter_active_positive iterator bound le : counter_active iterator bound le ->
  (0 < counter_remaining iterator bound le)%nat.
Proof.
  intros [x [upper [X [UP LT]]]]. unfold counter_remaining; rewrite X, UP.
  pose proof (Z2Nat.id (Int.signed upper - Int.signed x) ltac:(lia)); lia.
Qed.

Lemma counter_increment_distance iterator bound le : iterator <> bound ->
  counter_active iterator bound le ->
  counter_remaining iterator bound le = S (counter_remaining iterator bound (increment_temps iterator le)).
Proof.
  intros DISTINCT [x [upper [X [UP LT]]]].
  unfold increment_temps, counter_remaining; rewrite X, UP, PTree.gss,
    PTree.gso by congruence. rewrite UP, Int.add_signed.
  change (Int.signed Int.one) with 1%Z.
  rewrite Int.signed_repr by (pose proof (Int.signed_range x);
    pose proof (Int.signed_range upper); lia).
  rewrite <- Z2Nat.inj_succ by lia. f_equal; lia.
Qed.

Lemma counter_increment_evaluation ge locals iterator bound le m :
  counter_active iterator bound le ->
  exists v, eval_expr ge locals le m
    (Ebinop Oadd (Etempvar iterator type_int32s) (Econst_int Int.one type_int32s) type_int32s) v /\
    PTree.set iterator v le = increment_temps iterator le.
Proof.
  intros [x [upper [X [UP LT]]]]. exists (Vint (Int.add x Int.one)); split.
  - eapply eval_Ebinop; [constructor; exact X | constructor | reflexivity].
  - unfold increment_temps; rewrite X; reflexivity.
Qed.

Lemma counter_increment_normal fe ge locals iterator bound le m :
  counter_active iterator bound le ->
  exec_stmt fe ge locals le m (counter_increment iterator) E0
    (increment_temps iterator le) m Out_normal.
Proof.
  intro ACTIVE. destruct (@counter_increment_evaluation ge locals iterator bound le m ACTIVE)
    as [v [EVAL TEMPS]]. rewrite <- TEMPS. constructor; exact EVAL.
Qed.

Lemma counter_condition_active ge locals le m iterator bound :
  expression_test (counter_condition iterator bound)
    (Entry ge locals le m) true -> counter_active iterator bound le.
Proof.
  intros [v [EVAL BOOL]]. cbn [entry_ge entry_env entry_temps entry_memory
    counter_condition] in EVAL, BOOL.
  inversion EVAL; subst;
    try match goal with LV : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion LV end.
  match goal with
  | LEFT : eval_expr _ _ _ _ (Etempvar iterator _) ?vx,
    RIGHT : eval_expr _ _ _ _ (Etempvar bound _) ?vu |- _ =>
      inversion LEFT; inversion RIGHT; subst
  end;
    try match goal with LV : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion LV end.
  match goal with SEM : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    rename SEM into OP
  end.
  destruct v1; destruct v2; try discriminate OP.
  change (Some (Val.of_bool (Int.lt i i0)) = Some v) in OP.
  inversion OP; subst.
  match goal with X : le ! iterator = Some (Vint ?x), UP : le ! bound = Some (Vint ?u) |- _ =>
    exists x, u; split; [exact X | split; [exact UP |]]
  end.
  unfold Int.lt in BOOL. destruct (zlt _ _) as [LT|GE]; [exact LT | discriminate BOOL].
Qed.

Print Assumptions counter_increment_distance.
Print Assumptions counter_condition_active.

Section LOOP_PROTOCOL.
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

Definition loop_header := Sifthenelse (counter_condition iterator bound) body Sbreak.
Definition loop_increment := counter_increment iterator.
Definition loop_code := counted_loop iterator bound body.
Definition loop_stride := statement_weight body + 5.

Inductive loop_cursor : Type :=
| lp_start (le : temp_env) (m : mem)
| lp_header (le : temp_env) (m : mem)
| lp_body (code : statement) (stack : list statement) (le : temp_env) (m : mem)
    (CODE : memory_body code = true)
    (STACK : Forall (fun s => memory_body s = true) stack)
    (ACTIVE : counter_active iterator bound le)
| lp_increment (le : temp_env) (m : mem) (ACTIVE : counter_active iterator bound le)
| lp_latch (le : temp_env) (m : mem)
| lp_break (le : temp_env) (m : mem)
| lp_done (le : temp_env) (m : mem).

Definition loop_cursor_state c : state :=
  match c with
  | lp_start le m => State fn loop_code outside locals le m
  | lp_header le m => State fn loop_header (Kloop1 loop_header loop_increment outside) locals le m
  | @lp_body code stack le m _ _ _ =>
      State fn code (region_cont stack (Kloop1 loop_header loop_increment outside)) locals le m
  | @lp_increment le m _ => State fn loop_increment (Kloop2 loop_header loop_increment outside) locals le m
  | lp_latch le m => State fn Sskip (Kloop2 loop_header loop_increment outside) locals le m
  | lp_break le m => State fn Sbreak (Kloop1 loop_header loop_increment outside) locals le m
  | lp_done le m => State fn Sskip outside locals le m
  end.

Definition loop_cursor_rank c : nat :=
  match c with
  | lp_start le _ => counter_remaining iterator bound le * loop_stride + 3
  | lp_header le _ => counter_remaining iterator bound le * loop_stride + 2
  | @lp_body code stack le m _ _ _ =>
      Nat.pred (counter_remaining iterator bound le) * loop_stride +
        state_weight (State fn code (region_cont stack Kstop) locals le m) + 6
  | @lp_increment le _ _ => Nat.pred (counter_remaining iterator bound le) * loop_stride + 5
  | lp_latch le _ => counter_remaining iterator bound le * loop_stride + 4
  | lp_break _ _ => 1
  | lp_done _ _ => 0
  end.

Definition loop_cursor_done c : option (temp_env * mem) :=
  match c with lp_done le m => Some (le, m) | _ => None end.

Inductive loop_cursor_step : loop_cursor -> loop_cursor -> Prop :=
| lp_step_start : forall le m,
    loop_cursor_step (lp_start le m) (lp_header le m)
| lp_step_true : forall le m ACTIVE,
    expression_test (counter_condition iterator bound) (Entry ge locals le m) true ->
    loop_cursor_step (lp_header le m) (@lp_body body [] le m BODY (Forall_nil _) ACTIVE)
| lp_step_false : forall le m,
    expression_test (counter_condition iterator bound) (Entry ge locals le m) false ->
    loop_cursor_step (lp_header le m) (lp_break le m)
| lp_step_body : forall code stack le m code' stack' m' CODE STACK CODE' STACK' ACTIVE,
    fragment_step ge locals code stack le m code' stack' le m' ->
    loop_cursor_step (@lp_body code stack le m CODE STACK ACTIVE)
      (@lp_body code' stack' le m' CODE' STACK' ACTIVE)
| lp_step_body_done : forall le m CODE STACK ACTIVE,
    loop_cursor_step (@lp_body Sskip [] le m CODE STACK ACTIVE) (@lp_increment le m ACTIVE)
| lp_step_increment : forall le m ACTIVE,
    loop_cursor_step (@lp_increment le m ACTIVE) (lp_latch (increment_temps iterator le) m)
| lp_step_latch : forall le m,
    loop_cursor_step (lp_latch le m) (lp_start le m)
| lp_step_break : forall le m,
    loop_cursor_step (lp_break le m) (lp_done le m).

Lemma loop_step_sound c n : loop_cursor_step c n ->
  step ge (fe ge) (loop_cursor_state c) E0 (loop_cursor_state n).
Proof.
  intro MOVE; inversion MOVE; subst; cbn [loop_cursor_state].
  - constructor.
  - destruct H as [v [EVAL BOOL]]. eapply step_ifthenelse with (b := true); eauto.
  - destruct H as [v [EVAL BOOL]]. eapply step_ifthenelse with (b := false); eauto.
  - inversion H; subst; try discriminate CODE; cbn [region_cont];
      [eapply step_assign | apply step_seq |
       apply step_skip_seq | eapply step_ifthenelse]; eauto.
  - apply step_skip_or_continue_loop1; left; reflexivity.
  - destruct (@counter_increment_evaluation ge locals iterator bound le m ACTIVE)
      as [v [EVAL TEMPS]]. rewrite <- TEMPS. constructor; exact EVAL.
  - constructor.
  - constructor.
Qed.

Lemma loop_step_active c n : loop_cursor_step c n -> loop_cursor_done c = None.
Proof. intro MOVE; inversion MOVE; reflexivity. Qed.

Lemma loop_step_decreases c n : loop_cursor_step c n -> loop_cursor_rank n < loop_cursor_rank c.
Proof.
  intro MOVE; inversion MOVE; subst; cbn [loop_cursor_rank]; try lia.
  - pose proof (@counter_active_positive iterator bound le ACTIVE) as POS.
    unfold loop_stride; cbn [state_weight region_cont continuation_weight].
    destruct (counter_remaining iterator bound le); [lia |]. simpl; nia.
  - pose proof (@fragment_step_decreases ge locals code stack le m code' stack' le m' H fn Kstop).
    lia.
  - rewrite (@counter_increment_distance iterator bound le DISTINCT ACTIVE); simpl; lia.
Qed.

Lemma loop_step_closed c events next_state : loop_cursor_done c = None ->
  step ge (fe ge) (loop_cursor_state c) events next_state ->
  exists n, events = E0 /\ next_state = loop_cursor_state n /\ loop_cursor_step c n.
Proof.
  destruct c; cbn [loop_cursor_state loop_cursor_done]; intros DONE STEP.
  - inversion STEP; subst; try discriminate;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (lp_header le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    assert (TEST : expression_test (counter_condition iterator bound) (Entry ge locals le m) b)
      by (eexists; split; eassumption).
    destruct b.
    + pose proof (@counter_condition_active ge locals le m iterator bound TEST) as ACTIVE.
      exists (@lp_body body [] le m BODY (Forall_nil _) ACTIVE); repeat split; auto.
      constructor; exact TEST.
    + exists (lp_break le m); repeat split; auto. constructor; exact TEST.
  - destruct code; try (exfalso; discriminate CODE).
    { destruct stack as [|next rest].
      * simpl in STEP. inversion STEP; subst; try contradiction;
          try match goal with BAD : is_call_cont (Kloop1 _ _ _) |- _ => contradiction end;
          try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
        exists (@lp_increment le m ACTIVE); repeat split; try reflexivity.
        constructor.
      * assert (FIN : finite_statement Sskip = true) by reflexivity.
        assert (FSTACK : Forall (fun s => finite_statement s = true) (next :: rest))
          by (eapply Forall_impl; [intros s M; apply memory_body_finite; exact M | exact STACK]).
        assert (ACTIVE_STACK : Sskip <> Sskip \/ (next :: rest) <> [])
          by (right; discriminate).
        destruct (@fragment_step_from_ambient fe ge locals fn Sskip (next :: rest)
          (Kloop1 loop_header loop_increment outside) le m events next_state FIN FSTACK
          ACTIVE_STACK STEP)
          as [code' [stack' [le' [m' [TRACE [STATE MOVE]]]]]].
        destruct (@memory_body_step ge locals Sskip (next :: rest) le m code' stack' le' m'
          MOVE CODE STACK) as [TEMPS [CODE' STACK']]; subst le'.
        exists (@lp_body code' stack' le m' CODE' STACK' ACTIVE); repeat split; auto.
        constructor; exact MOVE.
    }
    all: pose proof (memory_body_finite _ CODE) as FIN;
      assert (FSTACK : Forall (fun s => finite_statement s = true) stack)
        by (eapply Forall_impl; [intros s M; apply memory_body_finite; exact M | exact STACK]);
      match type of CODE with memory_body ?code = true =>
        assert (ACTIVE_CODE : code <> Sskip \/ stack <> []) by (left; discriminate)
      end;
      destruct (@fragment_step_from_ambient fe ge locals fn _ stack
        (Kloop1 loop_header loop_increment outside) le m events next_state FIN FSTACK
        ACTIVE_CODE STEP)
        as [code' [stack' [le' [m' [TRACE [STATE MOVE]]]]]];
      destruct (@memory_body_step ge locals _ stack le m code' stack' le' m' MOVE CODE STACK)
        as [TEMPS [CODE' STACK']]; subst le';
      exists (@lp_body code' stack' le m' CODE' STACK' ACTIVE); repeat split; auto;
      constructor; exact MOVE.
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
    exists (lp_latch (increment_temps iterator le) m); split; [reflexivity | split].
    + cbn [loop_cursor_state]; rewrite TEMPS; reflexivity.
    + constructor.
  - inversion STEP; subst; try contradiction;
      try match goal with BAD : is_call_cont (Kloop2 _ _ _) |- _ => contradiction end.
    exists (lp_start le m); repeat split; constructor.
  - inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    exists (lp_done le m); repeat split; constructor.
  - discriminate DONE.
Qed.

Definition loop_run le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m loop_code E0 (fst result) (snd result) Out_normal.

Definition increment_tail le m (result : temp_env * mem) : Prop :=
  exists le1 m1, exec_stmt fe ge locals le m loop_increment E0 le1 m1 Out_normal /\
    loop_run le1 m1 result.

Definition header_completion le m (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals le m loop_header E0 (fst result) (snd result) Out_break \/
  exists le1 m1, exec_stmt fe ge locals le m loop_header E0 le1 m1 Out_normal /\
    increment_tail le1 m1 result.

Definition loop_cursor_completion c (result : temp_env * mem) : Prop :=
  match c with
  | lp_start le m | lp_latch le m => loop_run le m result
  | lp_header le m => header_completion le m result
  | @lp_body code stack le m _ _ _ => exists le1 m1,
      resumed_execution fe ge locals code stack le m le1 m1 /\ increment_tail le1 m1 result
  | @lp_increment le m _ => increment_tail le m result
  | lp_break le m | lp_done le m => result = (le, m)
  end.

Lemma loop_completion_prepend c n result : loop_cursor_step c n ->
  loop_cursor_completion n result -> loop_cursor_completion c result.
Proof.
  intros MOVE RUN; inversion MOVE; subst; cbn [loop_cursor_completion] in RUN |- *.
  - destruct RUN as [STOP | [le1 [m1 [HEADER [le2 [m2 [INC TAIL]]]]]]]; unfold loop_run.
    + eapply exec_Sloop_stop1 with (out' := Out_break); [exact STOP | constructor].
    + eapply exec_Sloop_loop with (out1 := Out_normal)
        (t1 := E0) (t2 := E0) (t3 := E0);
        [exact HEADER | constructor | exact INC | exact TAIL].
  - destruct RUN as [le1 [m1 [RUN TAIL]]].
    right; exists le1, m1; split; [|exact TAIL].
    destruct H as [v [EVAL BOOL]]. eapply exec_Sifthenelse with (b := true); eauto.
    apply initial_execution in RUN; exact RUN.
  - subst result; left. destruct H as [v [EVAL BOOL]].
    eapply exec_Sifthenelse with (b := false); eauto. constructor.
  - destruct RUN as [le1 [m1 [RUN TAIL]]]. exists le1, m1; split; [|exact TAIL].
    eapply fragment_step_prepend; eauto.
  - exists le, m; split; [apply completed_execution | exact RUN].
  - exists (increment_temps iterator le), m; split;
      [apply counter_increment_normal with (bound := bound); exact ACTIVE | exact RUN].
  - exact RUN.
  - exact RUN.
Qed.

Definition loop_exit_state (result : temp_env * mem) : state :=
  State fn Sskip outside locals (fst result) (snd result).

Lemma loop_done_state c result : loop_cursor_done c = Some result ->
  loop_cursor_state c = loop_exit_state result.
Proof. destruct c; cbn [loop_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.

Lemma loop_done_completion c result : loop_cursor_done c = Some result ->
  loop_cursor_completion c result.
Proof. destruct c; cbn [loop_cursor_done]; try discriminate; intro DONE; inversion DONE; reflexivity. Qed.

Definition counted_region_protocol :
  silent_protocol state event (temp_env * mem) (step ge (fe ge)) loop_exit_state :=
  {| cursor := loop_cursor;
     cursor_state := loop_cursor_state;
     cursor_rank := loop_cursor_rank;
     cursor_done := loop_cursor_done;
     cursor_completion := loop_cursor_completion;
     cursor_step := loop_cursor_step;
     cursor_step_sound := loop_step_sound;
     cursor_step_active := loop_step_active;
     cursor_step_decreases := loop_step_decreases;
     cursor_step_closed := loop_step_closed;
     cursor_completion_prepend := loop_completion_prepend;
     cursor_done_state := loop_done_state;
     cursor_done_completion := loop_done_completion |}.

Definition counted_entry_state (input : temp_env * mem) : state :=
  State fn loop_code outside locals (fst input) (snd input).

Definition counted_entry_result (input result : temp_env * mem) : Prop :=
  loop_run (fst input) (snd input) result.

Definition counted_region_entry : protocol_entry counted_region_protocol
  (temp_env * mem) counted_entry_state counted_entry_result.
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (step ge (fe ge)) loop_exit_state
    counted_region_protocol (temp_env * mem) counted_entry_state counted_entry_result
    (fun input => lp_start (fst input) (snd input)) _ _); intros; auto.
Defined.

Theorem counted_region_cannot_diverge c : ~ cursor_infinite counted_region_protocol c.
Proof. apply cursor_cannot_diverge. Qed.

Theorem counted_region_completed input length final result :
  cursor_path counted_region_protocol (lp_start (fst input) (snd input)) length final ->
  loop_cursor_done final = Some result ->
  exec_stmt fe ge locals (fst input) (snd input) loop_code
    E0 (fst result) (snd result) Out_normal /\
  length <= counter_remaining iterator bound (fst input) * loop_stride + 3.
Proof. apply (completed_entry counted_region_entry). Qed.
End LOOP_PROTOCOL.

Print Assumptions loop_step_closed.
Print Assumptions counted_region_cannot_diverge.
Print Assumptions counted_region_completed.
