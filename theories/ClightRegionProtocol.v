From Stdlib Require Import List Arith Lia.
From compcert.lib Require Import Maps.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Cop Clight ClightBigstep.
From Guard Require Import SilentRegionProtocol ClightFiniteRegion.
Import ListNotations.
Set Implicit Arguments.

(** A concrete language instance. The generic protocol does not inspect the
    Clight syntax, stores, temporaries or continuation used here. *)
Section INSTANCE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable fn : function.
Variable outside : cont.

Record finite_cursor := FiniteCursor {
  fc_statement : statement;
  fc_stack : list statement;
  fc_temps : temp_env;
  fc_memory : mem;
  fc_finite : finite_statement fc_statement = true;
  fc_stack_finite : Forall (fun s => finite_statement s = true) fc_stack
}.

Definition finite_cursor_state (c : finite_cursor) : state :=
  State fn (fc_statement c) (region_cont (fc_stack c) outside)
    locals (fc_temps c) (fc_memory c).

Definition finite_cursor_done (c : finite_cursor) : option (temp_env * mem) :=
  match fc_statement c, fc_stack c with
  | Sskip, [] => Some (fc_temps c, fc_memory c)
  | _, _ => None
  end.

Definition finite_cursor_step (c n : finite_cursor) : Prop :=
  fragment_step ge locals (fc_statement c) (fc_stack c) (fc_temps c) (fc_memory c)
    (fc_statement n) (fc_stack n) (fc_temps n) (fc_memory n).

Definition finite_cursor_completion (c : finite_cursor) (result : temp_env * mem) : Prop :=
  resumed_execution fe ge locals (fc_statement c) (fc_stack c)
    (fc_temps c) (fc_memory c) (fst result) (snd result).

Definition finite_exit_state (result : temp_env * mem) : state :=
  State fn Sskip outside locals (fst result) (snd result).

Lemma finite_step_sound c n : finite_cursor_step c n ->
  step ge (fe ge) (finite_cursor_state c) E0 (finite_cursor_state n).
Proof.
  unfold finite_cursor_step, finite_cursor_state; intro STEP.
  inversion STEP; subst; simpl; econstructor; eauto.
Qed.

Lemma finite_step_active c n : finite_cursor_step c n -> finite_cursor_done c = None.
Proof.
  destruct c as [code stack le m FIN STACK]; unfold finite_cursor_step, finite_cursor_done;
    simpl; intro STEP; inversion STEP; subst; reflexivity.
Qed.

Lemma finite_step_decreases c n : finite_cursor_step c n ->
  state_weight (finite_cursor_state n) < state_weight (finite_cursor_state c).
Proof.
  unfold finite_cursor_step, finite_cursor_state; intro STEP.
  eapply fragment_step_decreases; exact STEP.
Qed.

Lemma finite_step_closed c events next_state :
  finite_cursor_done c = None ->
  step ge (fe ge) (finite_cursor_state c) events next_state ->
  exists n, events = E0 /\ next_state = finite_cursor_state n /\ finite_cursor_step c n.
Proof.
  destruct c as [code stack le m FIN STACK]; cbn [finite_cursor_state].
  intros DONE STEP.
  assert (ACTIVE : code <> Sskip \/ stack <> []).
  { destruct code; try (left; discriminate).
    destruct stack; [discriminate DONE | right; discriminate]. }
  destruct (@fragment_step_from_ambient fe ge locals fn code stack outside le m
    events next_state FIN STACK ACTIVE STEP) as [code' [stack' [le' [m' [TRACE [STATE MOVE]]]]]].
  destruct (@fragment_step_finite ge locals code stack le m code' stack' le' m'
    MOVE FIN STACK) as [FIN' STACK'].
  exists (@FiniteCursor code' stack' le' m' FIN' STACK'); cbn.
  repeat split; auto.
Qed.

Lemma finite_completion_prepend c n result : finite_cursor_step c n ->
  finite_cursor_completion n result -> finite_cursor_completion c result.
Proof.
  unfold finite_cursor_step, finite_cursor_completion; intros STEP RUN.
  eapply fragment_step_prepend; eauto.
Qed.

Lemma finite_done_state c result : finite_cursor_done c = Some result ->
  finite_cursor_state c = finite_exit_state result.
Proof.
  destruct c as [code stack le m FIN STACK]; unfold finite_cursor_done; simpl.
  destruct code; destruct stack; try discriminate; intro DONE; inversion DONE; reflexivity.
Qed.

Lemma finite_done_completion c result : finite_cursor_done c = Some result ->
  finite_cursor_completion c result.
Proof.
  destruct c as [code stack le m FIN STACK]; unfold finite_cursor_done; simpl.
  destruct code; destruct stack; try discriminate; intro DONE; inversion DONE; subst.
  apply completed_execution.
Qed.

Definition finite_region_protocol :
  silent_protocol state event (temp_env * mem) (step ge (fe ge)) finite_exit_state :=
  {| cursor := finite_cursor;
     cursor_state := finite_cursor_state;
     cursor_rank := fun c => state_weight (finite_cursor_state c);
     cursor_done := finite_cursor_done;
     cursor_completion := finite_cursor_completion;
     cursor_step := finite_cursor_step;
     cursor_step_sound := finite_step_sound;
     cursor_step_active := finite_step_active;
     cursor_step_decreases := finite_step_decreases;
     cursor_step_closed := finite_step_closed;
     cursor_completion_prepend := finite_completion_prepend;
     cursor_done_state := finite_done_state;
     cursor_done_completion := finite_done_completion |}.

Record finite_input := FiniteInput {
  fi_statement : statement;
  fi_temps : temp_env;
  fi_memory : mem;
  fi_finite : finite_statement fi_statement = true
}.

Definition finite_begin (input : finite_input) : finite_cursor :=
  @FiniteCursor (fi_statement input) [] (fi_temps input) (fi_memory input)
    (fi_finite input) (Forall_nil _).

Definition finite_entry_state (input : finite_input) : state :=
  State fn (fi_statement input) outside locals (fi_temps input) (fi_memory input).

Definition finite_entry_result (input : finite_input) (result : temp_env * mem) : Prop :=
  exec_stmt fe ge locals (fi_temps input) (fi_memory input) (fi_statement input)
    E0 (fst result) (snd result) Out_normal.

Definition finite_region_entry :
  protocol_entry finite_region_protocol finite_input finite_entry_state finite_entry_result.
Proof.
  refine (@ProtocolEntry state event (temp_env * mem) (step ge (fe ge))
    finite_exit_state finite_region_protocol finite_input finite_entry_state
    finite_entry_result finite_begin _ _).
  - intro input; reflexivity.
  - intros input result RUN. eapply initial_execution; exact RUN.
Defined.

Theorem finite_region_cannot_diverge c :
  ~ cursor_infinite finite_region_protocol c.
Proof. apply cursor_cannot_diverge. Qed.

Theorem finite_region_completed input length final result :
  cursor_path finite_region_protocol (finite_begin input) length final ->
  finite_cursor_done final = Some result ->
  finite_entry_result input result /\
    length <= state_weight (finite_entry_state input).
Proof. apply (completed_entry finite_region_entry). Qed.
End INSTANCE.

Print Assumptions finite_region_cannot_diverge.
Print Assumptions finite_region_completed.
