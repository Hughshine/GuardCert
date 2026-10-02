From Stdlib Require Import List Arith Lia Wellfounded.
Import ListNotations.
Set Implicit Arguments.

(** The kernel sees an opaque step relation, exits and progress properties.
    Language instances describe their internal cursors and completion meaning. *)
Record silent_protocol (State Event Exit : Type)
  (step : State -> list Event -> State -> Prop) (exit_state : Exit -> State) := SilentProtocol {
  cursor : Type;
  cursor_state : cursor -> State;
  cursor_rank : cursor -> nat;
  cursor_done : cursor -> option Exit;
  cursor_completion : cursor -> Exit -> Prop;
  cursor_step : cursor -> cursor -> Prop;
  cursor_step_sound : forall current next, cursor_step current next ->
    step (cursor_state current) [] (cursor_state next);
  cursor_step_active : forall current next, cursor_step current next -> cursor_done current = None;
  cursor_step_decreases : forall current next, cursor_step current next -> cursor_rank next < cursor_rank current;
  cursor_step_closed : forall current events next_state,
    cursor_done current = None -> step (cursor_state current) events next_state ->
    exists next, events = [] /\ next_state = cursor_state next /\ cursor_step current next;
  cursor_completion_prepend : forall current next result,
    cursor_step current next -> cursor_completion next result -> cursor_completion current result;
  cursor_done_state : forall current result,
    cursor_done current = Some result -> cursor_state current = exit_state result;
  cursor_done_completion : forall current result,
    cursor_done current = Some result -> cursor_completion current result
}.
Arguments silent_protocol State Event Exit step exit_state : clear implicits.

Section PROTOCOL.
Context {State Event Exit} {step : State -> list Event -> State -> Prop} {exit_state : Exit -> State}.
Variable P : silent_protocol State Event Exit step exit_state.

Inductive cursor_path : cursor P -> nat -> cursor P -> Prop :=
| cursor_path_nil : forall current, cursor_path current 0 current
| cursor_path_cons : forall current middle final length,
    cursor_step P current middle -> cursor_path middle length final ->
    cursor_path current (S length) final.

Lemma cursor_path_bound current length final : cursor_path current length final ->
  length + cursor_rank P final <= cursor_rank P current.
Proof.
  intro PATH; induction PATH; [lia |].
  pose proof (cursor_step_decreases P _ _ H); lia.
Qed.

Lemma cursor_path_completion current length final result :
  cursor_path current length final -> cursor_done P final = Some result ->
  cursor_completion P current result.
Proof.
  intros PATH DONE; induction PATH; [eapply cursor_done_completion; eauto |].
  eapply cursor_completion_prepend; eauto.
Qed.

CoInductive cursor_infinite : cursor P -> Prop :=
| cursor_infinite_cons : forall current next,
    cursor_step P current next -> cursor_infinite next -> cursor_infinite current.

Theorem cursor_cannot_diverge current : ~ cursor_infinite current.
Proof.
  remember (cursor_rank P current) as fuel eqn:RANK.
  revert current RANK; induction fuel using lt_wf_ind; intros current RANK INFINITE.
  inversion INFINITE; subst.
  match goal with NEXT : cursor_step P current ?next, TAIL : cursor_infinite ?next |- _ =>
    eapply (H (cursor_rank P next));
      [pose proof (cursor_step_decreases P _ _ NEXT); lia | reflexivity | exact TAIL]
  end.
Qed.

Theorem done_or_silent_advance current :
  (exists result, cursor_done P current = Some result /\
    cursor_state P current = exit_state result /\ cursor_completion P current result) \/
  (cursor_done P current = None /\ forall events next_state,
    step (cursor_state P current) events next_state ->
    exists next, events = [] /\ next_state = cursor_state P next /\
      cursor_step P current next /\ cursor_rank P next < cursor_rank P current).
Proof.
  destruct (cursor_done P current) as [result|] eqn:DONE.
  - left; exists result; split; [reflexivity | split];
      eauto using cursor_done_state, cursor_done_completion.
  - right; split; [reflexivity |]. intros events next_state STEP.
    destruct (cursor_step_closed P _ _ _ DONE STEP) as [next [EVENTS [STATE ADVANCE]]].
    exists next; repeat split; auto. eapply cursor_step_decreases; eauto.
Qed.
End PROTOCOL.

Record protocol_entry {State Event Exit step exit_state}
  (P : silent_protocol State Event Exit step exit_state) (Input : Type)
  (entry_state : Input -> State) (entry_result : Input -> Exit -> Prop) := ProtocolEntry {
  begin_cursor : Input -> cursor P;
  begin_state : forall input, cursor_state P (begin_cursor input) = entry_state input;
  begin_completion : forall input result,
    cursor_completion P (begin_cursor input) result -> entry_result input result
}.
Arguments protocol_entry {State Event Exit step exit_state} P Input entry_state entry_result.

Theorem completed_entry {State Event Exit step exit_state}
  (P : silent_protocol State Event Exit step exit_state) Input entry_state entry_result
  (E : protocol_entry P Input entry_state entry_result) input length final result :
  cursor_path P (begin_cursor E input) length final -> cursor_done P final = Some result ->
  entry_result input result /\ length <= cursor_rank P (begin_cursor E input).
Proof.
  intros PATH DONE; split.
  - eapply (begin_completion E). eapply cursor_path_completion; eauto.
  - pose proof (cursor_path_bound PATH); lia.
Qed.

Print Assumptions cursor_cannot_diverge.
Print Assumptions completed_entry.
