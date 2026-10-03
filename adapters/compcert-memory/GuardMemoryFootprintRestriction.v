From Stdlib Require Import List Bool.
From compcert.common Require Import Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace.
Import ListNotations.
Set Implicit Arguments.

(** A multi-object view can retain only actual source cells. Its separation
    obligation then concerns those cells, rather than every address in a
    presumed allocation. The language instance must separately prove that
    checking these addresses is defined at the guard entry. *)
Definition memory_restrict_locations (allowed : MemCell -> bool) (locations : cell_locations) : cell_locations :=
  fun cell => if allowed cell then locations cell else None.
Definition memory_locations_separated_on (allowed : MemCell -> bool) (locations : cell_locations) :=
  forall first second first_location second_location,
    allowed first = true -> allowed second = true ->
    locations first = Some first_location -> locations second = Some second_location ->
    cell_neq first second -> location_disjoint first_location second_location.
Lemma memory_restrict_location_inverse allowed locations cell location :
  memory_restrict_locations allowed locations cell = Some location ->
  allowed cell = true /\ locations cell = Some location.
Proof.
  unfold memory_restrict_locations; destruct (allowed cell) eqn:ALLOWED;
    [intro RESOLVE; split; [reflexivity|exact RESOLVE]|discriminate].
Qed.
Theorem memory_restricted_locations_nonalias allowed locations :
  memory_locations_separated_on allowed locations ->
  locations_nonalias (memory_restrict_locations allowed locations).
Proof.
  intros SEPARATED first second first_location second_location FIRST SECOND DIFFERENT.
  apply memory_restrict_location_inverse in FIRST as [FIRST_ALLOWED FIRST].
  apply memory_restrict_location_inverse in SECOND as [SECOND_ALLOWED SECOND].
  exact (@SEPARATED first second first_location second_location FIRST_ALLOWED SECOND_ALLOWED FIRST SECOND DIFFERENT).
Qed.
Lemma memory_restrict_resolve_cells allowed locations cells :
  Forall (fun cell => allowed cell = true) cells ->
  resolve_cells cells (memory_restrict_locations allowed locations) = resolve_cells cells locations.
Proof.
  intro COVERED; induction COVERED; cbn [resolve_cells]; [reflexivity|].
  unfold memory_restrict_locations at 1; rewrite H,IHCOVERED; reflexivity.
Qed.
Definition memory_instruction_cells_covered allowed instruction parameters :=
  allowed (exact_cell (instruction_write instruction) parameters) = true /\
  Forall (fun cell => allowed cell = true)
    (map (fun access => exact_cell access parameters) (instruction_reads instruction)).
Theorem memory_restrict_instruction_semantics allowed locations instruction parameters writes reads before after :
  memory_instruction_cells_covered allowed instruction parameters ->
  (GuardMemoryInstr.instr_semantics instruction parameters writes reads
    (RuntimeState locations before) (RuntimeState locations after) <->
   GuardMemoryInstr.instr_semantics instruction parameters writes reads
    (RuntimeState (memory_restrict_locations allowed locations) before)
    (RuntimeState (memory_restrict_locations allowed locations) after)).
Proof.
  intros [WRITE READS]; unfold GuardMemoryInstr.instr_semantics,footprint_run; cbn.
  split.
  - intros [WRITES [READ_CELLS RUN]]; split; [exact WRITES|]; split; [exact READ_CELLS|].
    subst reads; destruct RUN as [write [loaded [RESOLVE [LOADS [FRAME ACTION]]]]].
    exists write,loaded; split.
    + unfold memory_restrict_locations; rewrite WRITE; exact RESOLVE.
    + split; [rewrite memory_restrict_resolve_cells by exact READS; exact LOADS|].
      split; [reflexivity|exact ACTION].
  - intros [WRITES [READ_CELLS RUN]]; split; [exact WRITES|]; split; [exact READ_CELLS|].
    subst reads; destruct RUN as [write [loaded [RESOLVE [LOADS [FRAME ACTION]]]]].
    exists write,loaded; split.
    + unfold memory_restrict_locations in RESOLVE; rewrite WRITE in RESOLVE; exact RESOLVE.
    + split; [rewrite memory_restrict_resolve_cells in LOADS by exact READS; exact LOADS|].
      split; [reflexivity|exact ACTION].

Qed.
Definition memory_restrict_state allowed state :=
  RuntimeState (memory_restrict_locations allowed (runtime_locations state)) (runtime_memory state).
Lemma memory_restrict_event_step allowed event before after :
  memory_instruction_cells_covered allowed (event_instruction event) (event_arguments event) ->
  memory_event_step event before after ->
  memory_event_step event (memory_restrict_state allowed before) (memory_restrict_state allowed after).
Proof.
  intros COVERED [writes [reads RUN]].
  assert (FRAME : runtime_locations after = runtime_locations before).
  { destruct RUN as [_ [_ [write [loaded [_ [_ [FRAME ACTION]]]]]]]; exact FRAME. }
  destruct before as [locations before]; destruct after as [target after]; cbn in FRAME; subst target.
  exists writes,reads; apply (proj1 (@memory_restrict_instruction_semantics allowed locations
    (event_instruction event) (event_arguments event) writes reads before after COVERED)); exact RUN.
Qed.
Theorem memory_restrict_trace_execution allowed events before after :
  Forall (fun event => memory_instruction_cells_covered allowed (event_instruction event) (event_arguments event)) events ->
  Iter.iter_semantics memory_event_step events before after ->
  Iter.iter_semantics memory_event_step events (memory_restrict_state allowed before) (memory_restrict_state allowed after).
Proof.
  intros COVERED RUN; revert COVERED; induction RUN; intro COVERED.
  - constructor.
  - inversion COVERED; subst; econstructor.
    + eapply memory_restrict_event_step; eassumption.
    + apply IHRUN; assumption.
Qed.
Definition memory_loop_cells_covered allowed loop parameters :=
  Forall (fun event => memory_instruction_cells_covered allowed (event_instruction event) (event_arguments event))
    (memory_loop_trace loop parameters).
Theorem memory_restrict_loop_execution allowed loop parameters before after :
  memory_loop_cells_covered allowed loop parameters ->
  L.loop_semantics loop parameters before after ->
  L.loop_semantics loop parameters (memory_restrict_state allowed before) (memory_restrict_state allowed after).
Proof.
  intros COVERED RUN; apply memory_loop_trace_correct.
  eapply memory_restrict_trace_execution; [exact COVERED|apply memory_loop_trace_correct; exact RUN].
Qed.
Lemma memory_unrestrict_resolve_cells allowed locations cells resolved :
  resolve_cells cells (memory_restrict_locations allowed locations) = Some resolved ->
  resolve_cells cells locations = Some resolved.
Proof.
  revert resolved; induction cells as [|cell cells IH]; intros resolved RESOLVE; [exact RESOLVE|].
  cbn [resolve_cells] in RESOLVE; destruct (memory_restrict_locations allowed locations cell)
    as [location|] eqn:LOCATION; [|discriminate].
  destruct (resolve_cells cells (memory_restrict_locations allowed locations))
    as [rest|] eqn:REST; [|discriminate].
  apply memory_restrict_location_inverse in LOCATION as [ALLOWED LOCATION].
  inversion RESOLVE; subst resolved; cbn [resolve_cells]; rewrite LOCATION.
  rewrite (IH rest eq_refl); reflexivity.
Qed.
(** A successful candidate in the restricted view can always be executed in
    the original view. Its successful address resolutions already establish
    coverage, so the caller need not supply another candidate footprint proof. *)
Theorem memory_unrestrict_instruction_semantics allowed locations instruction parameters writes reads before after :
  GuardMemoryInstr.instr_semantics instruction parameters writes reads
    (RuntimeState (memory_restrict_locations allowed locations) before)
    (RuntimeState (memory_restrict_locations allowed locations) after) ->
  GuardMemoryInstr.instr_semantics instruction parameters writes reads
    (RuntimeState locations before) (RuntimeState locations after).
Proof.
  intros [WRITES [READ_CELLS [write [loaded [WRITE [READS [FRAME RUN]]]]]]].
  split; [exact WRITES|]; split; [exact READ_CELLS|].
  exists write,loaded; split.
  - apply memory_restrict_location_inverse in WRITE as [ALLOWED WRITE]; exact WRITE.
  - split; [eapply memory_unrestrict_resolve_cells; exact READS|]; split; [reflexivity|exact RUN].
Qed.
Theorem memory_unrestrict_trace_execution allowed locations events before after :
  Iter.iter_semantics memory_event_step events
    (RuntimeState (memory_restrict_locations allowed locations) before)
    (RuntimeState (memory_restrict_locations allowed locations) after) ->
  Iter.iter_semantics memory_event_step events (RuntimeState locations before) (RuntimeState locations after).
Proof.
  revert before after; induction events as [|event events IH]; intros before after RUN; inversion RUN; subst.
  - constructor.
  - match goal with STEP : memory_event_step event _ ?middle |- _ =>
      destruct middle as [middle_locations middle];
      destruct STEP as [writes [reads EVENT]];
      assert (FRAME : middle_locations = memory_restrict_locations allowed locations)
        by (destruct EVENT as [_ [_ [write [loaded [_ [_ [FRAME ACTION]]]]]]]; exact FRAME);
      subst middle_locations
    end.
    econstructor.
    + exists writes,reads; eapply memory_unrestrict_instruction_semantics; exact EVENT.
    + apply IH; assumption.
Qed.
Theorem memory_unrestrict_loop_execution allowed locations loop parameters before after :
  L.loop_semantics loop parameters
    (RuntimeState (memory_restrict_locations allowed locations) before)
    (RuntimeState (memory_restrict_locations allowed locations) after) ->
  L.loop_semantics loop parameters (RuntimeState locations before) (RuntimeState locations after).
Proof.
  intro RUN; apply memory_loop_trace_correct; eapply memory_unrestrict_trace_execution;
    apply memory_loop_trace_correct; exact RUN.
Qed.
Print Assumptions memory_restricted_locations_nonalias.
Print Assumptions memory_restrict_instruction_semantics.
Print Assumptions memory_restrict_loop_execution.
Print Assumptions memory_unrestrict_loop_execution.
