From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightProjectedExecution ClightGlobalScope ClightRegionProgress.
From GuardInterface Require Import ClightCheckPlanFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoublePolyhedral GuardMemoryLongControl
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleReductionNestSource GuardMemoryDoubleRectangularNestData
  GuardMemoryDoubleRectangularNestDecoder GuardMemoryDoubleRectangularNestSource GuardMemoryDoubleRectangularNestEntry
  GuardMemoryRectangularCapture GuardMemoryRectangularCaptureObservations.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint double_rectangular_capture_steps (axes : double_rectangular_axes) caches caps :
  option (list rectangular_capture_step) :=
  match axes,caches,caps with
  | [],[],[]=>Some []
  | (_,header)::axes,cache::caches,cap::caps=>
      match double_rectangular_capture_steps axes caches caps with
      | Some steps=>Some (RectangularCaptureStep header cache cap::steps)
      | None=>None end
  | _,_,_=>None end.
Theorem double_rectangular_capture_steps_sound axes : forall caches caps steps,
  double_rectangular_capture_steps axes caches caps=Some steps ->
  Forall2 (fun axis step => snd axis=rectangular_capture_header step) axes steps /\
  map rectangular_capture_cache steps=caches /\ map rectangular_capture_limit steps=caps.
Proof.
  induction axes as [|[iterator header] axes IH]; intros [|cache caches] [|cap caps] steps;
    cbn [double_rectangular_capture_steps]; try discriminate.
  - intro RUN; inversion RUN; subst steps; repeat split; constructor.
  - destruct (double_rectangular_capture_steps axes caches caps) as [tail|] eqn:TAIL; [|discriminate].
    intro RUN; inversion RUN; subst steps.
    destruct (@IH caches caps tail TAIL) as [LINK [CACHES CAPS]].
    cbn [map rectangular_capture_header rectangular_capture_cache rectangular_capture_limit]; split.
    + constructor; [reflexivity|exact LINK].
    + split; [rewrite CACHES|rewrite CAPS]; reflexivity.
Qed.
Lemma double_rectangular_capture_observation_links ge locals memory after
  (axes : double_rectangular_axes) steps observations :
  Forall2 (fun axis step => snd axis=rectangular_capture_header step) axes steps ->
  Forall2 (rectangular_capture_observation ge locals memory after) steps observations ->
  Forall2 (fun axis observation => snd axis=fst observation) axes observations /\
  Forall2 (fun cap observation => Z.of_nat (snd (snd observation))<=cap)
    (map rectangular_capture_limit steps) observations.
Proof.
  intro LINK; revert observations; induction LINK; intros observations OBSERVATIONS.
  - inversion OBSERVATIONS; split; constructor.
  - inversion OBSERVATIONS as [|step observation steps observations' FACT REST]; subst step steps observations.
    destruct (IHLINK observations' REST) as [TAIL CAPS]; cbn [map]; split; constructor.
    + unfold rectangular_capture_observation in FACT; destruct FACT as [HEADER _]; congruence.
    + exact TAIL.
    + unfold rectangular_capture_observation in FACT; tauto.
    + exact CAPS.
Qed.

Theorem checked_double_rectangular_capture_model p source description caps steps fe ge locals temps memory
  flag live after final :
  checked_double_rectangular_raw_nest p [] source=Some description ->
  double_rectangular_entry_bounds_check caps description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_rectangular_globals description) locals ->
  Forall2 (fun axis step => snd axis=rectangular_capture_header step) (rectangular_nest_axes description) steps ->
  map rectangular_capture_limit steps=caps -> NoDup (map rectangular_capture_cache steps) ->
  ~ In flag (map rectangular_capture_cache steps) ->
  (forall key, In key (statement_temps source++live) -> ~ In key (flag::map rectangular_capture_cache steps)) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists (accepted : bool) prepared prepared_after,
    exec_stmt fe ge locals temps memory (rectangular_capture_code steps flag) E0 prepared memory Out_normal /\
    prepared ! flag=Some (Vint (if accepted then Int.one else Int.zero)) /\
    temp_agree live temps prepared /\ exec_stmt fe ge locals prepared memory source E0 prepared_after final Out_normal /\
    temp_agree live after prepared_after /\
    (accepted=true -> exists observations,
      Forall2 (rectangular_capture_observation ge locals memory prepared) steps observations /\
      Forall2 (fun axis observation => snd axis=fst observation) (rectangular_nest_axes description) observations /\
      DoubleAssignmentIRs.Loop.loop_semantics (double_rectangular_pipeline_model description)
        (map (fun observation => Z.of_nat (snd (snd observation))) observations)
        (RuntimeState (global_double_locations ge (double_source_instruction_layouts (rectangular_nest_instruction description))) memory)
        (RuntimeState (global_double_locations ge (double_source_instruction_layouts (rectangular_nest_instruction description))) final) /\
      prepared_after=double_rectangular_nest_exit (double_rectangular_iterators (rectangular_nest_axes description))
        (map (fun observation => snd (snd observation)) observations) prepared).
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL LINK CAPS DISTINCT FLAG_FRESH PRIVATE SOURCE.
  pose proof (@double_rectangular_checked_caps caps description BOUNDS) as [_ CAP_RANGES].
  assert (LIMITS : Forall (fun step => 0<=rectangular_capture_limit step<=Int.max_signed) steps).
  { apply Forall_forall; intros step MEMBER.
    assert (CAP_MEMBER : In (rectangular_capture_limit step) caps)
      by (rewrite <- CAPS; apply in_map; exact MEMBER).
    apply Forall_forall with (x:=rectangular_capture_limit step) in CAP_RANGES; [|exact CAP_MEMBER].
    destruct CAP_RANGES as [POSITIVE MAXIMUM]; split; [lia|exact MAXIMUM]. }
  destruct (@checked_double_rectangular_raw_nest_sound p [] source description CHECK) as [_ [CANONICAL EQUIV]].
  destruct (@checked_double_rectangular_nest_sound p [] _ description CANONICAL) as [_ [LEAF _]].
  destruct (@rectangular_capture_source_licensed (rectangular_nest_axes description) steps flag
    (rectangular_nest_body description) fe ge locals temps temps memory after final
    (@checked_double_reduction_assignment_shape p _ _ _ LEAF) LINK
    (@checked_double_rectangular_entry_headers p [] source description ge locals CHECK GLOBAL LOCAL) LIMITS
    (proj1 (@EQUIV fe ge locals temps memory E0 after final Out_normal) SOURCE))
    as [prepared [accepted RECEIPT]].
  assert (FRAME : temp_agree (statement_temps source++live) temps prepared).
  { intros key MEMBER; eapply rectangular_capture_receipt_frame; [exact RECEIPT| |].
    - intro SAME; subst key; apply (PRIVATE flag MEMBER); left; reflexivity.
    - intro CACHE; apply (PRIVATE key MEMBER); right; exact CACHE. }
  destruct (@structured_execution_temp_transport fe ge locals temps memory source E0 after final Out_normal SOURCE
    (statement_temps source++live) prepared (statement_temps source)
    (@check_plan_frameable_writes source (@checked_double_rectangular_raw_frameable p [] source description CHECK))
    ltac:(unfold statement_scope; intros key MEMBER; apply in_or_app; left; exact MEMBER) FRAME)
    as [prepared_after [PREPARED EXIT]].
  exists accepted,prepared,prepared_after; split.
  - eapply rectangular_capture_receipt_execution; exact RECEIPT.
  - split; [eapply rectangular_capture_receipt_flag; exact RECEIPT|split].
    + eapply temp_agree_weaken; [intros key MEMBER; apply in_or_app; right; exact MEMBER|exact FRAME].
    + split; [exact PREPARED|split].
      * eapply temp_agree_weaken; [intros key MEMBER; apply in_or_app; right; exact MEMBER|exact EXIT].
      * intro ACCEPT; subst accepted.
        destruct (@rectangular_capture_accepted_observations ge locals memory flag steps temps prepared
          RECEIPT DISTINCT FLAG_FRESH) as [observations OBSERVATIONS].
        destruct (@double_rectangular_capture_observation_links ge locals memory prepared
          (rectangular_nest_axes description) steps observations LINK OBSERVATIONS) as [AXES COUNT_LIMITS].
        rewrite CAPS in COUNT_LIMITS.
        destruct (@rectangular_capture_observations_loads ge locals memory prepared steps observations OBSERVATIONS)
          as [LOADS BINDINGS].
        destruct (proj1 (@checked_double_rectangular_raw_pipeline_execution p source description caps fe ge locals
          observations prepared memory prepared_after final CHECK BOUNDS GLOBAL LOCAL BINDINGS AXES COUNT_LIMITS LOADS)
          PREPARED) as [MODEL SET].
        exists observations; repeat split; assumption.
Qed.

Print Assumptions double_rectangular_capture_steps_sound.
Print Assumptions double_rectangular_capture_observation_links.
Print Assumptions checked_double_rectangular_capture_model.
