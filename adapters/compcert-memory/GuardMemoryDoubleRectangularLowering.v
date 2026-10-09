From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightTempFootprint
  ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLongControl GuardMemoryDoubleLocations
  GuardMemoryDoubleNestedBackend GuardMemoryDoubleTensorBackend GuardMemoryDoublePolyhedral
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleRectangularNestData GuardMemoryDoubleRectangularNestDecoder
  GuardMemoryDoubleRectangularNestEntry GuardMemoryDoubleRectangularNestCapture GuardMemoryRectangularCapture
  GuardMemoryRectangularCaptureObservations GuardMemoryDoubleRectangularCandidate
  GuardMemoryDoubleRectangularPrepared GuardMemoryDoubleRectangularExitCode.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma double_rectangular_words_frame caches counts before after :
  Forall2 (fun cache count => 0<Z.of_nat count /\ signed_range (Z.of_nat count) /\
    before ! cache=Some (Vint (Int.repr (Z.of_nat count)))) caches counts ->
  temp_agree caches before after ->
  Forall2 (fun cache count => 0<Z.of_nat count /\ signed_range (Z.of_nat count) /\
    after ! cache=Some (Vint (Int.repr (Z.of_nat count)))) caches counts.
Proof.
  intro WORDS; induction WORDS; intro FRAME; constructor.
  - destruct H as [POSITIVE [RANGE WORD]]; split; [exact POSITIVE|split; [exact RANGE|]].
    rewrite (FRAME x ltac:(left; reflexivity)); exact WORD.
  - apply IHWORDS; intros key MEMBER; apply FRAME; right; exact MEMBER.
Qed.
Definition double_rectangular_guarded_code source steps flag iterators caches code :=
  Ssequence (rectangular_capture_code steps flag)
    (Sifthenelse (Etempvar flag memory_signed_int_type)
      (Ssequence code (double_rectangular_exit_code iterators caches)) source).
Theorem checked_double_rectangular_guarded_execution p source description caps steps phase adapt choices generated
  caches flag live pool code fe ge locals temps memory after final :
  checked_double_rectangular_raw_nest p [] source=Some description ->
  double_rectangular_entry_bounds_check caps description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_rectangular_globals description) locals ->
  double_tensor_static ge locals (double_source_instruction_layouts (rectangular_nest_instruction description)) ->
  double_rectangular_capture_steps (rectangular_nest_axes description) caches caps=Some steps ->
  NoDup caches -> ~ In flag caches ->
  (forall cache, In cache caches -> ~ In cache (double_rectangular_iterators (rectangular_nest_axes description))) ->
  (forall key, In key (statement_temps source++live) -> ~ In key (flag::caches)) ->
  mayReturn (checked_double_rectangular_tiled_prepared_loop_progress phase adapt choices caps
    (double_rectangular_pipeline_request description)) (Some generated) ->
  compile_double_rectangular_candidate (double_source_instruction_layouts (rectangular_nest_instruction description))
    caches flag caps live pool generated=Some code ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists target_after,
    exec_stmt fe ge locals temps memory
      (double_rectangular_guarded_code source steps flag (double_rectangular_iterators (rectangular_nest_axes description))
        caches code) E0 target_after final Out_normal /\ temp_agree live after target_after.
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL STATIC STEPS DISTINCT FLAG_FRESH CACHES_FRESH PRIVATE PIPELINE CODE SOURCE.
  destruct (@double_rectangular_capture_steps_sound (rectangular_nest_axes description) caches caps steps STEPS)
    as [LINK [CACHES CAPS]].
  destruct (@checked_double_rectangular_capture_model p source description caps steps fe ge locals temps memory
    flag live after final CHECK BOUNDS GLOBAL LOCAL LINK CAPS ltac:(rewrite CACHES; exact DISTINCT)
    ltac:(rewrite CACHES; exact FLAG_FRESH) ltac:(rewrite CACHES; exact PRIVATE) SOURCE)
    as [accepted [prepared [prepared_after [CAPTURE [FLAG [ENTRY [FALLBACK [EXIT FACTS]]]]]]]].
  destruct accepted.
  - destruct (FACTS eq_refl) as [observations [OBSERVATIONS [AXES [MODEL SET]]]].
    assert (LIMITS : Forall (fun step => 0<=rectangular_capture_limit step<=Int.max_signed) steps).
    { pose proof (@double_rectangular_checked_caps caps description BOUNDS) as [_ CAP_RANGES].
      apply Forall_forall; intros step MEMBER.
      apply Forall_forall with (x:=rectangular_capture_limit step) in CAP_RANGES;
        [destruct CAP_RANGES; split; [lia|assumption]|rewrite <- CAPS; apply in_map; exact MEMBER]. }
    pose proof (@double_rectangular_observation_words ge locals memory prepared steps observations
      OBSERVATIONS LIMITS) as WORDS; rewrite CACHES in WORDS.
    pose proof (@double_rectangular_cache_view caches _ prepared WORDS) as VIEW; rewrite map_map in VIEW.
    pose proof (@double_rectangular_observation_ranges ge locals memory prepared steps observations OBSERVATIONS) as RANGES.
    rewrite CAPS in RANGES.
    assert (CANDIDATE_MODEL : DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated))
      (map (fun observation => Z.of_nat (snd (snd observation))) observations)
      (RuntimeState (global_double_locations ge (double_source_instruction_layouts (rectangular_nest_instruction description))) memory)
      (RuntimeState (global_double_locations ge (double_source_instruction_layouts (rectangular_nest_instruction description))) final)).
    { eapply (@checked_double_rectangular_tiled_prepared_loop_progress_at phase adapt choices caps
        (double_rectangular_pipeline_request description) generated _ _ _ PIPELINE).
      - cbn [double_rectangular_pipeline_request fst snd]; rewrite !map_length; eapply Forall2_length; exact AXES.
      - apply global_double_locations_nonalias.
      - exact RANGES.
      - exact MODEL. }
    destruct (@compiled_double_rectangular_candidate_execution
      (double_source_instruction_layouts (rectangular_nest_instruction description)) caches flag caps live pool generated code
      fe ge locals prepared memory _ final STATIC CODE VIEW
      (@double_rectangular_candidate_bounds caps _ RANGES) CANDIDATE_MODEL)
      as [candidate_after [FRAME CANDIDATE]].
    assert (RESTORE : exec_stmt fe ge locals candidate_after final
      (double_rectangular_exit_code (double_rectangular_iterators (rectangular_nest_axes description)) caches) E0
      (double_rectangular_nest_exit (double_rectangular_iterators (rectangular_nest_axes description))
        (map (fun observation => snd (snd observation)) observations) candidate_after) final Out_normal).
    { apply double_rectangular_exit_code_execution.
      - pose proof (Forall2_length LINK) as LENGTH; rewrite <- (map_length rectangular_capture_cache steps),CACHES in LENGTH.
        unfold double_rectangular_iterators; rewrite map_length; exact LENGTH.
      - exact CACHES_FRESH.
      - eapply double_rectangular_words_frame; [exact WORDS|].
        eapply temp_agree_weaken; [intros key MEMBER; apply in_or_app; left; exact MEMBER|exact FRAME]. }
    exists (double_rectangular_nest_exit (double_rectangular_iterators (rectangular_nest_axes description))
      (map (fun observation => snd (snd observation)) observations) candidate_after); split.
    + unfold double_rectangular_guarded_code.
      eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0); [exact CAPTURE|].
      eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true); [constructor; exact FLAG|reflexivity|].
      eapply exec_Sseq_1 with (le1:=candidate_after) (m1:=final) (t1:=E0) (t2:=E0); eassumption.
    + eapply temp_agree_trans; [exact EXIT|rewrite SET].
      apply double_rectangular_exit_agree.
      eapply temp_agree_weaken; [|exact FRAME].
      intros key MEMBER; apply in_or_app; right; right; exact MEMBER.
  - exists prepared_after; split; [|exact EXIT].
    unfold double_rectangular_guarded_code.
    eapply exec_Sseq_1 with (le1:=prepared) (m1:=memory) (t1:=E0) (t2:=E0); [exact CAPTURE|].
    eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false); [constructor; exact FLAG|reflexivity|exact FALLBACK].
Qed.

Print Assumptions double_rectangular_words_frame.
Print Assumptions checked_double_rectangular_guarded_execution.
