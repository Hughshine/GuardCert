From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryDoublePolyhedral
  GuardMemoryDoubleTensorBackend GuardMemoryDoubleNestedBackend GuardMemoryRectangularCapture
  GuardMemoryRectangularCaptureObservations.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Theorem double_rectangular_observation_words ge locals memory after steps observations :
  Forall2 (rectangular_capture_observation ge locals memory after) steps observations ->
  Forall (fun step => 0<=rectangular_capture_limit step<=Int.max_signed) steps ->
  Forall2 (fun cache count => 0<Z.of_nat count /\ signed_range (Z.of_nat count) /\
    after ! cache=Some (Vint (Int.repr (Z.of_nat count))))
    (map rectangular_capture_cache steps) (map (fun observation => snd (snd observation)) observations).
Proof.
  intro OBSERVATIONS; induction OBSERVATIONS; intro LIMITS; cbn [map]; [constructor|].
  inversion LIMITS as [|step steps LIMIT TAIL]; subst step steps; constructor.
  - unfold rectangular_capture_observation in H; destruct H as [_ [_ [_ [RANGE [_ WORD]]]]].
    split; [lia|split; [unfold signed_range; change (-2147483648<=Z.of_nat (snd (snd y))<=2147483647);
      change (0<=rectangular_capture_limit x<=2147483647) in LIMIT; lia|exact WORD]].
  - apply IHOBSERVATIONS; exact TAIL.
Qed.
Theorem double_rectangular_cache_view caches counts temps :
  Forall2 (fun cache count => 0<Z.of_nat count /\ signed_range (Z.of_nat count) /\
    temps ! cache=Some (Vint (Int.repr (Z.of_nat count)))) caches counts ->
  DoubleNested.A.typed_view caches (map Z.of_nat counts) temps.
Proof.
  intro WORDS; induction WORDS; intros [|index] identifier INDEX; cbn in INDEX; try discriminate.
  - inversion INDEX; subst identifier; cbn [map nth].
    destruct H as [_ [RANGE WORD]]; exists (Int.repr (Z.of_nat y)); split; [exact WORD|].
    apply Int.signed_repr; exact RANGE.
  - cbn [map nth]; apply IHWORDS; exact INDEX.
Qed.
Theorem double_rectangular_observation_ranges ge locals memory after steps observations :
  Forall2 (rectangular_capture_observation ge locals memory after) steps observations ->
  Forall2 (fun cap value => 0<=value<=cap) (map rectangular_capture_limit steps)
    (map (fun observation => Z.of_nat (snd (snd observation))) observations).
Proof.
  intro OBSERVATIONS; induction OBSERVATIONS; cbn [map]; constructor; [|exact IHOBSERVATIONS].
  unfold rectangular_capture_observation in H; destruct H as [_ [_ [_ [RANGE _]]]]; lia.
Qed.
Theorem double_rectangular_candidate_bounds caps parameters :
  Forall2 (fun cap value => 0<=value<=cap) caps parameters ->
  DoubleNested.A.env_within (map (fun cap => DoubleNested.A.Interval 0 cap) caps) parameters.
Proof.
  intro RANGES; induction RANGES; intros [|index] bound INDEX; cbn in INDEX; try discriminate.
  - inversion INDEX; subst bound; unfold DoubleNested.A.contains; cbn; exact H.
  - cbn [nth]; apply IHRANGES; exact INDEX.
Qed.
Definition compile_double_rectangular_candidate layouts caches flag caps live pool
  (generated : DoubleAssignmentIRs.Loop.t) :=
  compile_double_tensor_loop layouts caches (map (fun cap => DoubleNested.A.Interval 0 cap) caps)
    (flag::live) pool (fst (fst generated)).
Theorem compiled_double_rectangular_candidate_execution layouts caches flag caps live pool generated code
  fe ge locals temps memory parameters final :
  double_tensor_static ge locals layouts ->
  compile_double_rectangular_candidate layouts caches flag caps live pool generated=Some code ->
  DoubleNested.A.typed_view caches parameters temps ->
  DoubleNested.A.env_within (map (fun cap => DoubleNested.A.Interval 0 cap) caps) parameters ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) parameters
    (RuntimeState (global_double_locations ge layouts) memory)
    (RuntimeState (global_double_locations ge layouts) final) ->
  exists candidate_after,
    temp_agree (caches++flag::live) temps candidate_after /\
    exec_stmt fe ge locals temps memory code E0 candidate_after final Out_normal.
Proof.
  intros STATIC CODE VIEW WITHIN MODEL.
  destruct (@compile_double_tensor_loop_correct fe ge locals layouts STATIC caches
    (map (fun cap => DoubleNested.A.Interval 0 cap) caps) (flag::live) pool (fst (fst generated)) code
    parameters temps _ _ memory CODE VIEW WITHIN MODEL ltac:(split; reflexivity))
    as [candidate_after [target_memory [[LOCATIONS SAME] [FRAME RUN]]]].
  cbn [runtime_memory] in SAME; subst target_memory; exists candidate_after; auto.
Qed.

Print Assumptions double_rectangular_observation_words.
Print Assumptions double_rectangular_cache_view.
Print Assumptions double_rectangular_observation_ranges.
Print Assumptions double_rectangular_candidate_bounds.
Print Assumptions compiled_double_rectangular_candidate_execution.
