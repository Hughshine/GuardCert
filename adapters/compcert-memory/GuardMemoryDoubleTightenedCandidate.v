From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import PolCertGuardedLoopTightening ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleAssignment
  GuardMemoryDoublePolyhedral GuardMemoryDoubleNestedBackend GuardMemoryDoubleTensorBackend
  GuardMemoryDoubleLocations GuardMemoryDoubleRectangularCandidate.
Import ListNotations.
Set Implicit Arguments.
Module DoubleTightening := PolCertGuardedLoopTighteningFor DoubleAssignmentInstr DoubleAssignmentIRs.Loop.

Definition double_rectangular_tightened_loop caps body :=
  DoubleTightening.tighten (map (fun cap=>DoubleTightening.A.Interval 0 cap) caps) body.
Lemma double_tightening_initial_bounds caps parameters :
  DoubleNested.A.env_within (map (fun cap=>DoubleNested.A.Interval 0 cap) caps) parameters ->
  DoubleTightening.A.env_within (map (fun cap=>DoubleTightening.A.Interval 0 cap) caps) parameters.
Proof.
  unfold DoubleNested.A.env_within,DoubleTightening.A.env_within.
  intros WITHIN n bound INDEX; rewrite nth_error_map in INDEX.
  destruct (nth_error caps n) as [cap|] eqn:CAP; cbn in INDEX; try discriminate.
  inversion INDEX; subst bound; unfold DoubleTightening.A.contains; cbn.
  apply (WITHIN n (DoubleNested.A.Interval 0 cap)).
  rewrite nth_error_map,CAP; reflexivity.
Qed.
Definition compile_tightened_double_rectangular_candidate layouts caches flag caps live pool
  (generated : DoubleAssignmentIRs.Loop.t) :=
  compile_double_tensor_loop layouts caches (map (fun cap=>DoubleNested.A.Interval 0 cap) caps)
    (flag::live) pool (double_rectangular_tightened_loop caps (fst (fst generated))).

(** The validated enclosure remains the semantic premise.  The new compiler
    consumes the tightening theorem before lowering its actual runtime bounds. *)
Theorem compiled_tightened_double_rectangular_candidate_execution layouts caches flag caps live pool generated code
  fe ge locals temps memory parameters final :
  double_tensor_static ge locals layouts ->
  compile_tightened_double_rectangular_candidate layouts caches flag caps live pool generated=Some code ->
  DoubleNested.A.typed_view caches parameters temps ->
  DoubleNested.A.env_within (map (fun cap=>DoubleNested.A.Interval 0 cap) caps) parameters ->
  DoubleAssignmentIRs.Loop.loop_semantics (fst (fst generated)) parameters
    (RuntimeState (global_double_locations ge layouts) memory)
    (RuntimeState (global_double_locations ge layouts) final) ->
  exists candidate_after,
    temp_agree (caches++flag::live) temps candidate_after /\
    exec_stmt fe ge locals temps memory code E0 candidate_after final Out_normal.
Proof.
  intros STATIC CODE VIEW WITHIN MODEL.
  pose proof (@DoubleTightening.tighten_execution (fst (fst generated))
    (map (fun cap=>DoubleTightening.A.Interval 0 cap) caps) parameters
    (RuntimeState (global_double_locations ge layouts) memory)
    (RuntimeState (global_double_locations ge layouts) final)
    (@double_tightening_initial_bounds caps parameters WITHIN) MODEL) as TIGHTENED.
  destruct (@compile_double_tensor_loop_correct fe ge locals layouts STATIC caches
    (map (fun cap=>DoubleNested.A.Interval 0 cap) caps) (flag::live) pool
    (double_rectangular_tightened_loop caps (fst (fst generated))) code parameters temps _ _ memory
    CODE VIEW WITHIN TIGHTENED ltac:(split; reflexivity))
    as [candidate_after [target_memory [[LOCATIONS SAME] [FRAME RUN]]]].
  cbn [runtime_memory] in SAME; subst target_memory; exists candidate_after; auto.
Qed.

Print Assumptions compiled_tightened_double_rectangular_candidate_execution.
Print Assumptions double_tightening_initial_bounds.
