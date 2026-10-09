From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations
  GuardMemoryDoubleTensorBackend GuardMemoryDoubleNestedBackend GuardMemoryDoublePolyhedral
  GuardMemoryDoubleInitializedLowering GuardMemoryDoubleQuotientPrepared.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module DBL := DoubleAssignmentIRs.Loop.

Definition double_quotient_interval bound :=
  DoubleNested.A.Interval (DoubleQuotientCapture.Machine.lower bound)
    (DoubleQuotientCapture.Machine.upper bound).
Definition compile_double_ceil_capture cache quotient limit divisor :=
  match DoubleQuotientCapture.compile_capture [cache]
    [DoubleQuotientCapture.Machine.Interval 0 limit] quotient (double_ceil_numerator divisor) divisor with
  | Some (capture,bound) => Some (capture,double_quotient_interval bound)
  | None => None end.
Lemma double_quotient_ranges_transport bound limit value number :
  DoubleQuotientCapture.Machine.env_within
    [bound;DoubleQuotientCapture.Machine.Interval 0 limit] [value;number] ->
  DoubleNested.A.env_within [double_quotient_interval bound;DoubleNested.A.Interval 0 limit] [value;number].
Proof.
  intros WITHIN [|[|index]] range LOOKUP; cbn in LOOKUP.
  - inversion LOOKUP; subst; exact (WITHIN 0%nat bound eq_refl).
  - inversion LOOKUP; subst; exact (WITHIN 1%nat (DoubleQuotientCapture.Machine.Interval 0 limit) eq_refl).
  - destruct index; discriminate.
Qed.
Definition compile_double_quotient_candidate layouts cache flag quotient limit quotient_range live pool
  (generated : DoubleAssignmentIRs.Loop.t) :=
  compile_double_tensor_loop layouts [quotient;cache]
    [quotient_range;DoubleNested.A.Interval 0 limit] (flag::live) pool (fst (fst generated)).

Theorem compiled_double_quotient_candidate_execution layouts cache flag quotient limit quotient_range live pool
  generated code fe ge locals temps memory number quotient_value final :
  double_tensor_static ge locals layouts ->
  compile_double_quotient_candidate layouts cache flag quotient limit quotient_range live pool generated=Some code ->
  DoubleNested.A.typed_view [quotient;cache] [quotient_value;number] temps ->
  DoubleNested.A.env_within [quotient_range;DoubleNested.A.Interval 0 limit] [quotient_value;number] ->
  DBL.loop_semantics (fst (fst generated)) [quotient_value;number]
    (RuntimeState (global_double_locations ge layouts) memory)
    (RuntimeState (global_double_locations ge layouts) final) ->
  exists candidate_after,
    temp_agree ([quotient;cache;flag]++live) temps candidate_after /\
    exec_stmt fe ge locals temps memory code E0 candidate_after final Out_normal.
Proof.
  intros STATIC CODE VIEW WITHIN MODEL.
  destruct (@compile_double_tensor_loop_correct fe ge locals layouts STATIC
    [quotient;cache] [quotient_range;DoubleNested.A.Interval 0 limit] (flag::live) pool
    (fst (fst generated)) code [quotient_value;number] temps _ _ memory CODE VIEW WITHIN MODEL
    ltac:(split; reflexivity))
    as [candidate_after [target_memory [[LOCATIONS SAME] [FRAME RUN]]]].
  cbn [runtime_memory] in SAME; subst target_memory; exists candidate_after; auto.
Qed.
Theorem compiled_double_ceil_capture_execution cache quotient flag limit divisor capture quotient_range
  fe ge locals temps memory count live :
  compile_double_ceil_capture cache quotient limit divisor=Some (capture,quotient_range) ->
  signed_range (Z.of_nat count) -> Z.of_nat count<=limit ->
  temps ! cache=Some (Vint (Int.repr (Z.of_nat count))) ->
  ~ In quotient (cache::flag::live) ->
  let value := (Z.of_nat count+divisor-1)/divisor in
  let captured := PTree.set quotient (Vint (Int.repr value)) temps in
  exec_stmt fe ge locals temps memory capture E0 captured memory Out_normal /\
  DoubleNested.A.typed_view [quotient;cache] [value;Z.of_nat count] captured /\
  DoubleNested.A.env_within [quotient_range;DoubleNested.A.Interval 0 limit] [value;Z.of_nat count] /\
  DBL.eval_test [value;Z.of_nat count]
    (DoubleQuotientModel.quotient_relation (double_ceil_numerator divisor) divisor)=true /\
  temp_agree (cache::flag::live) temps captured.
Proof.
  unfold compile_double_ceil_capture.
  destruct (DoubleQuotientCapture.compile_capture [cache]
    [DoubleQuotientCapture.Machine.Interval 0 limit] quotient (double_ceil_numerator divisor) divisor)
    as [[statement bound]|] eqn:CAPTURE; try discriminate.
  intros COMPILE RANGE UPPER CACHE FRESH; inversion COMPILE; subst capture quotient_range.
  replace (Z.of_nat count+divisor-1) with (Z.of_nat count+(divisor-1)) by lia.
  assert (WITHIN : DoubleQuotientCapture.Machine.env_within
    [DoubleQuotientCapture.Machine.Interval 0 limit] [Z.of_nat count]).
  { intros [|index] interval LOOKUP; cbn in LOOKUP.
    - inversion LOOKUP; subst interval; change (0<=Z.of_nat count<=limit); lia.
    - destruct index; discriminate. }
  destruct (@DoubleQuotientCapture.quotient_capture_execution [cache]
    [DoubleQuotientCapture.Machine.Interval 0 limit]
    quotient (double_ceil_numerator divisor) divisor statement bound [Z.of_nat count] temps
    (flag::live) fe ge locals memory CAPTURE WITHIN
    (@double_initialized_cache_view cache count temps RANGE CACHE) FRESH)
    as [RUN [VIEW [BOUNDS [RELATION FRAME]]]].
  split; [exact RUN|split; [exact VIEW|split; [|auto]]].
  apply double_quotient_ranges_transport; exact BOUNDS.
Qed.

Print Assumptions compiled_double_ceil_capture_execution.
Print Assumptions compiled_double_quotient_candidate_execution.
