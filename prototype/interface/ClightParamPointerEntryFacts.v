From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryNaryAffineAccess GuardMemoryRecursiveSource
  GuardMemoryMultiPointerCells GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction
  GuardMemoryParamPointerSyntax GuardMemoryParamPointerHeader GuardMemoryParamPointerProjectedCandidate
  GuardMemoryParamAxisFootprint GuardMemoryParamAxisFrame GuardMemoryParamRuntimeFrame
  GuardMemoryParamAxisGuard GuardMemoryProjectedCondition.
From GuardInterface Require Import ClightPrivateCheckFacts ClightParamPointerCheckFacts.
Import ListNotations.
Set Implicit Arguments.

(** The domain library transports the actual restricted location view. Only
    cells in the source footprint require pointer-binding agreement. *)
Theorem param_pointer_restricted_locations_temp_frame source
  (package : memory_param_pointer_region_package source) ge locals memory original current live :
  memory_param_pointer_header_domain package (Entry ge locals original memory) ->
  memory_param_pointer_header_accept package (Entry ge locals original memory) = true ->
  temp_agree (memory_param_axis_pointer_guard_protected package live) original current ->
  forall cell,
    memory_restrict_locations (memory_footprint_allowed (memory_param_pointer_runtime_footprint package current))
      (memory_multi_pointer_locations current (param_pointer_region_window package)) cell =
    memory_restrict_locations (memory_footprint_allowed (memory_param_pointer_runtime_footprint package original))
      (memory_multi_pointer_locations original (param_pointer_region_window package)) cell.
Proof.
  intros DOMAIN ACCEPT FRAME.
  assert (CONTEXT : temp_agree (memory_param_pointer_runtime_context package) original current).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    unfold memory_param_axis_pointer_guard_protected; repeat rewrite in_app_iff; auto. }
  rewrite (@memory_param_pointer_runtime_footprint_temp_frame source package original current CONTEXT).
  destruct (@memory_param_pointer_header_sound source package _ DOMAIN ACCEPT) as [_ [BOUND_RANGES _]].
  destruct (@memory_param_axis_pointer_bound_values _ _ ge locals original memory BOUND_RANGES)
    as [counts [WORDS RANGES]].
  assert (SIGNED : Forall signed_range counts).
  { eapply Forall_impl; [|exact RANGES]; intros count [_ RANGE]; exact RANGE. }
  intro cell; unfold memory_restrict_locations.
  destruct (memory_footprint_allowed (memory_param_pointer_runtime_footprint package original) cell) eqn:ALLOWED;
    [|reflexivity].
  apply memory_footprint_allowed_exact in ALLOWED.
  apply (proj1 (@memory_param_axis_pointer_footprint_member source package original counts cell WORDS SIGNED))
    in ALLOWED as [access [coordinates [ACCESS [COORDINATES ->]]]].
  pose proof (memory_param_axis_pointer_accesses_covered package) as COVER.
  apply Forall_forall with (x := access) in COVER; [|exact ACCESS].
  unfold memory_param_axis_pointer_access_cell, memory_multi_pointer_locations; cbn [point_cell arr_id].
  rewrite FRAME; [reflexivity|apply memory_param_axis_pointer_protected_pointer; exact COVER].
Qed.

Lemma private_check_locations_nonalias_ext first second :
  (forall cell, first cell = second cell) ->
  (locations_nonalias first <-> locations_nonalias second).
Proof.
  intro SAME; split; intros SEPARATED a b first_location second_location FIRST SECOND DIFFERENT.
  - eapply SEPARATED; [rewrite SAME; exact FIRST|rewrite SAME; exact SECOND|exact DIFFERENT].
  - eapply SEPARATED; [rewrite <- SAME; exact FIRST|rewrite <- SAME; exact SECOND|exact DIFFERENT].
Qed.

(** Header, affine footprint and actual pointer bindings retain the same
    meaning after writes to fresh scan counters and its Boolean flag. *)
Theorem param_pointer_presumption_temp_frame source (package : memory_param_pointer_region_package source)
  ge locals memory original current live :
  memory_param_pointer_header_domain package (Entry ge locals original memory) ->
  temp_agree (memory_param_axis_pointer_guard_protected package live) original current ->
  (memory_param_pointer_runtime_presumption package (Entry ge locals current memory) <->
   memory_param_pointer_runtime_presumption package (Entry ge locals original memory)).
Proof.
  intros DOMAIN FRAME.
  assert (HEADER : memory_param_pointer_header_accept package (Entry ge locals current memory) =
    memory_param_pointer_header_accept package (Entry ge locals original memory)).
  { apply memory_param_pointer_header_accept_temp_frame.
    eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    unfold memory_param_axis_pointer_guard_protected, memory_param_pointer_runtime_context.
    repeat rewrite in_app_iff in *; intuition. }
  unfold memory_param_pointer_runtime_presumption; cbn [entry_temps]; rewrite HEADER.
  destruct (memory_param_pointer_header_accept package (Entry ge locals original memory)) eqn:ACCEPT.
  - pose proof (@param_pointer_restricted_locations_temp_frame source package ge locals memory original current live
      DOMAIN ACCEPT FRAME) as SAME.
    rewrite (@private_check_locations_nonalias_ext _ _ SAME); reflexivity.
  - split; intros [IMPOSSIBLE _]; discriminate.
Qed.

Lemma param_pointer_protected_idempotent source (package : memory_param_pointer_region_package source) live identifier :
  In identifier (memory_param_axis_pointer_guard_protected package
    (memory_param_axis_pointer_guard_protected package live)) ->
  In identifier (memory_param_axis_pointer_guard_protected package live).
Proof.
  unfold memory_param_axis_pointer_guard_protected; repeat rewrite in_app_iff; intuition.
Qed.

(** Ask the established encoder for its stronger observation frame, then
    weaken the execution relation to the caller's declared live temporaries. *)
Theorem param_axis_pointer_guard_entry_witness source (package : memory_param_pointer_region_package source)
  fe entry live left right flag :
  length left = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  length right = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  NoDup (left ++ right) ->
  NoDup (left ++ param_pointer_region_parameters package) ->
  NoDup (right ++ param_pointer_region_parameters package) ->
  (forall identifier, In identifier (left ++ right) ->
    ~ In identifier (memory_param_axis_pointer_guard_protected package live) /\ identifier <> flag) ->
  ~ In flag (memory_param_axis_pointer_guard_protected package live) ->
  memory_param_pointer_runtime_domain package entry ->
  exists accepted checked,
    memory_projected_check_execution fe entry live
      (memory_param_axis_pointer_guard_statement package left right flag) accepted checked /\
    temp_agree (memory_param_axis_pointer_guard_protected package live) (entry_temps entry) checked /\
    (accepted = true -> memory_param_pointer_runtime_presumption package entry).
Proof.
  intros LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM FRESH FLAG DOMAIN.
  destruct (@memory_param_axis_pointer_guard_execution source package fe entry
    (memory_param_axis_pointer_guard_protected package live) left right flag
    LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM
    ltac:(intros identifier MEMBER; destruct (FRESH identifier MEMBER) as [PROTECTED NOT_FLAG];
      split; [intro BAD; apply PROTECTED; eapply param_pointer_protected_idempotent; exact BAD|exact NOT_FLAG])
    ltac:(intro BAD; apply FLAG; eapply param_pointer_protected_idempotent; exact BAD)
    DOMAIN) as [accepted [checked [[RUN FRAME] SOUND]]].
  exists accepted,checked; split.
  - split; [exact RUN|].
    eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER.
    unfold memory_param_axis_pointer_guard_protected; repeat (apply in_or_app; right); exact MEMBER.
  - split; [exact FRAME|]; intro ACCEPT.
    destruct entry as [ge locals original memory]; cbn in *.
    apply (proj1 (@param_pointer_presumption_temp_frame source package ge locals memory original checked live
      (proj1 DOMAIN) FRAME)); apply SOUND; exact ACCEPT.
Qed.

Theorem param_axis_pointer_guard_original_entry_sound source (package : memory_param_pointer_region_package source)
  fe entry live left right flag :
  length left = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  length right = length (memory_nest_iterators (param_pointer_region_nest package)) ->
  NoDup (left ++ right) ->
  NoDup (left ++ param_pointer_region_parameters package) ->
  NoDup (right ++ param_pointer_region_parameters package) ->
  (forall identifier, In identifier (left ++ right) ->
    ~ In identifier (memory_param_axis_pointer_guard_protected package live) /\ identifier <> flag) ->
  ~ In flag (memory_param_axis_pointer_guard_protected package live) ->
  memory_param_pointer_runtime_domain package entry ->
  forall accepted checked,
    memory_projected_check_execution fe entry live
      (memory_param_axis_pointer_guard_statement package left right flag) accepted checked ->
    temp_agree (memory_param_axis_pointer_guard_protected package live) (entry_temps entry) checked /\
    (accepted = true -> memory_param_pointer_runtime_presumption package entry).
Proof.
  intros LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM FRESH FLAG DOMAIN.
  apply (@projected_check_witness_all fe entry live
    (memory_param_axis_pointer_guard_statement package left right flag)
    (fun accepted checked =>
      temp_agree (memory_param_axis_pointer_guard_protected package live) (entry_temps entry) checked /\
      (accepted = true -> memory_param_pointer_runtime_presumption package entry))).
  - apply param_axis_pointer_guard_quiet.
  - eapply param_axis_pointer_guard_entry_witness; eassumption.
Qed.

Print Assumptions param_pointer_restricted_locations_temp_frame.
Print Assumptions param_pointer_presumption_temp_frame.
Print Assumptions param_axis_pointer_guard_entry_witness.
Print Assumptions param_axis_pointer_guard_original_entry_sound.
