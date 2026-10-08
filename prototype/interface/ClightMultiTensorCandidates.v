From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryScalarLoops GuardMemoryScalarChecker GuardMemoryPointerBackend GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend
  GuardMemoryMultiTensorBackend GuardMemoryFootprintRestriction GuardMemoryFiniteFootprint GuardMemoryLoopTrace.
From GuardInterface Require Import ClightTensorCandidates ClightTensorGeneratedCandidates ClightTensorBackendGuard GuardMemoryTiledPreparedPipeline.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Proposals carry the actual Loop and witnesses. Multi-array lowering and
    the old verified domain checker independently check the proposed data. *)
Definition check_multi_tensor_generated axes cap scalars instructions dimensions pointers layout live pool proposal :=
  let candidate:=tensor_generated_loop proposal in
  let check:=match proposal with
  | TensorGeneratedMapped _ steps=>checked_memory_scalar_candidate axes cap scalars instructions layout pointers candidate steps
  | TensorGeneratedTiled _ witnesses=>checked_memory_scalar_generated_tiling axes cap scalars instructions layout pointers candidate witnesses end in
  match compile_multi_tensor_buffer_loop dimensions pointers layout
    (tensor_encoder_bounds(memory_scalar_static_bounds axes cap scalars))live pool candidate with
  | Some code=>BIND valid <- check -; pure(if valid then Some code else None)
  | None=>pure None end.

Theorem check_multi_tensor_generated_sound axes cap scalars instructions dimensions pointers layout live pool proposal code :
  mayReturn(check_multi_tensor_generated axes cap scalars instructions dimensions pointers layout live pool proposal)(Some code) ->
  compile_multi_tensor_buffer_loop dimensions pointers layout(tensor_encoder_bounds(memory_scalar_static_bounds axes cap scalars))
    live pool(tensor_generated_loop proposal)=Some code /\
  memory_scalar_candidate_certificate axes cap scalars instructions layout(tensor_generated_loop proposal).
Proof.
  unfold check_multi_tensor_generated; destruct(compile_multi_tensor_buffer_loop _ _ _ _ _ _ _)as [generated|]eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN; destruct valid; [|discriminate].
  inversion RUN; subst generated; split; [reflexivity|].
  destruct proposal; cbn in *.
  - eapply checked_memory_scalar_candidate_correct; exact VALID.
  - eapply checked_memory_scalar_generated_tiling_correct; exact VALID.
Qed.

Definition multi_tensor_source_footprint axes scalars instructions parameters :=
  memory_events_footprint(memory_loop_trace(memory_scalar_rectangle 0 axes scalars instructions)parameters).

(** This obligation concerns only source cells, not all pointer bindings or
    all addresses of an allocation. A source/guard factory must produce it
    from source-licensed observations; it is not discharged by lowering. *)
Definition multi_tensor_separated_source axes scalars instructions parameters temps sizes :=
  locations_nonalias(memory_restrict_locations
    (memory_footprint_allowed(multi_tensor_source_footprint axes scalars instructions parameters))
    (multi_tensor_locations temps sizes)).

Theorem multi_tensor_checked_candidate_execution axes cap scalars instructions dimensions pointers layout live pool
    candidate code parameters temps memory final sizes fe ge locals :
  compile_multi_tensor_buffer_loop dimensions pointers layout(tensor_encoder_bounds(memory_scalar_static_bounds axes cap scalars))
    live pool candidate=Some code ->
  memory_scalar_candidate_certificate axes cap scalars instructions layout candidate ->
  tensor_observe_dimensions dimensions temps=Some sizes ->
  decision_run(Entry ge locals temps memory)(tensor_backend_guard dimensions)true ->
  MemoryNested.A.typed_view layout parameters temps ->
  MemoryNested.A.env_within(memory_scalar_static_bounds axes cap scalars)parameters -> length parameters=length layout ->
  multi_tensor_separated_source axes scalars instructions parameters temps sizes ->
  L.loop_semantics(memory_scalar_rectangle 0 axes scalars instructions)parameters
    (RuntimeState(multi_tensor_locations temps sizes)memory)(RuntimeState(multi_tensor_locations temps sizes)final) ->
  exists target_temps,
    temp_agree(layout++multi_tensor_buffer_protected dimensions pointers++live)temps target_temps /\
    multi_tensor_buffer_capability temps sizes dimensions pointers target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps final Out_normal.
Proof.
  intros COMPILE CERTIFICATE OBSERVE GUARD VIEW WITHIN LENGTH SEPARATED SOURCE.
  assert(LAYOUT:tensor_layout_flag sizes=true)by
    (exact(@tensor_backend_guard_accepts(Entry ge locals temps memory)dimensions sizes OBSERVE GUARD)).
  set(allowed:=memory_footprint_allowed(multi_tensor_source_footprint axes scalars instructions parameters)).
  set(restricted:=memory_restrict_locations allowed(multi_tensor_locations temps sizes)).
  assert(COVERED:memory_loop_cells_covered allowed(memory_scalar_rectangle 0 axes scalars instructions)parameters).
  { apply memory_loop_own_footprint_covered. }
  assert(RESTRICTED:L.loop_semantics(memory_scalar_rectangle 0 axes scalars instructions)parameters
    (RuntimeState restricted memory)(RuntimeState restricted final)).
  { change(L.loop_semantics(memory_scalar_rectangle 0 axes scalars instructions)parameters
      (memory_restrict_state allowed(RuntimeState(multi_tensor_locations temps sizes)memory))
      (memory_restrict_state allowed(RuntimeState(multi_tensor_locations temps sizes)final))).
    eapply memory_restrict_loop_execution; [exact COVERED|exact SOURCE]. }
  assert(NONALIAS:GuardMemoryInstr.NonAlias(RuntimeState restricted memory))by exact SEPARATED.
  pose proof(CERTIFICATE parameters(RuntimeState restricted memory)(RuntimeState restricted final)
    LENGTH WITHIN NONALIAS RESTRICTED)as CHECKED.
  assert(TARGET:L.loop_semantics candidate parameters(RuntimeState(multi_tensor_locations temps sizes)memory)
    (RuntimeState(multi_tensor_locations temps sizes)final))by(eapply memory_unrestrict_loop_execution; exact CHECKED).
  destruct(@compile_multi_tensor_buffer_loop_correct temps sizes LAYOUT dimensions fe ge locals pointers layout
    (tensor_encoder_bounds(memory_scalar_static_bounds axes cap scalars))live pool candidate code parameters temps
    (RuntimeState(multi_tensor_locations temps sizes)memory)(RuntimeState(multi_tensor_locations temps sizes)final)memory
    COMPILE VIEW(tensor_encoder_bounds_sound WITHIN)TARGET eq_refl
    (conj(temp_agree_refl pointers temps)(proj1(@tensor_observe_dimensions_sound dimensions temps sizes OBSERVE))))
    as [target_temps [target_memory [MEMORY [CAPABILITY [FRAME EXEC]]]]].
  unfold multi_tensor_buffer_view in MEMORY; inversion MEMORY; subst target_memory.
  exists target_temps; auto.
Qed.

Theorem check_multi_tensor_generated_execution axes cap scalars instructions dimensions pointers layout live pool proposal code
    parameters temps memory final sizes fe ge locals :
  mayReturn(check_multi_tensor_generated axes cap scalars instructions dimensions pointers layout live pool proposal)(Some code) ->
  tensor_observe_dimensions dimensions temps=Some sizes ->
  decision_run(Entry ge locals temps memory)(tensor_backend_guard dimensions)true ->
  MemoryNested.A.typed_view layout parameters temps ->
  MemoryNested.A.env_within(memory_scalar_static_bounds axes cap scalars)parameters -> length parameters=length layout ->
  multi_tensor_separated_source axes scalars instructions parameters temps sizes ->
  L.loop_semantics(memory_scalar_rectangle 0 axes scalars instructions)parameters
    (RuntimeState(multi_tensor_locations temps sizes)memory)(RuntimeState(multi_tensor_locations temps sizes)final) ->
  exists target_temps,temp_agree(layout++multi_tensor_buffer_protected dimensions pointers++live)temps target_temps /\
    multi_tensor_buffer_capability temps sizes dimensions pointers target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps final Out_normal.
Proof.
  intro CHECK; apply check_multi_tensor_generated_sound in CHECK as [COMPILE CERTIFICATE].
  exact(@multi_tensor_checked_candidate_execution axes cap scalars instructions dimensions pointers layout live pool
    (tensor_generated_loop proposal)code parameters temps memory final sizes fe ge locals COMPILE CERTIFICATE).
Qed.

Print Assumptions check_multi_tensor_generated_sound.
Print Assumptions multi_tensor_checked_candidate_execution.
Print Assumptions check_multi_tensor_generated_execution.
