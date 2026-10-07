From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryPolyhedral GuardMemoryScalarLoops GuardMemoryScalarChecker GuardMemoryScalarTiling
  GuardMemoryPointerBackend GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend.
From GuardInterface Require Import ClightTensorBackendGuard.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition tensor_encoder_bounds bounds := map(fun bound=>MemoryFramedNested.N.A.Interval
  (MemoryNested.A.lower bound)(MemoryNested.A.upper bound))bounds.
Lemma tensor_encoder_bounds_sound bounds parameters : MemoryNested.A.env_within bounds parameters ->
  MemoryFramedNested.N.A.env_within(tensor_encoder_bounds bounds)parameters.
Proof.
  intros WITHIN index interval INDEX; unfold tensor_encoder_bounds in INDEX; rewrite nth_error_map in INDEX.
  destruct(nth_error bounds index)as [bound|]eqn:BOUND; cbn in INDEX; [|discriminate].
  inversion INDEX; subst interval; exact(WITHIN index bound BOUND).
Qed.

Definition check_compile_tensor_candidate dimension_sources pointer logical_array layout bounds live pool candidate
    (check:CoreAlarmed.Base.imp bool) :
    CoreAlarmed.Base.imp(option statement) :=
  match compile_tensor_buffer_loop dimension_sources pointer logical_array layout bounds live pool candidate with
  | Some code => BIND valid <- check -; pure(if valid then Some code else None)
  | None => pure None end.
Theorem check_compile_tensor_candidate_sound dimension_sources pointer logical_array layout bounds live pool candidate check code :
  mayReturn(check_compile_tensor_candidate dimension_sources pointer logical_array layout bounds live pool candidate check)(Some code) ->
  compile_tensor_buffer_loop dimension_sources pointer logical_array layout bounds live pool candidate=Some code /\ mayReturn check true.
Proof.
  unfold check_compile_tensor_candidate; destruct(compile_tensor_buffer_loop _ _ _ _ _ _ _ _)as [generated|]eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN; destruct valid; [|discriminate].
  inversion RUN; subst generated; split; [reflexivity|exact VALID].
Qed.
Definition check_tensor_mapped axes cap scalars instructions dimension_sources pointer logical_array layout live pool candidate steps :=
  check_compile_tensor_candidate dimension_sources pointer logical_array layout(tensor_encoder_bounds(memory_scalar_static_bounds axes cap scalars))live pool candidate
    (checked_memory_scalar_candidate axes cap scalars instructions layout[logical_array]candidate steps).
Definition check_tensor_tiled axes cap scalars instructions dimension_sources pointer logical_array layout live pool rows columns :=
  if (2 <=? axes)%nat && (0 <? rows)&&(0 <? columns) && Nat.eqb(length layout)(axes+scalars) then
    check_compile_tensor_candidate dimension_sources pointer logical_array layout(tensor_encoder_bounds(memory_scalar_static_bounds axes cap scalars))live pool
      (memory_scalar_tiled_loop axes scalars instructions rows columns true)
      (checked_memory_scalar_tiling axes cap scalars instructions layout[logical_array]rows columns)
  else pure None.

Section EXECUTION.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable dimension_sources : list tensor_dimension_source.
Variable pointer logical_array : ident.
Variable block : Values.block.
Variable base : ptrofs.

(** Candidate search and schedules are untrusted. Only the old verified checker,
    the concrete observed layout, and the new instruction backend are consumed.
    A frontend must still supply the source-to-Loop execution correspondence. *)
Theorem tensor_checked_candidate_execution axes cap scalars instructions layout live pool candidate code parameters temps source target memory dimensions :
  compile_tensor_buffer_loop dimension_sources pointer logical_array layout(tensor_encoder_bounds(memory_scalar_static_bounds axes cap scalars))live pool candidate=Some code ->
  memory_scalar_candidate_certificate axes cap scalars instructions layout candidate ->
  tensor_observe_dimensions dimension_sources temps=Some dimensions ->
  decision_run(Entry ge locals temps memory)(tensor_backend_guard dimension_sources)true ->
  MemoryNested.A.typed_view layout parameters temps -> MemoryNested.A.env_within(memory_scalar_static_bounds axes cap scalars)parameters ->
  length parameters=length layout ->
  L.loop_semantics(memory_scalar_rectangle 0 axes scalars instructions)parameters source target ->
  tensor_buffer_view dimensions logical_array block base source memory -> temps ! pointer=Some(Vptr block base) ->
  exists target_temps target_memory,tensor_buffer_view dimensions logical_array block base target target_memory /\
    tensor_buffer_capability dimensions dimension_sources pointer block base target_temps /\
    temp_agree(layout++tensor_buffer_protected dimension_sources pointer++live)temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  intros COMPILE CANDIDATE OBSERVE GUARD VIEW WITHIN LENGTH SOURCE MEMORY POINTER.
  assert(LAYOUT:tensor_layout_flag dimensions=true)by
    (exact(@tensor_backend_guard_accepts(Entry ge locals temps memory)dimension_sources dimensions OBSERVE GUARD)).
  assert(NONALIAS:GuardMemoryInstr.NonAlias source).
  { unfold tensor_buffer_view in MEMORY; subst source; apply tensor_backend_guard_nonalias with(entry:=Entry ge locals temps memory)(sources:=dimension_sources);
      assumption. }
  pose proof(CANDIDATE parameters source target LENGTH WITHIN NONALIAS SOURCE)as TARGET.
  eapply compile_tensor_buffer_loop_correct; [exact LAYOUT|exact COMPILE|exact VIEW| |exact TARGET|exact MEMORY|].
  - apply tensor_encoder_bounds_sound; exact WITHIN.
  -
  split; [exact POINTER|exact(proj1(@tensor_observe_dimensions_sound dimension_sources temps dimensions OBSERVE))].
Qed.

Theorem check_tensor_mapped_execution axes cap scalars instructions layout live pool candidate steps code parameters temps source target memory dimensions :
  mayReturn(check_tensor_mapped axes cap scalars instructions dimension_sources pointer logical_array layout live pool candidate steps)(Some code) ->
  tensor_observe_dimensions dimension_sources temps=Some dimensions ->
  decision_run(Entry ge locals temps memory)(tensor_backend_guard dimension_sources)true ->
  MemoryNested.A.typed_view layout parameters temps -> MemoryNested.A.env_within(memory_scalar_static_bounds axes cap scalars)parameters ->
  length parameters=length layout ->
  L.loop_semantics(memory_scalar_rectangle 0 axes scalars instructions)parameters source target ->
  tensor_buffer_view dimensions logical_array block base source memory -> temps ! pointer=Some(Vptr block base) ->
  exists target_temps target_memory,tensor_buffer_view dimensions logical_array block base target target_memory /\
    tensor_buffer_capability dimensions dimension_sources pointer block base target_temps /\
    temp_agree(layout++tensor_buffer_protected dimension_sources pointer++live)temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  intros CHECK OBSERVE GUARD VIEW WITHIN LENGTH SOURCE MEMORY POINTER.
  unfold check_tensor_mapped in CHECK; apply check_compile_tensor_candidate_sound in CHECK as [COMPILE VALID].
  pose proof(@checked_memory_scalar_candidate_correct axes cap scalars instructions layout[logical_array]candidate steps VALID)as CERTIFICATE.
  eapply tensor_checked_candidate_execution; eassumption.
Qed.

Theorem check_tensor_tiled_execution axes cap scalars instructions layout live pool rows columns code parameters temps source target memory dimensions :
  mayReturn(check_tensor_tiled axes cap scalars instructions dimension_sources pointer logical_array layout live pool rows columns)(Some code) ->
  tensor_observe_dimensions dimension_sources temps=Some dimensions ->
  decision_run(Entry ge locals temps memory)(tensor_backend_guard dimension_sources)true ->
  MemoryNested.A.typed_view layout parameters temps -> MemoryNested.A.env_within(memory_scalar_static_bounds axes cap scalars)parameters ->
  length parameters=length layout ->
  L.loop_semantics(memory_scalar_rectangle 0 axes scalars instructions)parameters source target ->
  tensor_buffer_view dimensions logical_array block base source memory -> temps ! pointer=Some(Vptr block base) ->
  exists target_temps target_memory,tensor_buffer_view dimensions logical_array block base target target_memory /\
    tensor_buffer_capability dimensions dimension_sources pointer block base target_temps /\
    temp_agree(layout++tensor_buffer_protected dimension_sources pointer++live)temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  unfold check_tensor_tiled; destruct((2 <=? axes)%nat&&(0 <? rows)&&(0 <? columns)&&Nat.eqb(length layout)(axes+scalars))eqn:STATIC;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  repeat rewrite andb_true_iff in STATIC; destruct STATIC as [[[AXES ROWS]COLUMNS]ARITY].
  apply Nat.leb_le in AXES; apply Z.ltb_lt in ROWS,COLUMNS; apply Nat.eqb_eq in ARITY.
  intros CHECK OBSERVE GUARD VIEW WITHIN LENGTH SOURCE MEMORY POINTER.
  apply check_compile_tensor_candidate_sound in CHECK as [COMPILE VALID].
  pose proof(@checked_memory_scalar_tiling_correct axes cap scalars instructions layout[logical_array]rows columns
    ARITY AXES ROWS COLUMNS VALID)as CERTIFICATE.
  eapply tensor_checked_candidate_execution; eassumption.
Qed.
End EXECUTION.

Print Assumptions check_compile_tensor_candidate_sound.
Print Assumptions tensor_encoder_bounds_sound.
Print Assumptions tensor_checked_candidate_execution.
Print Assumptions check_tensor_mapped_execution.
Print Assumptions check_tensor_tiled_execution.
