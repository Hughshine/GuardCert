From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryExtractorProgress GuardMemoryFootprintCapabilities GuardMemoryFootprintRestriction
  GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition GuardMemoryMultiPointerCells.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_multi_pointer_source_tree (temps : temp_env) (extent : Z) source parameters :=
  memory_finite_address_tree memory_multi_pointer_cell_code
    (memory_events_footprint (memory_loop_trace source parameters)).
(** The source trace is a proof witness for a finite footprint. A compiler
    must still instantiate a static or activated footprint representation;
    this theorem does not insert an entry computation of the source trace. *)
Theorem memory_multi_pointer_source_address_domain source parameters ge locals temps memory after extent :
  extent <= Int.max_signed+1 ->
  L.loop_semantics source parameters (RuntimeState (memory_multi_pointer_locations temps extent) memory)
    (RuntimeState (memory_multi_pointer_locations temps extent) after) ->
  Forall (memory_cell_address_binding memory_multi_pointer_cell_code (memory_multi_pointer_locations temps extent)
    (Entry ge locals temps memory)) (memory_events_footprint (memory_loop_trace source parameters)).
Proof.
  intros EXTENT SOURCE; apply memory_multi_pointer_footprint_encoding; [exact EXTENT|].
  pose proof (@memory_loop_source_capabilities source parameters
    (RuntimeState (memory_multi_pointer_locations temps extent) memory)
    (RuntimeState (memory_multi_pointer_locations temps extent) after)
    (memory_multi_pointer_locations_int32 temps extent) SOURCE) as CAPABILITIES.
  apply Forall_forall; intros cell MEMBER; unfold memory_events_footprint in MEMBER.
  apply in_flat_map in MEMBER as [event [EVENT CELL]].
  apply Forall_forall with (x := event) in CAPABILITIES; [|exact EVENT].
  apply Forall_forall with (x := cell) in CAPABILITIES; [exact CAPABILITIES|exact CELL].
Qed.
Theorem memory_multi_pointer_source_guard_exact source parameters ge locals temps memory after extent :
  extent <= Int.max_signed+1 ->
  L.loop_semantics source parameters (RuntimeState (memory_multi_pointer_locations temps extent) memory)
    (RuntimeState (memory_multi_pointer_locations temps extent) after) ->
  forall flag, decision_run (Entry ge locals temps memory)
    (memory_multi_pointer_source_tree temps extent source parameters) flag <->
    flag = memory_finite_address_check (memory_multi_pointer_locations temps extent)
      (memory_events_footprint (memory_loop_trace source parameters)).
Proof.
  intros EXTENT SOURCE flag; apply memory_finite_address_exact.
  eapply memory_multi_pointer_source_address_domain; eassumption.
Qed.
Theorem memory_multi_pointer_guarded_candidate source candidate context vars parameters ge locals temps memory after extent :
  extent <= Int.max_signed+1 -> length parameters = length context ->
  mayReturn (checked_memory_loop_equivalence (source,context,vars) (candidate,context,vars)) true ->
  L.loop_semantics source parameters (RuntimeState (memory_multi_pointer_locations temps extent) memory)
    (RuntimeState (memory_multi_pointer_locations temps extent) after) ->
  decision_run (Entry ge locals temps memory)
    (memory_multi_pointer_source_tree temps extent source parameters) true ->
  L.loop_semantics candidate parameters (RuntimeState (memory_multi_pointer_locations temps extent) memory)
    (RuntimeState (memory_multi_pointer_locations temps extent) after).
Proof.
  intros EXTENT LENGTH CHECK SOURCE GUARD.
  pose proof (@memory_multi_pointer_source_address_domain source parameters ge locals temps memory after extent
    EXTENT SOURCE) as DOMAIN.
  eapply memory_finite_footprint_separated_candidate; [exact LENGTH|exact CHECK| |exact SOURCE].
  apply (@memory_finite_address_separation_sound memory_multi_pointer_cell_code
    (memory_multi_pointer_locations temps extent) (Entry ge locals temps memory) _ DOMAIN).
  symmetry; exact (proj1 (@memory_multi_pointer_source_guard_exact source parameters ge locals temps memory after extent
    EXTENT SOURCE true) GUARD).
Qed.
Print Assumptions memory_multi_pointer_source_address_domain.
Print Assumptions memory_multi_pointer_source_guard_exact.
Print Assumptions memory_multi_pointer_guarded_candidate.
