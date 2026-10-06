From Stdlib Require Import Bool List.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightRegionProgress.
From GuardMemory Require Import GuardMemorySequentialCondition GuardMemoryProjectedCondition.
From GuardInterface Require Import ClightQuietDeterminacy.
Set Implicit Arguments.

(** Private loop checks retain their actual after-state. Completed executions
    are unique when the syntax satisfies the language's quiet restriction. *)
Theorem projected_check_execution_unique fe entry live check first first_after second second_after :
  quiet_statement check = true ->
  memory_projected_check_execution fe entry live check first first_after ->
  memory_projected_check_execution fe entry live check second second_after ->
  first = second /\ first_after = second_after.
Proof.
  intros QUIET [FIRST FRAME] [SECOND OTHER_FRAME].
  destruct (@quiet_execution_determinate fe (entry_ge entry) (entry_env entry)
    (entry_temps entry) (entry_memory entry) check _ _ _ _ FIRST QUIET _ _ _ _ SECOND)
    as [TRACE [TEMPS [MEMORY OUTCOME]]].
  split; [destruct first, second; cbn [memory_check_outcome] in OUTCOME; congruence|exact TEMPS].
Qed.

(** A domain library can prove a completed witness once. Determinacy upgrades
    its property to every completed execution; it does not prove availability,
    guard safety, or the host's exact dispatch law. *)
Theorem projected_check_witness_all fe entry live check property :
  quiet_statement check = true ->
  (exists accepted checked,
    memory_projected_check_execution fe entry live check accepted checked /\ property accepted checked) ->
  forall accepted checked,
    memory_projected_check_execution fe entry live check accepted checked -> property accepted checked.
Proof.
  intros QUIET [first [first_after [WITNESS PROPERTY]]] accepted checked RUN.
  destruct (projected_check_execution_unique QUIET WITNESS RUN) as [ACCEPTED CHECKED].
  subst accepted checked; exact PROPERTY.
Qed.

Print Assumptions projected_check_execution_unique.
Print Assumptions projected_check_witness_all.
