From Stdlib Require Import List.
From compcert.common Require Import Smallstep.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightPrivateRegion ClightPrivateRegionProof ClightPrivatePool
  ClightTempScope ClightTempFootprint.
From GuardMemory Require Import GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightSignedExpressionProgress.
Import ListNotations.
Set Implicit Arguments.

(** The host consumes checked local contracts, irrespective of the optimizer
    that produced the table. Source progress concerns the original code even
    when its dynamic condition refuses the rewrite. *)
Definition apply_expression_region_table pool table (p : Clight.program) :=
  transform_private_program signed_expression_region_progress_supported
    (fun _ _ => select_memory_tiled_table table) pool p.

Theorem apply_expression_region_table_correct pool table p :
  Forall (fun pair => PrivateRegion.projected_region_contract
    (program_temps p) (fst pair) (snd pair)) table ->
  forward_simulation (Clight.semantics2 p)
    (Clight.semantics2 (apply_expression_region_table pool table p)).
Proof.
  intro TABLE; unfold apply_expression_region_table,transform_private_program.
  destruct (private_pool_check (program_temps p) pool) eqn:FRESH.
  - eapply PrivateRegionProof.transform_program_correct2 with (live:=program_temps p).
    + exact signed_expression_region_progress_supported_sound.
    + apply select_memory_tiled_table_sound; exact TABLE.
    + apply program_scope_computed.
    + eapply private_pool_check_sound; exact FRESH.
  - apply forward_simulation_step with (match_states:=@eq Clight.state).
    + reflexivity.
    + intros source INIT; exists source; auto.
    + intros; subst; assumption.
    + intros source events next STEP target SAME; subst target; exists next; auto.
Qed.

Print Assumptions apply_expression_region_table_correct.
