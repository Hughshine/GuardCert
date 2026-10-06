From Stdlib Require Import List.
From compcert.common Require Import AST Smallstep.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightPrivateRegion ClightPrivateRegionProof ClightPrivatePool ClightTempFootprint ClightTempScope.
From GuardMemory Require Import GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightDependentBoundSyntax ClightSignedExpressionProgress.
Import ListNotations.
Set Implicit Arguments.

Definition private_pointer_head (pool : list (ident * type)) :=
  match pool with [] => [] | (pointer,_)::rest => (pointer,signed_pointer_type)::rest end.
Definition propose_dependent_private_names live count := private_pointer_head (propose_private_names live count).
Lemma private_pointer_head_names pool : var_names (private_pointer_head pool) = var_names pool.
Proof. destruct pool as [|[pointer ty] rest]; reflexivity. Qed.
Lemma private_pointer_head_fresh live pool :
  private_pool_check live (private_pointer_head pool) = private_pool_check live pool.
Proof. unfold private_pool_check; rewrite private_pointer_head_names; reflexivity. Qed.

(** The source progress selector accepts actual signed expressions, including
    compound loads. Neither this host nor its pool assumes their stability. *)
Definition apply_dependent_region_table pool table (p : Clight.program) :=
  transform_private_program signed_expression_region_progress_supported
    (fun _ _ => select_memory_tiled_table table) pool p.
Theorem apply_dependent_region_table_correct pool table p :
  Forall (fun pair => PrivateRegion.projected_region_contract
    (program_temps p) (fst pair) (snd pair)) table ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (apply_dependent_region_table pool table p)).
Proof.
  intro TABLE; unfold apply_dependent_region_table,transform_private_program.
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

Print Assumptions private_pointer_head_names.
Print Assumptions private_pointer_head_fresh.
Print Assumptions apply_dependent_region_table_correct.
