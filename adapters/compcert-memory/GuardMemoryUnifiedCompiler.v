From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy SimplExpr SimplExprproof
  SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCondition ClightPrivateRule ClightPrivateRegion
  ClightPrivateRegionProof ClightPrivatePool ClightTempFootprint ClightTempScope
  ClightStructuredProgress ClightRectangularSelector ClightRectangularStore
  ClightRectangularGuard ClightRectangularRegion ClightRectangularLoops GuardCompiler
  ClightFrontendLoopProtocol ClightFrontendRegion ClightStraightLine ClightSharedRegion ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryClightRectangles GuardMemoryCompiler GuardMemoryTiledClight GuardMemoryTiledCompiler
  GuardMemoryArrayFamilyBackend GuardMemoryOperationsClight GuardMemoryOperationsTiledClight GuardMemoryOperationsCompiler
  GuardMemoryInstr GuardMemoryLoops GuardMemoryProposedClight GuardMemoryProposedCompiler
  GuardMemoryNamedOperations GuardMemoryNamedCompiler GuardMemoryAffineReindex GuardMemoryNamedMappedCompiler GuardMemoryNamedRaggedCompiler
  GuardMemoryScheduledCompiler GuardMemoryParametricSyntax GuardMemoryParametricCompiler.
Import CoreAlarmed ListNotations PrivateRegion.
Import Clight.
Set Implicit Arguments.
Local Open Scope Z_scope.

Inductive guarded_memory_candidate :=
| GuardedAffineCandidate (candidate : L.stmt) (swaps : list nat)
| GuardedMappedCandidate (candidate : L.stmt) (steps : list memory_affine_reindex)
| GuardedTilingCandidate (rows columns : Z)
| GuardedScheduleCandidate (schedules : list (list (list Z * Z))) (steps : list memory_affine_reindex).
Definition guarded_memory_proposer := list memory_instruction -> option guarded_memory_candidate.
Definition check_memory_parametric_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_parametric source with
  | Some package =>
    match propose (map named_operation_instruction (parametric_operations package)) with
    | Some (GuardedAffineCandidate candidate swaps) =>
      check_memory_parametric_mapped_region live pool (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source
    | Some (GuardedMappedCandidate candidate steps) =>
      check_memory_parametric_mapped_region live pool (fun _ => Some (candidate,steps)) source
    | Some (GuardedTilingCandidate rows columns) => check_memory_parametric_tiled_region live pool rows columns source
    | Some (GuardedScheduleCandidate schedules steps) => check_memory_parametric_scheduled_region live pool schedules steps source
    | None => CoreAlarmed.Base.pure None end
  | None => CoreAlarmed.Base.pure None end.
Theorem check_memory_parametric_unified_region_sound live pool propose source target :
  mayReturn (check_memory_parametric_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_parametric_unified_region.
  destruct (describe_memory_parametric source) as [package|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (propose (map named_operation_instruction (parametric_operations package))) as [candidate|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct candidate; intro CHECK.
  - eapply check_memory_parametric_mapped_region_sound; exact CHECK.
  - eapply check_memory_parametric_mapped_region_sound; exact CHECK.
  - eapply check_memory_parametric_tiled_region_sound; exact CHECK.
  - eapply check_memory_parametric_scheduled_region_sound; exact CHECK.
Qed.
Definition check_memory_ragged_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_ragged source with
  | Some package =>
    match propose (map named_operation_instruction (ragged_operations package)) with
    | Some (GuardedAffineCandidate candidate swaps) =>
      check_memory_ragged_mapped_region live pool
        (fun _ => Some (candidate,map MemoryReindexSwap swaps)) source
    | Some (GuardedMappedCandidate candidate steps) =>
      check_memory_ragged_mapped_region live pool (fun _ => Some (candidate,steps)) source
    | Some (GuardedTilingCandidate rows columns) => check_memory_ragged_tiled_region live pool rows columns source
    | Some (GuardedScheduleCandidate schedules steps) => check_memory_ragged_scheduled_region live pool schedules steps source
    | None => CoreAlarmed.Base.pure None end
  | None => check_memory_parametric_unified_region live pool propose source end.
Theorem check_memory_ragged_unified_region_sound live pool propose source target :
  mayReturn (check_memory_ragged_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_ragged_unified_region.
  destruct (describe_memory_ragged source) as [package|];
    [|apply check_memory_parametric_unified_region_sound].
  destruct (propose (map named_operation_instruction (ragged_operations package))) as [candidate|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct candidate; intro CHECK.
  - eapply check_memory_ragged_mapped_region_sound; exact CHECK.
  - eapply check_memory_ragged_mapped_region_sound; exact CHECK.
  - eapply check_memory_ragged_tiled_region_sound; exact CHECK.
  - eapply check_memory_ragged_scheduled_region_sound; exact CHECK.
Qed.
Definition check_memory_named_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_named source with
  | Some package =>
    match propose (map named_operation_instruction (named_operations package)) with
    | Some (GuardedAffineCandidate candidate swaps) =>
      check_memory_named_affine_region live pool (fun _ => Some (candidate,swaps)) source
    | Some (GuardedMappedCandidate candidate steps) =>
      check_memory_named_mapped_region live pool (fun _ => Some (candidate,steps)) source
    | Some (GuardedTilingCandidate rows columns) => check_memory_named_tiled_region live pool rows columns source
    | Some (GuardedScheduleCandidate schedules steps) => check_memory_named_scheduled_region live pool schedules steps source
    | None => CoreAlarmed.Base.pure None end
  | None => check_memory_ragged_unified_region live pool propose source end.
Theorem check_memory_named_unified_region_sound live pool propose source target :
  mayReturn (check_memory_named_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_named_unified_region.
  destruct (describe_memory_named source) as [package|];
    [|apply check_memory_ragged_unified_region_sound].
  destruct (propose (map named_operation_instruction (named_operations package))) as [candidate|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct candidate; intro CHECK.
  - eapply check_memory_named_affine_region_sound; exact CHECK.
  - eapply check_memory_named_mapped_region_sound; exact CHECK.
  - eapply check_memory_named_tiled_region_sound; exact CHECK.
  - eapply check_memory_named_scheduled_region_sound; exact CHECK.
Qed.
Definition check_memory_unified_region live pool (propose : guarded_memory_proposer) source :=
  match describe_memory_operations source with
  | Some package =>
    match propose (map (operation_instruction 3%positive) (operations_list package)) with
    | Some (GuardedAffineCandidate candidate swaps) =>
      check_memory_proposed_region live pool (fun _ => Some (candidate,swaps)) source
    | Some (GuardedMappedCandidate candidate steps) =>
      check_memory_named_unified_region live pool propose source
    | Some (GuardedTilingCandidate rows columns) =>
      check_memory_operations_region live pool rows columns source
    | Some (GuardedScheduleCandidate schedules steps) =>
      check_memory_named_scheduled_region live pool schedules steps source
    | None => CoreAlarmed.Base.pure None end
  | None => check_memory_named_unified_region live pool propose source end.
Theorem check_memory_unified_region_sound live pool propose source target :
  mayReturn (check_memory_unified_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_unified_region.
  destruct (describe_memory_operations source) as [package|];
    [|apply check_memory_named_unified_region_sound].
  destruct (propose (map (operation_instruction 3%positive) (operations_list package))) as [candidate|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct candidate; intro CHECK.
  - eapply check_memory_proposed_region_sound; exact CHECK.
  - eapply check_memory_named_unified_region_sound; exact CHECK.
  - eapply check_memory_operations_region_sound; exact CHECK.
  - eapply check_memory_named_scheduled_region_sound; exact CHECK.
Qed.
Fixpoint checked_memory_unified_regions live pool propose sources : CoreAlarmed.Base.imp (list (statement * statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND candidate <- check_memory_unified_region live pool propose source -;
    BIND table <- checked_memory_unified_regions live pool propose rest -;
    pure (match candidate with Some target => (source,target)::table | None => table end)
  end.
Lemma checked_memory_unified_regions_sound live pool propose sources table :
  mayReturn (checked_memory_unified_regions live pool propose sources) table ->
  Forall (fun pair => projected_region_contract live (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources; intros table CHECK; cbn in CHECK.
  - apply mayReturn_pure in CHECK; subst table; constructor.
  - bind_imp_destruct CHECK candidate CANDIDATE; bind_imp_destruct CHECK rest REST.
    apply mayReturn_pure in CHECK; destruct candidate as [target|]; subst table; [constructor|];
      eauto using check_memory_unified_region_sound.
Qed.
Definition compile_memory_unified_regions propose private_count (program : Csyntax.program) : CoreAlarmed.Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      let live := program_temps normalized in
      let pool := propose_private_names live private_count in
      BIND table <- checked_memory_unified_regions live pool propose (memory_program_candidates normalized) -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight
        (apply_memory_tiled_table pool table normalized)))
    end
  end.
Theorem memory_unified_cstrategy_forward propose private_count program target :
  mayReturn (compile_memory_unified_regions propose private_count program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_memory_unified_regions; destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1.
  2: intro COMPILED; apply mayReturn_pure in COMPILED; discriminate.
  destruct (SimplLocals.transf_program clight) as [normalized|errors] eqn:P2.
  2: intro COMPILED; apply mayReturn_pure in COMPILED; discriminate.
  intro COMPILED; bind_imp_destruct COMPILED table TABLE.
  apply mayReturn_pure in COMPILED; rewrite Compiler.print_identity in COMPILED.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply apply_memory_tiled_table_correct; eapply checked_memory_unified_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact COMPILED.
Qed.
Theorem compile_memory_unified_regions_correct propose private_count program target :
  mayReturn (compile_memory_unified_regions propose private_count program) (OK target) ->
  backward_simulation (Csem.semantics program) (Asm.semantics target).
Proof.
  intro COMPILED.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics program)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * apply memory_unified_cstrategy_forward with (propose := propose) (private_count := private_count); exact COMPILED.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions compile_memory_unified_regions_correct.
