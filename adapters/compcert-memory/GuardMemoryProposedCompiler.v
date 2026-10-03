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
  GuardMemoryInstr GuardMemoryLoops GuardMemoryProposedClight.
Import CoreAlarmed ListNotations PrivateRegion.
Import Clight.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_candidate_proposer := list memory_instruction -> option (L.stmt * list nat).
Definition memory_proposed_target source (package : memory_operations_package source) code :=
  memory_operations_target package code.
Theorem memory_proposed_target_sound source (package : memory_operations_package source) live pairs candidate swaps code :
  compile_array_operations_candidate (described_shape (operations_description package)) (operations_list package)
    (described_array (operations_description package)) (rectangle_bound (operations_description package))
    (rectangle_inner_bound (operations_description package)) live pairs candidate = Some code ->
  mayReturn (checked_array_operations_candidate (described_shape (operations_description package)) (operations_list package) candidate swaps) true ->
  projected_region_contract live source (memory_proposed_target package code).
Proof.
  destruct package as [d shapes CERT]; cbn; intros COMPILE CHECK.
  destruct CERT as [SOURCE BODY OUTER RN RC NC RM CM VALID LAYOUTS NONEMPTY]; subst source.
  unfold memory_proposed_target,memory_operations_target,rectangle_described_source; cbn.
  change (projected_region_contract live
    (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (generated_private_region (@memory_proposed_array_operations_rule (described_shape d) VALID shapes LAYOUTS NONEMPTY
      (described_array d) (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d) RN RC NC RM CM BODY OUTER
      live pairs candidate swaps code COMPILE CHECK))).
  apply encoded_private_rule_sound.
Qed.
Definition check_memory_proposed_region live pool (propose : memory_candidate_proposer) source : CoreAlarmed.Base.imp (option statement) :=
  match private_counter_pairs pool,describe_memory_operations source with
  | Some pairs,Some package =>
    let d := operations_description package in
    match propose (map (operation_instruction 3%positive) (operations_list package)) with
    | Some (candidate,swaps) => match compile_array_operations_candidate (described_shape d) (operations_list package)
        (described_array d) (rectangle_bound d) (rectangle_inner_bound d) live pairs candidate with
      | Some code => BIND valid <- checked_array_operations_candidate (described_shape d) (operations_list package) candidate swaps -;
        pure (if valid then Some (memory_proposed_target package code) else None)
      | None => pure None end
    | None => pure None end
  | _,_ => pure None end.
Theorem check_memory_proposed_region_sound live pool propose source target :
  mayReturn (check_memory_proposed_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_proposed_region.
  destruct (private_counter_pairs pool) as [pairs|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (describe_memory_operations source) as [package|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (propose (map (operation_instruction 3%positive) (operations_list package))) as [[candidate swaps]|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (compile_array_operations_candidate (described_shape (operations_description package)) (operations_list package)
    (described_array (operations_description package)) (rectangle_bound (operations_description package))
    (rectangle_inner_bound (operations_description package)) live pairs candidate) as [code|] eqn:COMPILE;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  intro CHECK; bind_imp_destruct CHECK valid VALID; apply mayReturn_pure in CHECK.
  destruct valid; [inversion CHECK; subst target|discriminate].
  apply memory_proposed_target_sound with (pairs := pairs) (candidate := candidate) (swaps := swaps); assumption.
Qed.
Fixpoint checked_memory_proposed_regions live pool propose sources : CoreAlarmed.Base.imp (list (statement * statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND candidate <- check_memory_proposed_region live pool propose source -;
    BIND table <- checked_memory_proposed_regions live pool propose rest -;
    pure (match candidate with Some target => (source,target)::table | None => table end)
  end.
Lemma checked_memory_proposed_regions_sound live pool propose sources table :
  mayReturn (checked_memory_proposed_regions live pool propose sources) table ->
  Forall (fun pair => projected_region_contract live (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources; intros table CHECK; cbn in CHECK.
  - apply mayReturn_pure in CHECK; subst table; constructor.
  - bind_imp_destruct CHECK candidate CANDIDATE; bind_imp_destruct CHECK rest REST.
    apply mayReturn_pure in CHECK; destruct candidate as [target|]; subst table; [constructor|];
      eauto using check_memory_proposed_region_sound.
Qed.
Definition compile_memory_proposed_regions propose private_count (program : Csyntax.program) : CoreAlarmed.Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      let live := program_temps normalized in
      let pool := propose_private_names live private_count in
      BIND table <- checked_memory_proposed_regions live pool propose (memory_program_candidates normalized) -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight
        (apply_memory_tiled_table pool table normalized)))
    end
  end.
Theorem memory_proposed_cstrategy_forward propose private_count program target :
  mayReturn (compile_memory_proposed_regions propose private_count program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_memory_proposed_regions; destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1.
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
  { apply apply_memory_tiled_table_correct; eapply checked_memory_proposed_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact COMPILED.
Qed.
Theorem compile_memory_proposed_regions_correct propose private_count program target :
  mayReturn (compile_memory_proposed_regions propose private_count program) (OK target) ->
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
      * apply memory_proposed_cstrategy_forward with (propose := propose) (private_count := private_count); exact COMPILED.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions compile_memory_proposed_regions_correct.
