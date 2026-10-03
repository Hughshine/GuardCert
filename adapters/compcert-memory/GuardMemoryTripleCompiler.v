From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPureExpr ClightPrivateRule ClightPrivateRegion ClightPrivatePool ClightSharedRegion ClightRectangularSelector.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryRegistryBackend GuardMemoryAffineReindex GuardMemoryScheduleProducer GuardMemoryTripleSyntax
  GuardMemoryTripleGuard GuardMemoryTripleRestore GuardMemoryTripleCandidate GuardMemoryTripleChecker GuardMemoryTripleTiling GuardMemoryNaryLoops.
From GuardMemory Require Import GuardMemoryTiledCompiler.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition compile_memory_triple_region_candidate source (package : memory_triple_region_package source) live pool candidate :=
  let d := triple_region_description package in
  compile_memory_registry_loop (memory_triple_region_descriptors package) (memory_triple_context d)
    (memory_triple_bounds (triple_cap d)) live pool candidate.
Definition memory_triple_region_arrays source (package : memory_triple_region_package source) :=
  map memory_descriptor_variable (memory_triple_region_descriptors package).
Definition memory_triple_region_target source (package : memory_triple_region_package source) code :=
  let d := triple_region_description package in
  shared_guarded_statement (decision_bind
    (memory_triple_guard_tree (triple_cap d) (memory_triple_region_descriptors package) (triple_row d) (triple_row_bound d)
      (triple_column_bound d) (triple_depth_bound d)) (Decision true) (Decision false))
    (memory_triple_candidate code d) source.
Theorem memory_triple_region_target_sound source (package : memory_triple_region_package source) live pairs candidate code :
  compile_memory_triple_region_candidate package live pairs candidate = Some code ->
  memory_triple_candidate_certificate (triple_cap (triple_region_description package)) (memory_triple_region_instructions package)
    (memory_triple_context (triple_region_description package)) candidate ->
  projected_region_contract live source (memory_triple_region_target package code).
Proof.
  intros COMPILE CHECK.
  change (projected_region_contract live source
    (generated_private_region (@memory_triple_candidate_rule source package live pairs candidate code COMPILE CHECK))).
  apply encoded_private_rule_sound.
Qed.
Definition check_memory_triple_region_candidate live pool source (package : memory_triple_region_package source)
  candidate (check : CoreAlarmed.Base.imp bool) : CoreAlarmed.Base.imp (option statement) :=
  match private_counter_pairs pool with
  | Some pairs => match compile_memory_triple_region_candidate package live pairs candidate with
      | Some code => BIND valid <- check -;
          pure (if valid then Some (memory_triple_region_target package code) else None)
      | None => pure None end
  | None => pure None end.
Theorem check_memory_triple_region_candidate_sound live pool source (package : memory_triple_region_package source) candidate check target :
  (mayReturn check true -> memory_triple_candidate_certificate (triple_cap (triple_region_description package))
    (memory_triple_region_instructions package) (memory_triple_context (triple_region_description package)) candidate) ->
  mayReturn (check_memory_triple_region_candidate live pool package candidate check) (Some target) ->
  projected_region_contract live source target.
Proof.
  intros CERT; unfold check_memory_triple_region_candidate.
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_triple_region_candidate package live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [inversion RUN; subst target|discriminate].
  eapply memory_triple_region_target_sound; [exact COMPILE|apply CERT; exact VALID].
Qed.
Definition check_memory_triple_mapped_region live pool
  (propose : list memory_instruction -> option (L.stmt*list memory_affine_reindex)) source :=
  match describe_memory_triple_region source with
  | Some package => match propose (memory_triple_region_instructions package) with
      | Some (candidate,steps) => let d := triple_region_description package in
          check_memory_triple_region_candidate live pool package candidate
            (checked_memory_triple_candidate (triple_cap d) (memory_triple_region_instructions package)
              (memory_triple_context d) (memory_triple_region_arrays package) candidate steps)
      | None => pure None end
  | None => pure None end.
Theorem check_memory_triple_mapped_region_sound live pool propose source target :
  mayReturn (check_memory_triple_mapped_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_triple_mapped_region; destruct (describe_memory_triple_region source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (memory_triple_region_instructions package)) as [[candidate steps]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  apply check_memory_triple_region_candidate_sound; apply checked_memory_triple_candidate_correct.
Qed.
Definition check_memory_triple_tiled_region live pool bi bj source :=
  match describe_memory_triple_region source with
  | Some package => if (0 <? bi) && (0 <? bj) then let d := triple_region_description package in
      check_memory_triple_region_candidate live pool package
        (memory_triple_tiled_loop (memory_triple_region_instructions package) bi bj true)
        (checked_memory_triple_tiling (triple_cap d) (memory_triple_region_instructions package)
          (memory_triple_context d) (memory_triple_region_arrays package) bi bj)
      else pure None
  | None => pure None end.
Theorem check_memory_triple_tiled_region_sound live pool bi bj source target :
  mayReturn (check_memory_triple_tiled_region live pool bi bj source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_triple_tiled_region; destruct (describe_memory_triple_region source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct ((0 <? bi) && (0 <? bj)) eqn:SIZE; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  apply andb_true_iff in SIZE as [BI BJ]; apply Z.ltb_lt in BI; apply Z.ltb_lt in BJ.
  apply check_memory_triple_region_candidate_sound; apply checked_memory_triple_tiling_correct; [reflexivity|exact BI|exact BJ].
Qed.
Definition check_memory_triple_scheduled_region live pool schedules steps source :=
  match describe_memory_triple_region source with
  | Some package => let d := triple_region_description package in
      let context := memory_triple_context d in
      let vars := map (fun array => (array,tt)) (context++memory_triple_region_arrays package) in
      BIND candidate <- memory_generate_scheduled_loop
        (memory_triple_assumed_loop (triple_cap d) (memory_nary_rectangle 0 3 (memory_triple_region_instructions package)),context,vars) schedules -;
      match candidate with
      | Some candidate => check_memory_triple_mapped_region live pool (fun _ => Some (candidate,steps)) source
      | None => pure None end
  | None => pure None end.
Theorem check_memory_triple_scheduled_region_sound live pool schedules steps source target :
  mayReturn (check_memory_triple_scheduled_region live pool schedules steps source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_triple_scheduled_region; destruct (describe_memory_triple_region source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN candidate GENERATED; destruct candidate as [candidate|];
    [eapply check_memory_triple_mapped_region_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.
Print Assumptions check_memory_triple_mapped_region_sound.
Print Assumptions check_memory_triple_tiled_region_sound.
Print Assumptions check_memory_triple_scheduled_region_sound.
