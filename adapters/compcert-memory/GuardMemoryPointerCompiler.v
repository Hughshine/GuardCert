From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPureExpr ClightPrivateRule ClightPrivateRegion
  ClightPrivatePool ClightSharedRegion ClightRectangularSelector.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryRegistryBackend GuardMemoryAffineReindex GuardMemoryScheduleProducer GuardMemoryRecursiveSource
  GuardMemoryRecursiveSyntax GuardMemoryRecursiveGuard GuardMemoryRecursiveRestore GuardMemoryRecursiveCandidate
  GuardMemoryRecursiveChecker GuardMemoryRecursiveTiling GuardMemoryNaryLoops GuardMemoryTiledCompiler
  GuardMemoryPointerSyntax GuardMemoryPointerCandidate GuardMemoryPointerBackend GuardMemoryPointerConditionSearch.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition compile_memory_pointer_region_candidate source (package : memory_pointer_region_package source) live pool candidate :=
  compile_memory_pointer_buffer_loop (pointer_region_pointer package) (pointer_region_pointer package)
    (memory_nest_bounds (pointer_region_nest package))
    (memory_pointer_static_bounds (length (memory_nest_iterators (pointer_region_nest package)))
      (pointer_region_limit package)) live pool candidate.
Definition memory_pointer_region_arrays source (package : memory_pointer_region_package source) := [pointer_region_pointer package].
Definition memory_pointer_region_target source (package : memory_pointer_region_package source) code :=
  shared_guarded_statement (decision_bind (memory_recursive_guard_tree (pointer_region_limit package)
    [] (pointer_region_nest package)) (Decision true) (Decision false))
    (memory_recursive_candidate code (pointer_region_nest package)) source.
Theorem memory_pointer_region_target_sound source (package : memory_pointer_region_package source) live pairs candidate code :
  compile_memory_pointer_region_candidate package live pairs candidate = Some code ->
  memory_recursive_candidate_certificate (length (memory_nest_iterators (pointer_region_nest package)))
    (pointer_region_limit package) (memory_pointer_region_instructions package)
    (memory_nest_bounds (pointer_region_nest package)) candidate ->
  projected_region_contract live source (memory_pointer_region_target package code).
Proof.
  intros COMPILE CHECK.
  change (projected_region_contract live source
    (generated_private_region (@memory_pointer_candidate_rule source package live pairs candidate code COMPILE CHECK))).
  apply encoded_private_rule_sound.
Qed.
Definition check_memory_pointer_region_candidate live pool source (package : memory_pointer_region_package source)
  candidate (check : CoreAlarmed.Base.imp bool) : CoreAlarmed.Base.imp (option statement) :=
  match private_counter_pairs pool with
  | Some pairs => match compile_memory_pointer_region_candidate package live pairs candidate with
      | Some code => BIND valid <- check -;
          pure (if valid then Some (memory_pointer_region_target package code) else None)
      | None => pure None end
  | None => pure None end.
Theorem check_memory_pointer_region_candidate_sound live pool source (package : memory_pointer_region_package source) candidate check target :
  (mayReturn check true -> memory_recursive_candidate_certificate (length (memory_nest_iterators (pointer_region_nest package)))
    (pointer_region_limit package) (memory_pointer_region_instructions package)
    (memory_nest_bounds (pointer_region_nest package)) candidate) ->
  mayReturn (check_memory_pointer_region_candidate live pool package candidate check) (Some target) ->
  projected_region_contract live source target.
Proof.
  intros CERT; unfold check_memory_pointer_region_candidate.
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_pointer_region_candidate package live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [inversion RUN; subst target|discriminate].
  eapply memory_pointer_region_target_sound; [exact COMPILE|apply CERT; exact VALID].
Qed.
Section SERVICES.
Variable describe : memory_pointer_describer.
Definition check_memory_pointer_mapped_at live pool
  (propose : list memory_instruction -> option (L.stmt*list memory_affine_reindex)) source :=
  match describe source with
  | Some package => match propose (memory_pointer_region_instructions package) with
      | Some (candidate,steps) => let nest := pointer_region_nest package in
          check_memory_pointer_region_candidate live pool package candidate
            (checked_memory_recursive_candidate (length (memory_nest_iterators nest)) (pointer_region_limit package)
              (memory_pointer_region_instructions package) (memory_nest_bounds nest)
              (memory_pointer_region_arrays package) candidate steps)
      | None => pure None end
  | None => pure None end.
Theorem check_memory_pointer_mapped_at_sound live pool propose source target :
  mayReturn (check_memory_pointer_mapped_at live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_pointer_mapped_at; destruct (describe source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (memory_pointer_region_instructions package)) as [[candidate steps]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  apply check_memory_pointer_region_candidate_sound; apply checked_memory_recursive_candidate_correct.
Qed.
Definition check_memory_pointer_tiled_at live pool bi bj source :=
  match describe source with
  | Some package => let dimensions := length (memory_nest_iterators (pointer_region_nest package)) in
      if (2 <=? dimensions)%nat && (0 <? bi) && (0 <? bj) then
        check_memory_pointer_region_candidate live pool package
          (memory_recursive_tiled_loop dimensions (memory_pointer_region_instructions package) bi bj true)
          (checked_memory_recursive_tiling dimensions (pointer_region_limit package) (memory_pointer_region_instructions package)
            (memory_nest_bounds (pointer_region_nest package)) (memory_pointer_region_arrays package) bi bj)
      else pure None
  | None => pure None end.
Theorem check_memory_pointer_tiled_at_sound live pool bi bj source target :
  mayReturn (check_memory_pointer_tiled_at live pool bi bj source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_pointer_tiled_at; destruct (describe source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct ((2 <=? length (memory_nest_iterators (pointer_region_nest package)))%nat && (0 <? bi) && (0 <? bj)) eqn:SIZE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  rewrite !andb_true_iff,Nat.leb_le,Z.ltb_lt,Z.ltb_lt in SIZE; destruct SIZE as [[DIMENSIONS BI] BJ].
  apply check_memory_pointer_region_candidate_sound; apply checked_memory_recursive_tiling_correct;
    [symmetry; apply memory_nest_lengths|exact DIMENSIONS|exact BI|exact BJ].
Qed.
Definition check_memory_pointer_scheduled_at live pool schedules steps source :=
  match describe source with
  | Some package => let nest := pointer_region_nest package in let context := memory_nest_bounds nest in
      let vars := map (fun array => (array,tt)) (context++memory_pointer_region_arrays package) in
      BIND candidate <- memory_generate_scheduled_loop
        (memory_recursive_assumed_loop (length (memory_nest_iterators nest)) (pointer_region_limit package)
          (memory_nary_rectangle 0 (length (memory_nest_iterators nest)) (memory_pointer_region_instructions package)),context,vars) schedules -;
      match candidate with
      | Some candidate => check_memory_pointer_mapped_at live pool (fun _ => Some (candidate,steps)) source
      | None => pure None end
  | None => pure None end.
Theorem check_memory_pointer_scheduled_at_sound live pool schedules steps source target :
  mayReturn (check_memory_pointer_scheduled_at live pool schedules steps source) (Some target) -> projected_region_contract live source target.
Proof.
  unfold check_memory_pointer_scheduled_at; destruct (describe source) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN candidate GENERATED; destruct candidate as [candidate|];
    [eapply check_memory_pointer_mapped_at_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.
End SERVICES.
Definition memory_pointer_search_caps : list Z := [2147483647;8;4;3;2;1].
Definition check_memory_pointer_mapped_region live pool propose source :=
  check_memory_pointer_caps (fun describe => check_memory_pointer_mapped_at describe live pool propose) memory_pointer_search_caps source.
Theorem check_memory_pointer_mapped_region_sound live pool propose source target :
  mayReturn (check_memory_pointer_mapped_region live pool propose source) (Some target) -> projected_region_contract live source target.
Proof.
  apply check_memory_pointer_caps_sound; intros describe original chosen RUN.
  eapply check_memory_pointer_mapped_at_sound; exact RUN.
Qed.
Definition check_memory_pointer_tiled_region live pool bi bj source :=
  check_memory_pointer_caps (fun describe => check_memory_pointer_tiled_at describe live pool bi bj) memory_pointer_search_caps source.
Theorem check_memory_pointer_tiled_region_sound live pool bi bj source target :
  mayReturn (check_memory_pointer_tiled_region live pool bi bj source) (Some target) -> projected_region_contract live source target.
Proof.
  apply check_memory_pointer_caps_sound; intros describe original chosen RUN.
  eapply check_memory_pointer_tiled_at_sound; exact RUN.
Qed.
Definition check_memory_pointer_scheduled_region live pool schedules steps source :=
  check_memory_pointer_caps (fun describe => check_memory_pointer_scheduled_at describe live pool schedules steps) memory_pointer_search_caps source.
Theorem check_memory_pointer_scheduled_region_sound live pool schedules steps source target :
  mayReturn (check_memory_pointer_scheduled_region live pool schedules steps source) (Some target) -> projected_region_contract live source target.
Proof.
  apply check_memory_pointer_caps_sound; intros describe original chosen RUN.
  eapply check_memory_pointer_scheduled_at_sound; exact RUN.
Qed.
Print Assumptions check_memory_pointer_mapped_region_sound.
Print Assumptions check_memory_pointer_tiled_region_sound.
Print Assumptions check_memory_pointer_scheduled_region_sound.
