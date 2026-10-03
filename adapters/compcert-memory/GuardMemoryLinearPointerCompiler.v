From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryAffineReindex
  GuardMemoryRecursiveSource GuardMemoryRecursiveCandidate GuardMemoryRecursiveChecker
  GuardMemoryScalarChecker GuardMemoryScalarLoops GuardMemoryScalarCandidates GuardMemoryScheduleProducer
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerCompiler GuardMemoryMultiPointerProjectedCandidate
  GuardMemoryLinearPointerSyntax GuardMemoryLinearPointerPair GuardMemoryLinearPointerGuard GuardMemoryProjectedCondition
  GuardMemoryRecursiveSyntax GuardMemoryTiledCompiler GuardMemorySequentialCondition.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_linear_pointer_guard_names_check source (package : memory_linear_pointer_pair_package source) live x y flag :=
  memory_identifiers_unique_check [x;y;flag;linear_pointer_bound (linear_pointer_pair_region package)] &&
  forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_linear_pointer_guard_protected package live))) [x;y;flag].

Lemma memory_linear_pointer_guard_names_sound source (package : memory_linear_pointer_pair_package source) live x y flag :
  memory_linear_pointer_guard_names_check package live x y flag = true ->
  NoDup [x;y;flag;linear_pointer_bound (linear_pointer_pair_region package)] /\
  ~ In x (memory_linear_pointer_guard_protected package live) /\
  ~ In y (memory_linear_pointer_guard_protected package live) /\
  ~ In flag (memory_linear_pointer_guard_protected package live).
Proof.
  unfold memory_linear_pointer_guard_names_check; rewrite andb_true_iff; intros [UNIQUE FRESH].
  assert (ALL : forall identifier, In identifier [x;y;flag] ->
    ~ In identifier (memory_linear_pointer_guard_protected package live)).
  { intros identifier MEMBER BAD; apply forallb_forall with (x := identifier) in FRESH; [|exact MEMBER].
    apply negb_true_iff in FRESH; assert (FOUND : existsb (Pos.eqb identifier) (memory_linear_pointer_guard_protected package live) = true).
    { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. } congruence. }
  split; [apply memory_identifiers_unique_check_sound; exact UNIQUE|repeat split; apply ALL; cbn; auto].
Qed.

Definition memory_linear_pointer_region_target source (package : memory_linear_pointer_pair_package source) x y flag code :=
  memory_sequential_guarded_statement (memory_linear_pointer_guard_statement package x y flag)
    (memory_recursive_candidate code (multi_pointer_region_nest (linear_pointer_region (linear_pointer_pair_region package)))) source.

Theorem memory_linear_pointer_region_target_sound source (package : memory_linear_pointer_pair_package source) live pairs candidate code x y flag :
  memory_linear_pointer_guard_names_check package live x y flag = true ->
  compile_memory_multi_pointer_region_candidate (linear_pointer_region (linear_pointer_pair_region package)) live pairs candidate = Some code ->
  memory_scalar_candidate_certificate (length (memory_nest_iterators (multi_pointer_region_nest (linear_pointer_region (linear_pointer_pair_region package)))))
    (multi_pointer_region_limit (linear_pointer_region (linear_pointer_pair_region package)))
    (memory_multi_pointer_region_arity (linear_pointer_region (linear_pointer_pair_region package)))
    (memory_multi_pointer_region_instructions (linear_pointer_region (linear_pointer_pair_region package)))
    (memory_multi_pointer_region_context (linear_pointer_region (linear_pointer_pair_region package))) candidate ->
  projected_region_contract live source (memory_linear_pointer_region_target package x y flag code).
Proof.
  intros NAMES COMPILE CHECK; destruct (@memory_linear_pointer_guard_names_sound source package live x y flag NAMES) as [UNIQUE [X [Y FLAG]]].
  unfold memory_linear_pointer_region_target.
  eapply memory_projected_private_rule_sound with
    (rule := @memory_multi_pointer_projected_candidate_rule source (linear_pointer_region (linear_pointer_pair_region package))
      live pairs candidate code COMPILE CHECK).
  intros fe s DOMAIN; eapply memory_linear_pointer_guard_execution; eassumption.
Qed.

Definition check_memory_linear_pointer_region_candidate live pool source (package : memory_linear_pointer_pair_package source)
  candidate (check : CoreAlarmed.Base.imp bool) : CoreAlarmed.Base.imp (option statement) :=
  match private_counter_pairs pool with
  | Some (((x,y)::(flag,spare)::rest) as pairs) =>
      if memory_linear_pointer_guard_names_check package live x y flag then
        match compile_memory_multi_pointer_region_candidate (linear_pointer_region (linear_pointer_pair_region package)) live pairs candidate with
        | Some code => BIND valid <- check -;
            pure (if valid then Some (memory_linear_pointer_region_target package x y flag code) else None)
        | None => pure None end
      else pure None
  | _ => pure None end.

Theorem check_memory_linear_pointer_region_candidate_sound live pool source (package : memory_linear_pointer_pair_package source) candidate check target :
  (mayReturn check true -> memory_scalar_candidate_certificate
    (length (memory_nest_iterators (multi_pointer_region_nest (linear_pointer_region (linear_pointer_pair_region package)))))
    (multi_pointer_region_limit (linear_pointer_region (linear_pointer_pair_region package)))
    (memory_multi_pointer_region_arity (linear_pointer_region (linear_pointer_pair_region package)))
    (memory_multi_pointer_region_instructions (linear_pointer_region (linear_pointer_pair_region package)))
    (memory_multi_pointer_region_context (linear_pointer_region (linear_pointer_pair_region package))) candidate) ->
  mayReturn (check_memory_linear_pointer_region_candidate live pool package candidate check) (Some target) ->
  projected_region_contract live source target.
Proof.
  intros CERT; unfold check_memory_linear_pointer_region_candidate.
  destruct (private_counter_pairs pool) as [[|[x y] [|[flag spare] rest]]|];
    try (intro RUN; apply mayReturn_pure in RUN; discriminate).
  destruct (memory_linear_pointer_guard_names_check package live x y flag) eqn:NAMES;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_multi_pointer_region_candidate (linear_pointer_region (linear_pointer_pair_region package)) live ((x,y)::(flag,spare)::rest) candidate)
    as [code|] eqn:COMPILE; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [inversion RUN; subst target|discriminate].
  eapply memory_linear_pointer_region_target_sound; [exact NAMES|exact COMPILE|apply CERT; exact VALID].
Qed.

Definition check_memory_linear_pointer_mapped_package live pool source (package : memory_linear_pointer_pair_package source) raw_candidate steps :=
  let region := linear_pointer_region (linear_pointer_pair_region package) in
  let dimensions := length (memory_nest_iterators (multi_pointer_region_nest region)) in
  let candidate := memory_carry_scalar_arguments 0 dimensions (memory_multi_pointer_region_arity region) raw_candidate in
  check_memory_linear_pointer_region_candidate live pool package candidate
    (checked_memory_scalar_candidate dimensions (multi_pointer_region_limit region)
      (memory_multi_pointer_region_arity region) (memory_multi_pointer_region_instructions region)
      (memory_multi_pointer_region_context region) (memory_multi_pointer_region_arrays region) candidate steps).
Theorem check_memory_linear_pointer_mapped_package_sound live pool source (package : memory_linear_pointer_pair_package source) candidate steps target :
  mayReturn (check_memory_linear_pointer_mapped_package live pool package candidate steps) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_linear_pointer_mapped_package; apply check_memory_linear_pointer_region_candidate_sound;
    apply checked_memory_scalar_candidate_correct.
Qed.

Definition check_memory_linear_pointer_scheduled_package live pool source (package : memory_linear_pointer_pair_package source) schedules steps :=
  let region := linear_pointer_region (linear_pointer_pair_region package) in
  let dimensions := length (memory_nest_iterators (multi_pointer_region_nest region)) in
  let context := memory_multi_pointer_region_context region in
  let vars := map (fun identifier => (identifier,tt)) (context++memory_multi_pointer_region_arrays region) in
  BIND candidate <- memory_generate_scheduled_loop
    (memory_recursive_assumed_loop dimensions (multi_pointer_region_limit region)
      (memory_scalar_rectangle 0 dimensions (memory_multi_pointer_region_arity region)
        (memory_multi_pointer_region_instructions region)),context,vars) schedules -;
  match candidate with
  | Some candidate => check_memory_linear_pointer_mapped_package live pool package candidate steps
  | None => pure None end.
Theorem check_memory_linear_pointer_scheduled_package_sound live pool source (package : memory_linear_pointer_pair_package source) schedules steps target :
  mayReturn (check_memory_linear_pointer_scheduled_package live pool package schedules steps) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_linear_pointer_scheduled_package; intro RUN;
    bind_imp_destruct RUN candidate GENERATED; destruct candidate as [candidate|];
    [eapply check_memory_linear_pointer_mapped_package_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.

Print Assumptions check_memory_linear_pointer_mapped_package_sound.
Print Assumptions check_memory_linear_pointer_scheduled_package_sound.
