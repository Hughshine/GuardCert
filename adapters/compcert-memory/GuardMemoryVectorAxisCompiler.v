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
  GuardMemoryLinearPointerSyntax GuardMemoryProjectedCondition GuardMemoryRecursiveSyntax
  GuardMemoryTiledCompiler GuardMemorySequentialCondition GuardMemoryStatefulRule.
From GuardMemory Require Import GuardMemoryAxisPointerFrame GuardMemoryAxisPointerGuard.
From GuardMemory Require Import GuardMemoryMultiPointerBackend.
From GuardMemory Require Import GuardMemoryVectorGuard GuardMemoryVectorChecker GuardMemoryVectorPointerBounds
  GuardMemoryVectorPointerSyntax GuardMemoryVectorPointerProjectedCandidate GuardMemoryVectorAxisFrame GuardMemoryVectorAxisGuard.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_vector_pointer_region_context source (package : memory_vector_pointer_region_package source) :=
  memory_vector_pointer_runtime_context package.
Definition memory_vector_pointer_region_arity source (package : memory_vector_pointer_region_package source) :=
  length (vector_pointer_region_scalars package).
Definition memory_vector_pointer_region_arrays source (package : memory_vector_pointer_region_package source) :=
  vector_pointer_region_pointers package.
Definition compile_memory_vector_pointer_region_candidate source (package : memory_vector_pointer_region_package source) live pool candidate :=
  compile_memory_multi_pointer_buffer_loop (vector_pointer_region_pointers package) (memory_vector_pointer_region_context package)
    (memory_vector_pointer_static_bounds (vector_pointer_region_limits package) (memory_vector_pointer_region_arity package)) live pool candidate.

Definition memory_vector_axis_pointer_guard_names_check source (package : memory_vector_pointer_region_package source)
  live left_counters right_counters flag :=
  Nat.eqb (length left_counters) (length (memory_nest_iterators (vector_pointer_region_nest package))) &&
  Nat.eqb (length right_counters) (length (memory_nest_iterators (vector_pointer_region_nest package))) &&
  memory_identifiers_unique_check ((left_counters++right_counters)++[flag]) &&
  forallb (fun identifier => negb (existsb (Pos.eqb identifier) (memory_vector_axis_pointer_guard_protected package live)))
    ((left_counters++right_counters)++[flag]).

Lemma memory_vector_axis_pointer_guard_names_sound source (package : memory_vector_pointer_region_package source)
  live left_counters right_counters flag :
  memory_vector_axis_pointer_guard_names_check package live left_counters right_counters flag = true ->
  length left_counters = length (memory_nest_iterators (vector_pointer_region_nest package)) /\
  length right_counters = length (memory_nest_iterators (vector_pointer_region_nest package)) /\
  NoDup (left_counters++right_counters) /\
  (forall identifier, In identifier (left_counters++right_counters) ->
    ~ In identifier (memory_vector_axis_pointer_guard_protected package live) /\ identifier <> flag) /\
  ~ In flag (memory_vector_axis_pointer_guard_protected package live).
Proof.
  unfold memory_vector_axis_pointer_guard_names_check; rewrite !andb_true_iff,!Nat.eqb_eq.
  intros [[[LEFT RIGHT] UNIQUE] FRESH].
  apply memory_identifiers_unique_check_sound in UNIQUE.
  pose proof (@NoDup_app_remove_r _ (left_counters++right_counters) [flag] UNIQUE) as COUNTERS.
  pose proof (@NoDup_remove_2 _ (left_counters++right_counters) [] flag UNIQUE) as FLAG_PRIVATE.
  rewrite app_nil_r in FLAG_PRIVATE.
  assert (ALL : forall identifier, In identifier ((left_counters++right_counters)++[flag]) ->
    ~ In identifier (memory_vector_axis_pointer_guard_protected package live)).
  { intros identifier MEMBER BAD; apply forallb_forall with (x := identifier) in FRESH; [|exact MEMBER].
    apply negb_true_iff in FRESH.
    assert (FOUND : existsb (Pos.eqb identifier) (memory_vector_axis_pointer_guard_protected package live) = true).
    { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. } congruence. }
  split; [exact LEFT|split; [exact RIGHT|split; [exact COUNTERS|split]]].
  - intros identifier MEMBER; split; [apply ALL; apply in_or_app; left; exact MEMBER|].
    intro SAME; subst; apply FLAG_PRIVATE; exact MEMBER.
  - apply ALL; apply in_or_app; right; cbn; auto.
Qed.

Definition memory_vector_axis_pointer_region_target source (package : memory_vector_pointer_region_package source)
  left_counters right_counters flag code :=
  memory_sequential_guarded_statement
    (memory_vector_axis_pointer_guard_statement package left_counters right_counters flag)
    (memory_recursive_candidate code (vector_pointer_region_nest package)) source.

Theorem memory_vector_axis_pointer_region_target_sound source (package : memory_vector_pointer_region_package source)
  live pairs candidate code left_counters right_counters flag :
  memory_vector_axis_pointer_guard_names_check package live left_counters right_counters flag = true ->
  compile_memory_vector_pointer_region_candidate package live pairs candidate = Some code ->
  memory_bounded_candidate_certificate (memory_vector_static_bounds (vector_pointer_region_limits package)
      (memory_vector_pointer_region_arity package)) (length (memory_nest_iterators (vector_pointer_region_nest package)))
    (memory_vector_pointer_region_arity package)
    (memory_vector_pointer_region_instructions package) (memory_vector_pointer_region_context package) candidate ->
  projected_region_contract live source
    (memory_vector_axis_pointer_region_target package left_counters right_counters flag code).
Proof.
  intros NAMES COMPILE CHECK.
  destruct (@memory_vector_axis_pointer_guard_names_sound source package live left_counters right_counters flag NAMES)
    as [LEFT [RIGHT [UNIQUE [FRESH FLAG]]]].
  unfold memory_vector_axis_pointer_region_target.
  eapply memory_projected_private_rule_stateful_sound with
    (rule := @memory_vector_pointer_projected_candidate_rule source package live pairs candidate code COMPILE CHECK).
  intros fe s DOMAIN; eapply memory_vector_axis_pointer_guard_execution; eassumption.
Qed.

Definition check_memory_vector_axis_pointer_region_candidate live pool source (package : memory_vector_pointer_region_package source)
  candidate (check : CoreAlarmed.Base.imp bool) : CoreAlarmed.Base.imp (option statement) :=
  if Nat.leb (length (memory_linear_pointer_accesses (vector_pointer_region_code package))) 32%nat then
  match private_counter_pairs pool with
  | Some pairs =>
      let dimensions := length (memory_nest_iterators (vector_pointer_region_nest package)) in
      let selected := firstn dimensions pairs in
      let left_counters := map fst selected in
      let right_counters := map snd selected in
      match nth_error pairs dimensions with
      | Some (flag,spare) =>
          if memory_vector_axis_pointer_guard_names_check package live left_counters right_counters flag then
            match compile_memory_vector_pointer_region_candidate package live pairs candidate with
            | Some code => BIND valid <- check -;
                pure (if valid then Some (memory_vector_axis_pointer_region_target package left_counters right_counters flag code) else None)
            | None => pure None end
          else pure None
      | None => pure None end
  | None => pure None end else pure None.

Theorem check_memory_vector_axis_pointer_region_candidate_sound live pool source (package : memory_vector_pointer_region_package source)
  candidate check target :
  (mayReturn check true -> memory_bounded_candidate_certificate (memory_vector_static_bounds (vector_pointer_region_limits package)
      (memory_vector_pointer_region_arity package))
    (length (memory_nest_iterators (vector_pointer_region_nest package))) (memory_vector_pointer_region_arity package) (memory_vector_pointer_region_instructions package)
    (memory_vector_pointer_region_context package) candidate) ->
  mayReturn (check_memory_vector_axis_pointer_region_candidate live pool package candidate check) (Some target) ->
  projected_region_contract live source target.
Proof.
  intros CERT; unfold check_memory_vector_axis_pointer_region_candidate.
  destruct (Nat.leb (length (memory_linear_pointer_accesses (vector_pointer_region_code package))) 32%nat);
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (nth_error pairs (length (memory_nest_iterators (vector_pointer_region_nest package)))) as [[flag spare]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (memory_vector_axis_pointer_guard_names_check package live
    (map fst (firstn (length (memory_nest_iterators (vector_pointer_region_nest package))) pairs))
    (map snd (firstn (length (memory_nest_iterators (vector_pointer_region_nest package))) pairs)) flag) eqn:NAMES;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_memory_vector_pointer_region_candidate package live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN;
    destruct valid; [inversion RUN; subst target|discriminate].
  eapply memory_vector_axis_pointer_region_target_sound; [exact NAMES|exact COMPILE|apply CERT; exact VALID].
Qed.
