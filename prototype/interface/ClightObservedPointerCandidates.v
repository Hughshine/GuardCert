From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryAffineReindex
  GuardMemoryRecursiveSource GuardMemoryRecursiveCandidate GuardMemoryRecursiveChecker
  GuardMemoryScalarChecker GuardMemoryScalarLoops GuardMemoryScalarCandidates GuardMemoryScalarTiling
  GuardMemoryScheduleProducer GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerCompiler
  GuardMemoryRecursiveSyntax GuardMemoryTiledCompiler.
From GuardMemory Require Import GuardMemoryAxisPointerCompiler GuardMemoryArrayBackend.
From GuardMemory Require Import GuardMemoryArrayBackend.
From GuardMemory Require Import GuardMemoryVectorChecker GuardMemoryVectorTiling.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryParamPointerBounds GuardMemoryParamAxisCompiler.
From GuardInterface Require Import ClightParamPointerPreservation.
From GuardMemory Require Import GuardMemoryParamAxisDescribe.
From GuardInterface Require Import ClightParamPointerCandidates ClightObservedPointerCandidate ClightObservedPointerSyntax ClightSourceObservation ClightSequenceContracts.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition check_observed_param_pointer_mapped_package live pool source (package : memory_param_pointer_region_package source) loads
  raw_candidate steps :=
  let dimensions := length (memory_nest_iterators (param_pointer_region_nest package)) in
  let candidate := memory_carry_scalar_arguments 0 dimensions (memory_param_pointer_region_arity package) raw_candidate in
  check_observed_param_pointer_candidate live pool package loads candidate
    (checked_memory_bounded_candidate (memory_param_static_bounds (param_pointer_region_limits package)
      (param_pointer_region_parameter_limits package) (length (param_pointer_region_scalars package))) dimensions
      (memory_param_pointer_region_arity package) (memory_param_pointer_region_instructions package)
      (memory_param_pointer_region_context package) (memory_param_pointer_region_arrays package) candidate steps).
Theorem check_observed_param_pointer_mapped_package_sound live pool source (package : memory_param_pointer_region_package source) loads
  candidate steps target :
  mayReturn (check_observed_param_pointer_mapped_package live pool package loads candidate steps) (Some target) ->
  projected_region_contract live (Ssequence (source_load_prefix loads) source) target.
Proof.
  unfold check_observed_param_pointer_mapped_package; apply check_observed_param_pointer_candidate_sound;
    apply checked_memory_bounded_candidate_correct.
Qed.

Definition check_observed_param_pointer_scheduled_package live pool source (package : memory_param_pointer_region_package source) loads
  schedules steps :=
  let dimensions := length (memory_nest_iterators (param_pointer_region_nest package)) in
  let context := memory_param_pointer_region_context package in
  let vars := map (fun identifier => (identifier,tt)) (context++memory_param_pointer_region_arrays package) in
  BIND candidate <- memory_generate_scheduled_loop
    (memory_bounded_assumed_loop (map (fun cap => MemoryNested.A.Interval 1 cap) (param_pointer_region_limits package))
      (memory_scalar_rectangle 0 dimensions (memory_param_pointer_region_arity package)
        (memory_param_pointer_region_instructions package)),context,vars) schedules -;
  match candidate with
  | Some candidate => check_observed_param_pointer_mapped_package live pool package loads candidate steps
  | None => pure None end.
Theorem check_observed_param_pointer_scheduled_package_sound live pool source (package : memory_param_pointer_region_package source) loads
  schedules steps target :
  mayReturn (check_observed_param_pointer_scheduled_package live pool package loads schedules steps) (Some target) ->
  projected_region_contract live (Ssequence (source_load_prefix loads) source) target.
Proof.
  unfold check_observed_param_pointer_scheduled_package; intro RUN;
    bind_imp_destruct RUN candidate GENERATED; destruct candidate as [candidate|];
    [eapply check_observed_param_pointer_mapped_package_sound; exact RUN|apply mayReturn_pure in RUN; discriminate].
Qed.

Definition check_observed_param_pointer_tiled_package live pool source (package : memory_param_pointer_region_package source) loads bi bj :=
  let dimensions := length (memory_nest_iterators (param_pointer_region_nest package)) in
  if (2 <=? dimensions)%nat && (0 <? bi) && (0 <? bj) then
    check_observed_param_pointer_candidate live pool package loads
      (memory_scalar_tiled_loop dimensions (memory_param_pointer_region_arity package)
        (memory_param_pointer_region_instructions package) bi bj true)
      (checked_memory_bounded_tiling (memory_param_static_bounds (param_pointer_region_limits package)
        (param_pointer_region_parameter_limits package) (length (param_pointer_region_scalars package))) dimensions (memory_param_pointer_region_arity package)
        (memory_param_pointer_region_instructions package) (memory_param_pointer_region_context package)
        (memory_param_pointer_region_arrays package) bi bj)
  else pure None.
Theorem check_observed_param_pointer_tiled_package_sound live pool source (package : memory_param_pointer_region_package source) loads bi bj target :
  mayReturn (check_observed_param_pointer_tiled_package live pool package loads bi bj) (Some target) ->
  projected_region_contract live (Ssequence (source_load_prefix loads) source) target.
Proof.
  unfold check_observed_param_pointer_tiled_package.
  destruct ((2 <=? length (memory_nest_iterators (param_pointer_region_nest package)))%nat && (0 <? bi) && (0 <? bj)) eqn:SIZE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  rewrite !andb_true_iff,Nat.leb_le,Z.ltb_lt,Z.ltb_lt in SIZE; destruct SIZE as [[DIMENSIONS BI] BJ].
  apply check_observed_param_pointer_candidate_sound.
  pose proof (param_pointer_region_limits_length (param_pointer_region_syntax package)) as LENGTH.
  destruct (param_pointer_region_limits package) as [|first [|second rest]] eqn:LIMITS; cbn in LENGTH; try lia.
  eapply checked_memory_bounded_tiling_correct with (first_cap := first) (second_cap := second).
  - unfold memory_param_static_bounds; reflexivity.
  - unfold memory_param_static_bounds; reflexivity.
  - unfold memory_param_pointer_region_context,memory_param_pointer_runtime_context,memory_param_pointer_region_arity;
      rewrite !length_app; f_equal; symmetry; apply memory_nest_lengths.
  - exact DIMENSIONS.
  - exact BI.
  - exact BJ.
Qed.
Print Assumptions check_observed_param_pointer_tiled_package_sound.

Print Assumptions check_observed_param_pointer_mapped_package_sound.
Print Assumptions check_observed_param_pointer_scheduled_package_sound.

Definition check_observed_pointer_package live pool (propose : pointer_preserving_proposer) source
  (package : memory_param_pointer_region_package source) loads :=
  match propose (pointer_preserving_request_of package) with
  | Some (PointerMappedProposal candidate steps) =>
      check_observed_param_pointer_mapped_package live pool package loads candidate steps
  | Some (PointerTilingProposal rows columns) =>
      check_observed_param_pointer_tiled_package live pool package loads rows columns
  | Some (PointerScheduleProposal schedules steps) =>
      check_observed_param_pointer_scheduled_package live pool package loads schedules steps
  | None => pure None end.
Lemma check_observed_pointer_package_sound live pool propose source
  (package : memory_param_pointer_region_package source) loads target :
  mayReturn (check_observed_pointer_package live pool propose package loads) (Some target) ->
  projected_region_contract live (Ssequence (source_load_prefix loads) source) target.
Proof.
  unfold check_observed_pointer_package; destruct (propose (pointer_preserving_request_of package)) as [proposal|].
  - destruct proposal; [apply check_observed_param_pointer_mapped_package_sound|
      apply check_observed_param_pointer_tiled_package_sound|apply check_observed_param_pointer_scheduled_package_sound].
  - intro RUN; apply mayReturn_pure in RUN; discriminate.
Qed.

(** Reuse the existing checked profile search with a more general result
    predicate. This does not trust a proposed source profile. *)
Lemma check_param_axis_profiles_postcondition source
  (check : memory_param_pointer_region_package source -> CoreAlarmed.Base.imp (option statement))
  (property : statement -> Prop) :
  (forall package target, mayReturn (check package) (Some target) -> property target) ->
  forall profiles target, mayReturn (check_memory_param_axis_profiles check profiles) (Some target) -> property target.
Proof.
  intros CHECK profiles; induction profiles as [|profile profiles IH]; intros target RUN;
    cbn [check_memory_param_axis_profiles] in RUN.
  - apply mayReturn_pure in RUN; discriminate.
  - destruct (describe_memory_param_axis_at source profile) as [package|].
    + bind_imp_destruct RUN candidate ACCEPTED; destruct candidate as [candidate|].
      * apply mayReturn_pure in RUN; inversion RUN; subst target; apply CHECK with (package:=package); exact ACCEPTED.
      * apply IH; exact RUN.
    + apply IH; exact RUN.
Qed.

Definition check_observed_pointer_source live pool (propose : pointer_preserving_proposer) source :=
  match describe_observed_pointer_source source with
  | Some observed =>
    BIND candidate <- @check_memory_param_axis_profiles (observed_source_loop observed)
      (fun package => check_observed_pointer_package live pool propose package (observed_source_loads observed))
      (propose_memory_param_axis_profiles (observed_source_loop observed)) -;
    pure (match candidate with
      | Some target => Some (Ssequence target (observed_source_suffix observed))
      | None => None end)
  | None => pure None end.
Theorem check_observed_pointer_source_sound live pool propose source target :
  mayReturn (check_observed_pointer_source live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_observed_pointer_source; destruct (describe_observed_pointer_source source) as [observed|].
  - intro RUN; bind_imp_destruct RUN candidate ACCEPTED; apply mayReturn_pure in RUN;
      destruct candidate as [candidate|]; [injection RUN as <-|discriminate].
    eapply flattened_projected_region_contract; [exact (observed_source_flat observed)|].
    apply projected_region_quiet_suffix; [exact (observed_source_suffix_quiet observed)|].
    eapply check_param_axis_profiles_postcondition; [|exact ACCEPTED].
    intros package chosen CHECK; eapply check_observed_pointer_package_sound; exact CHECK.
  - intro RUN; apply mayReturn_pure in RUN; discriminate.
Qed.

(** Existing sources without a checked observation prefix retain the original
    private-scan path. Both kinds of replacement use the same program host. *)
Definition check_observed_or_scanned_pointer_source live pool propose source :=
  BIND candidate <- check_observed_pointer_source live pool propose source -;
  match candidate with
  | Some target => pure (Some target)
  | None => check_private_scan_param_pointer_source live pool propose source end.
Theorem check_observed_or_scanned_pointer_source_sound live pool propose source target :
  mayReturn (check_observed_or_scanned_pointer_source live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_observed_or_scanned_pointer_source; intro RUN; bind_imp_destruct RUN candidate ACCEPTED.
  destruct candidate as [candidate|].
  - apply mayReturn_pure in RUN; injection RUN as <-; eapply check_observed_pointer_source_sound; exact ACCEPTED.
  - eapply check_private_scan_param_pointer_source_sound; exact RUN.
Qed.

Print Assumptions check_observed_pointer_source_sound.
Print Assumptions check_observed_or_scanned_pointer_source_sound.
