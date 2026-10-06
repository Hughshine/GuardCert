From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCondition ClightPureExpr ClightPrivateRule
  ClightPrivateRegion ClightTempFrame ClightTempFootprint ClightRectangularStore
  ClightRectangularSelector ClightFrontendLoopProtocol ClightStraightLine ClightRegionProgress.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryTiledClight GuardMemoryNamedRegistrySource GuardMemoryNamedOperations
  GuardMemoryNamedGuard GuardMemoryNamedCandidate GuardMemoryNamedChecker GuardMemoryNamedCompiler
  GuardMemoryAffineReindex GuardMemoryNamedMappedChecker GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightGuardRealization ClightReadonlyPreservation
  ClightReadonlyRuleEmbedding ClightSharedGuard.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition named_preserving_branch source (package : memory_named_package source) code :=
  let d := named_description package in
  rectangle_tiled_candidate code (rectangle_row d) (rectangle_bound d)
    (rectangle_column d) (rectangle_inner_bound d).
Definition named_preserving_tree source (package : memory_named_package source) :=
  let d := named_description package in
  decision_bind (memory_named_guard_tree (described_shape d)
    (named_array_descriptors (described_shape d) (named_operations package))
    (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d)) (Decision true) (Decision false).
Definition named_preserving_target source (package : memory_named_package source) code (shared : bool) result :=
  if shared then shared_guard_statement (named_preserving_tree package) result (named_preserving_branch package code) source
  else tree_statement (named_preserving_tree package) (named_preserving_branch package code) source.

Theorem named_preserving_target_sound source (package : memory_named_package source) live pairs candidate code shared result :
  compile_named_array_candidate (described_shape (named_description package)) (named_operations package)
    (rectangle_bound (named_description package)) (rectangle_inner_bound (named_description package))
    live pairs candidate = Some code ->
  memory_named_candidate_certificate (described_shape (named_description package)) (named_operations package) candidate ->
  (shared = true -> quiet_statement (named_preserving_branch package code) = true /\
    ~ In result (statement_temps (named_preserving_branch package code) ++ statement_temps source ++ live)) ->
  PrivateRegion.projected_region_contract live source (named_preserving_target package code shared result).
Proof.
  destruct package as [d operations CERT]; cbn; intros COMPILE CHECK SHARED.
  destruct CERT as [SOURCE BODY OUTER RN RC NC RM CM VALID LAYOUTS NONEMPTY]; subst source.
  set (old := @memory_named_array_candidate_rule (described_shape d) VALID operations LAYOUTS
    (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
    (rectangle_inner_body d) (rectangle_described_outer_body d) RN RC NC RM CM BODY OUTER
    live pairs candidate code COMPILE CHECK).
  set (rule := encoded_private_as_preserving old).
  destruct shared.
  - destruct (SHARED eq_refl) as [QUIET FRESH].
    exact (@preserving_realized_region_contract live
      (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d)) rule
      (@shared_normal_realization live (preserving_guard rule) (preserving_candidate rule)
        (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d)) result
        (statement_temps (preserving_candidate rule)) (preserving_writes rule)
        (@quiet_source_write_bound (preserving_candidate rule) QUIET) (preserving_source_writes rule) FRESH)).
  - exact (@preserving_realized_region_contract live
      (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d)) rule
      (direct_normal_realization live (preserving_guard rule) (preserving_candidate rule)
        (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d)))).
Qed.

(** Source/candidate selection remains an optimizer operation. These two
    proposal forms consume the actual mapped-domain or tiling validator. *)
Inductive preserving_polyhedral_candidate :=
| PreservingMappedCandidate (candidate : L.stmt) (steps : list memory_affine_reindex)
| PreservingTilingCandidate (rows columns : Z).
Definition preserving_polyhedral_proposer := list memory_instruction -> option preserving_polyhedral_candidate.

Definition checked_named_preserving_candidate source (package : memory_named_package source) proposal :
  CoreAlarmed.Base.imp (option L.stmt) :=
  let d := named_description package in
  match proposal with
  | PreservingMappedCandidate candidate steps =>
    BIND valid <- checked_named_mapped_candidate (described_shape d) (named_operations package)
      (rectangle_bound d) (rectangle_inner_bound d) candidate steps -;
    pure (if valid then Some candidate else None)
  | PreservingTilingCandidate rows columns =>
    match Z_lt_dec 0 rows, Z_lt_dec 0 columns with
    | left _, left _ =>
      BIND valid <- checked_named_tiled_candidate (described_shape d) (named_operations package) rows columns -;
      pure (if valid then Some (memory_tiled_sequence (map named_operation_instruction (named_operations package)) rows columns)
        else None)
    | _, _ => pure None end
  end.

Theorem checked_named_preserving_candidate_sound source (package : memory_named_package source) proposal candidate :
  mayReturn (checked_named_preserving_candidate package proposal) (Some candidate) ->
  memory_named_candidate_certificate (described_shape (named_description package)) (named_operations package) candidate.
Proof.
  destruct proposal as [loop steps|rows columns]; cbn [checked_named_preserving_candidate].
  - intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
    destruct valid; [inversion RUN; subst candidate|discriminate].
    eapply checked_named_mapped_candidate_correct; exact VALID.
  - destruct (Z_lt_dec 0 rows) as [ROWS|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
    destruct (Z_lt_dec 0 columns) as [COLUMNS|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
    intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN.
    destruct valid; [inversion RUN; subst candidate|discriminate].
    apply checked_named_tiled_candidate_correct; assumption.
Qed.

Print Assumptions named_preserving_target_sound.
Print Assumptions checked_named_preserving_candidate_sound.
