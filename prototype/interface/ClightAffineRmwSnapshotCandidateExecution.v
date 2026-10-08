From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightGuard.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricWidth.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightAffineSnapshotSyntax
  ClightAffineSnapshotSourceInputs ClightAffineZeroSnapshotCandidateCondition ClightAffineRmwSnapshotCondition
  ClightAffineSnapshotRowObservation ClightAffineRowObservationTransport ClightAffineZeroPointerCandidate
  ClightAffineInnerPointerSourceGuard ClightAffinePointerGuard ClightAffineDomainFacts
  ClightFirstReachedWidth ClightAffineZeroSnapshotPreparation.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section EXECUTION.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Variable rmw : affine_snapshot_rmw_site site.
Let package:=snapshot_cached_package site.
Variable live : list ident.
Variable candidate : affine_zero_pointer_candidate_package package live.
Variables first later alias : decision_tree.
Hypothesis FIRST : compile_first_reached_width 0(affine_inner_pointer_column_limit package)0
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some first.
Hypothesis LATER : compile_first_reached_width 0(affine_inner_pointer_column_limit package)1
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_zero_snapshot_header_bounds site)(affine_inner_pointer_expression package)=Some later.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package=Some alias.

Definition affine_rmw_snapshot_guarded_candidate:=tree_statement
  (affine_rmw_snapshot_candidate_tree rmw first later alias
    (affine_zero_candidate_validator_bounds candidate)(affine_zero_candidate_encoder_bounds candidate))
  (affine_zero_pointer_candidate_statement candidate)original.

Theorem affine_rmw_snapshot_guarded_candidate_execution fe ge locals temps memory after final :
  affine_zero_snapshot_candidate_domain site fe(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exists target,exec_stmt fe ge locals temps memory affine_rmw_snapshot_guarded_candidate E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros DOMAIN SOURCE.
  pose proof(@affine_rmw_snapshot_candidate_condition original site rmw fe fragment_observation(@eq fragment_observation)
    first later alias(affine_zero_candidate_validator_bounds candidate)(affine_zero_candidate_encoder_bounds candidate)
    FIRST LATER ALIAS)as CONDITION.
  destruct(readonly_available CONDITION _ DOMAIN)as [accepted [checked [RUN SAME]]]; subst checked.
  unfold affine_rmw_snapshot_guarded_candidate; destruct accepted.
  - destruct(readonly_sound CONDITION _ _ _ DOMAIN(conj RUN eq_refl))as [_ SOUND].
    destruct(SOUND eq_refl)as [READY [ROWS [NONALIAS RANGES]]].
    assert(CACHED:exec_stmt fe ge locals temps memory(snapshot_cached_source site)E0 after final Out_normal).
    { apply affine_row_snapshot_checked_cached_execution;
        [exact(proj1 DOMAIN)|exact READY|exact ROWS|exact SOURCE]. }
    destruct(@affine_zero_pointer_candidate_execution(snapshot_cached_source site)package live candidate
      fe ge locals temps memory after final READY NONALIAS RANGES CACHED)as [target [EXECUTE PUBLIC]].
    exists target; split; [eapply decision_fragment_run with(b:=true); [exact RUN|exact EXECUTE]|exact PUBLIC].
  - exists after; split; [eapply decision_fragment_run with(b:=false); [exact RUN|exact SOURCE]|apply temp_agree_refl].
Qed.
End EXECUTION.

Print Assumptions affine_rmw_snapshot_guarded_candidate_execution.
