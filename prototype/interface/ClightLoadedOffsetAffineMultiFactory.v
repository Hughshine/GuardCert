From Stdlib Require Import List Bool PArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryTiledCompiler GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageDecode
  AffineNestPackageRanges AffineNestStaticPackage AffineNestMultiStaticPackage AffineNestMultiCandidateLocal
  AffineNestCandidateEvidence AffineNestCheckedCompiler AffineNestMultiCheckedCompiler.
From GuardInterface Require Import ClightMaterializedCheck ClightLoadedAffineScanSite
  ClightLoadedAffineMultiGuard ClightLoadedAffineMultiPreservation ClightLoadedAffineMultiFactory
  ClightLoadedOffsetAffineMultiGuard ClightLoadedOffsetAffineMultiPreservation.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.

(** A user proposes the original source description and retained header
    pointer and machine offset. Both are checked against the actual AST, never trusted. *)
Definition offset_affine_source_proposer := list ident -> list(ident*type) -> statement ->
  option(list ident*affine_guard_proposal*ident*int).

(** Captured inputs are protected by candidate lowering. Their declarations
    stay in the checked integer pool, but their pair is not a counter resource. *)

Definition check_offset_affine_multi_region live pool
  (describe : offset_affine_source_proposer)(propose : affine_candidate_proposer) source :=
  match describe live pool source with
  | Some(parameters,proposal,pointer,delta) =>
    if affine_names_allocated_check [affine_proposed_bound proposal](var_names pool) then
    match check_offset_affine_multi_site source parameters live(var_names pool)proposal pointer delta,
      private_counter_pairs pool with
    | Some site,Some pairs => match propose(affine_multi_make_request(offset_multi_package site)) with
      | Some(candidate,evidence) =>
        match compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
          (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
          (loaded_affine_scan_ports parameters proposal live)
          (loaded_affine_candidate_pairs(affine_proposed_bound proposal)pairs) candidate with
        | Some code =>
          BIND valid <- checked_affine_candidate(affine_package_validator_bounds proposal)
            (affine_multi_source_loop(offset_multi_package site))(affine_package_context parameters proposal)
            (affine_proposed_pointers proposal) candidate evidence -;
          pure(if valid then Some(materialized_select(offset_multi_test site)
            (affine_multi_candidate_code proposal code)source) else None)
        | None => pure None end
      | None => pure None end
    | _,_ => pure None end
    else pure None
  | None => pure None end.

Theorem check_offset_affine_multi_region_sound live pool describe propose source target :
  mayReturn(check_offset_affine_multi_region live pool describe propose source)(Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_offset_affine_multi_region.
  destruct(describe live pool source) as [[[[parameters proposal] pointer] delta]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(affine_names_allocated_check [affine_proposed_bound proposal](var_names pool));
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(check_offset_affine_multi_site source parameters live(var_names pool) proposal pointer delta) as [site|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(propose(affine_multi_make_request(offset_multi_package site))) as [[candidate evidence]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
    (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
    (loaded_affine_scan_ports parameters proposal live)
    (loaded_affine_candidate_pairs(affine_proposed_bound proposal)pairs) candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN; destruct valid; [|discriminate].
  inversion RUN; subst target.
  eapply offset_affine_multi_region_contract with(candidate:=candidate)
    (pool:=loaded_affine_candidate_pairs(affine_proposed_bound proposal)pairs).
  - eapply checked_affine_candidate_correct; exact VALID.
  - exact COMPILE.
Qed.

Print Assumptions check_offset_affine_multi_region_sound.
