From Stdlib Require Import List Bool PArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryTiledCompiler GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestPackageDecode
  AffineNestPackageRanges AffineNestStaticPackage AffineNestMultiStaticPackage AffineNestMultiCandidateLocal
  AffineNestCandidateEvidence AffineNestCheckedCompiler AffineNestMultiCheckedCompiler.
From GuardInterface Require Import ClightMaterializedCheck ClightNestedConstantSite ClightNestedConstantMultiSite
  ClightNestedConstantMultiPreservation ClightNestedFrontendRegion ClightNestedFrontendFactory
  ClightNestedInvariantCertificate ClightNestedInvariantPreservation ClightNestedCompactCandidate.
From Guard Require Import ClightSyntaxEquality.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.

(** Untrusted compile-time source/candidate proposals. The checked factory
    consumes data, not source/model or guarded-correctness proof callbacks. *)
Definition check_ncs_invariant_frontend_region live pool(describe:ncs_frontend_proposer)(propose:affine_candidate_proposer) source :=
  match describe live pool source with
  | Some(indexed,parameters,proposal,shape) =>
    if statement_eq source(ncs_frontend_source indexed shape) then
    if affine_names_allocated_check(ncs_caches shape++ncs_helpers shape)(var_names pool) then
    match check_ncs_invariant_stability_site(ncs_original shape)parameters live(var_names pool)proposal shape,private_counter_pairs pool with
    | Some site,Some pairs => match propose(affine_multi_make_request(ncs_multi_package(ncs_invariant_stability_core site))) with
      | Some(candidate,evidence) =>
        match compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
          (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
          (ncs_ports(ncs_original shape)parameters live shape)(ncs_candidate_pairs(ncs_ports(ncs_original shape)parameters live shape)pairs)candidate with
        | Some code =>
          BIND valid <- checked_affine_candidate(affine_package_validator_bounds proposal)
            (affine_multi_source_loop(ncs_multi_package(ncs_invariant_stability_core site)))(affine_package_context parameters proposal)
            (affine_proposed_pointers proposal)candidate evidence -;
          pure(if valid then Some(materialized_select(ncs_invariant_stability_test site)
            (ncs_compact_candidate_code shape code)source) else None)
        | None => pure None end
      | None => pure None end
    | _,_ => pure None end
    else pure None
    else pure None
  | None => pure None end.

Theorem check_ncs_invariant_frontend_region_sound live pool describe propose source target :
  mayReturn(check_ncs_invariant_frontend_region live pool describe propose source)(Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_ncs_invariant_frontend_region.
  destruct(describe live pool source) as [[[[indexed parameters] proposal] shape]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(statement_eq source(ncs_frontend_source indexed shape)) as [EXACT|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  subst source.
  destruct(affine_names_allocated_check(ncs_caches shape++ncs_helpers shape)(var_names pool));
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(check_ncs_invariant_stability_site(ncs_original shape)parameters live(var_names pool)proposal shape) as [site|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(propose(affine_multi_make_request(ncs_multi_package(ncs_invariant_stability_core site)))) as [[candidate evidence]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
    (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal)
    (ncs_ports(ncs_original shape)parameters live shape)(ncs_candidate_pairs(ncs_ports(ncs_original shape)parameters live shape)pairs)candidate)
    as [code|] eqn:COMPILE; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN; destruct valid; [|discriminate].
  inversion RUN; subst target.
  eapply ncs_invariant_frontend_region_contract with(candidate:=candidate)(pool:=ncs_candidate_pairs(ncs_ports(ncs_original shape)parameters live shape)pairs).
  - eapply checked_affine_candidate_correct; exact VALID.
  - exact COMPILE.
Qed.

Print Assumptions check_ncs_invariant_frontend_region_sound.
