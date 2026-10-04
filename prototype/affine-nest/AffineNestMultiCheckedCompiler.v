From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryAffineReindex GuardMemoryTiledCompiler GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode AffineNestGuardPackage AffineNestPackageDecode
  AffineNestPackageRanges AffineNestStaticPackage AffineNestRegion.
From GuardAffineNest Require Import AffineNestCandidateEvidence.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.

From GuardAffineNest Require Import AffineNestCheckedCompiler AffineNestMultiStaticPackage AffineNestMultiRegion.
Definition affine_multi_make_request source parameters live allocated proposal
  (package:affine_multi_static_package source parameters live allocated proposal) :=
  AffineCandidateRequest(affine_multi_source_loop package)(affine_package_context parameters proposal)
    (affine_package_validator_bounds proposal)(affine_proposed_pointers proposal)
    ((affine_proposed_floor proposal,affine_proposed_cap proposal)::affine_proposed_remaining proposal).

Definition check_affine_multi_region live pool (describe:affine_source_proposer)(propose:affine_candidate_proposer) source :=
  match describe live pool source with
  | Some(parameters,proposal) => match check_affine_multi_static_package source parameters live(var_names pool) proposal,private_counter_pairs pool with
    | Some package,Some pairs => match propose(affine_multi_make_request package) with
      | Some(candidate,evidence) => match compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)
          (affine_package_context parameters proposal)(affine_package_encoder_bounds proposal) live pairs candidate with
        | Some code => BIND valid <- checked_affine_candidate(affine_package_validator_bounds proposal)
            (affine_multi_source_loop package)(affine_package_context parameters proposal)(affine_proposed_pointers proposal) candidate evidence -;
          pure(if valid then Some(affine_multi_guarded_region package code) else None)
        | None => pure None end
      | None => pure None end
    | _,_ => pure None end
  | None => pure None end.

Theorem check_affine_multi_region_sound live pool describe propose source target :
  mayReturn(check_affine_multi_region live pool describe propose source)(Some target) -> projected_region_contract live source target.
Proof.
  unfold check_affine_multi_region.
  destruct(describe live pool source) as [[parameters proposal]|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(check_affine_multi_static_package source parameters live(var_names pool) proposal) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(propose(affine_multi_make_request package)) as [[candidate evidence]|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(compile_window_multi_pointer_buffer_loop(affine_proposed_pointers proposal)(affine_package_context parameters proposal)
    (affine_package_encoder_bounds proposal) live pairs candidate) as [code|] eqn:COMPILE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN; destruct valid; [|discriminate].
  inversion RUN; subst target.
  eapply affine_multi_guarded_region_sound with(source_loop:=affine_multi_source_loop package)
    (candidate:=candidate)(pool:=pairs).
  - exact(affine_multi_pointer_private package).
  - exact(affine_multi_pointer_public package).
  - exact(affine_multi_window_low package).
  - exact(affine_multi_window_high package).
  - exact(affine_multi_window_span package).
  - exact(affine_multi_source_lower package).
  - exact(affine_multi_shadow_scope package).
  - eapply checked_affine_candidate_correct; exact VALID.
  - exact COMPILE.
Qed.
Print Assumptions check_affine_multi_region_sound.
