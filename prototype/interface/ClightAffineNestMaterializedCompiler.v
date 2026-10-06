From Stdlib Require Import List Bool ZArith.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryTiledCompiler GuardMemoryBoundedSourceChecker GuardMemoryWindowBackend.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestPackageGuard
  AffineNestPackageDecode AffineNestPackageRanges AffineNestCandidateLocal
  AffineNestStaticPackage AffineNestMultiStaticPackage AffineNestMultiGuardExecution
  AffineNestMultiCandidateLocal AffineNestCandidateEvidence AffineNestCheckedCompiler
  AffineNestMultiCheckedCompiler.
From GuardInterface Require Import ClightMaterializedCheck ClightAffineNestMaterialized.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.

(** Source and candidate proposals remain untrusted. A new syntax check binds
    the actual materialized guard to the language host before installation. *)
Definition check_materialized_affine_single live pool
  (describe : affine_source_proposer) (propose : affine_candidate_proposer) source :=
  match describe live pool source with
  | Some (parameters,proposal) =>
    match check_affine_static_package source parameters live (var_names pool) proposal,private_counter_pairs pool with
    | Some package,Some pairs => match propose (affine_make_request package) with
      | Some (candidate,evidence) =>
        match compile_window_multi_pointer_buffer_loop (affine_proposed_pointers proposal)
          (affine_package_context parameters proposal) (affine_package_encoder_bounds proposal) live pairs candidate with
        | Some code => match describe_materialized_check (affine_package_guard_code (affine_static_guard package))
            (Etempvar (affine_proposed_result proposal) type_int32s) with
          | Some test =>
            BIND valid <- checked_affine_candidate (affine_package_validator_bounds proposal)
              (affine_static_source_loop package) (affine_package_context parameters proposal)
              (affine_proposed_pointers proposal) candidate evidence -;
            pure (if valid then Some (materialized_select test (affine_single_candidate_code proposal code) source) else None)
          | None => pure None end
        | None => pure None end
      | None => pure None end
    | _,_ => pure None end
  | None => pure None end.

Theorem check_materialized_affine_single_sound live pool describe propose source target :
  mayReturn (check_materialized_affine_single live pool describe propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_materialized_affine_single.
  destruct (describe live pool source) as [[parameters proposal]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (check_affine_static_package source parameters live (var_names pool) proposal) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (affine_make_request package)) as [[candidate evidence]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_window_multi_pointer_buffer_loop (affine_proposed_pointers proposal)
    (affine_package_context parameters proposal) (affine_package_encoder_bounds proposal) live pairs candidate)
    as [code|] eqn:COMPILE; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_materialized_check (affine_package_guard_code (affine_static_guard package))
    (Etempvar (affine_proposed_result proposal) type_int32s)) as [test|] eqn:DESCRIBE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN; destruct valid; [|discriminate].
  inversion RUN; subst target.
  eapply affine_single_materialized_region_sound with (package:=package) (pool:=pairs)
    (source_loop:=affine_static_source_loop package) (candidate:=candidate).
  - exact DESCRIBE.
  - eapply checked_affine_candidate_correct; exact VALID.
  - reflexivity.
  - exact COMPILE.
Qed.

Definition check_materialized_affine_multi live pool
  (describe : affine_source_proposer) (propose : affine_candidate_proposer) source :=
  match describe live pool source with
  | Some (parameters,proposal) =>
    match check_affine_multi_static_package source parameters live (var_names pool) proposal,private_counter_pairs pool with
    | Some package,Some pairs => match propose (affine_multi_make_request package) with
      | Some (candidate,evidence) =>
        match compile_window_multi_pointer_buffer_loop (affine_proposed_pointers proposal)
          (affine_package_context parameters proposal) (affine_package_encoder_bounds proposal) live pairs candidate with
        | Some code => match describe_materialized_check (affine_multi_guard_code package)
            (Etempvar (affine_proposed_result proposal) type_int32s) with
          | Some test =>
            BIND valid <- checked_affine_candidate (affine_package_validator_bounds proposal)
              (affine_multi_source_loop package) (affine_package_context parameters proposal)
              (affine_proposed_pointers proposal) candidate evidence -;
            pure (if valid then Some (materialized_select test (affine_multi_candidate_code proposal code) source) else None)
          | None => pure None end
        | None => pure None end
      | None => pure None end
    | _,_ => pure None end
  | None => pure None end.

Theorem check_materialized_affine_multi_sound live pool describe propose source target :
  mayReturn (check_materialized_affine_multi live pool describe propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_materialized_affine_multi.
  destruct (describe live pool source) as [[parameters proposal]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (check_affine_multi_static_package source parameters live (var_names pool) proposal) as [package|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (propose (affine_multi_make_request package)) as [[candidate evidence]|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_window_multi_pointer_buffer_loop (affine_proposed_pointers proposal)
    (affine_package_context parameters proposal) (affine_package_encoder_bounds proposal) live pairs candidate)
    as [code|] eqn:COMPILE; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_materialized_check (affine_multi_guard_code package)
    (Etempvar (affine_proposed_result proposal) type_int32s)) as [test|] eqn:DESCRIBE;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN valid VALID; apply mayReturn_pure in RUN; destruct valid; [|discriminate].
  inversion RUN; subst target.
  eapply affine_multi_materialized_region_sound with (package:=package) (pool:=pairs)
    (source_loop:=affine_multi_source_loop package) (candidate:=candidate).
  - exact DESCRIBE.
  - eapply checked_affine_candidate_correct; exact VALID.
  - reflexivity.
  - exact COMPILE.
Qed.

Definition check_materialized_affine_region live pool describe propose source :=
  BIND single <- check_materialized_affine_single live pool describe propose source -;
  match single with
  | Some target => pure (Some target)
  | None => check_materialized_affine_multi live pool describe propose source end.

Theorem check_materialized_affine_region_sound live pool describe propose source target :
  mayReturn (check_materialized_affine_region live pool describe propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_materialized_affine_region; intro RUN; bind_imp_destruct RUN single SINGLE.
  destruct single as [code|].
  - apply mayReturn_pure in RUN; inversion RUN; subst code.
    eapply check_materialized_affine_single_sound; exact SINGLE.
  - eapply check_materialized_affine_multi_sound; exact RUN.
Qed.

Print Assumptions check_materialized_affine_single_sound.
Print Assumptions check_materialized_affine_multi_sound.
Print Assumptions check_materialized_affine_region_sound.
