From Stdlib Require Import List.
From compcert.common Require Import AST Events.
From compcert.cfrontend Require Import Clight ClightBigstep Ctypes.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCondition ClightPrivateRegion ClightTempFootprint.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightAffineSnapshotSyntax ClightAffineSnapshotCaptureCandidate
  ClightAffineZeroSnapshotPreparation ClightAffineEmptyWidth ClightAffineEmptySignedCondition
  ClightAffineEmptyConditionCapture ClightAffineEmptyRuntimePrelude ClightCheckPlanFrame
  ClightAffineEmptySignedBuilder ClightAffineEmptySnapshotPlannedBuilder
  ClightObservedPointerSyntax ClightSourceObservation ClightSequenceContracts
  ClightCertifiedRegionBuilder ClightLoopAdministrative ClightWordNestedStoreFrontend.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Reuse the exact administrative equivalence in the reverse direction too.
    This does not strengthen the original source/candidate model certificates. *)
Lemma affine_empty_runtime_normalized_previous live source previous :
  PrivateRegion.projected_region_contract live source previous ->
  PrivateRegion.projected_region_contract live (trim_loop_skips source) previous.
Proof.
  intros CONTRACT temps p locals entry current memory after final SCOPE AGREE SOURCE fn continuation.
  apply CONTRACT with (le:=entry) (le':=after) (m':=final).
  - intros id MEMBER; apply SCOPE; rewrite trim_loop_skips_temps; exact MEMBER.
  - exact AGREE.
  - apply (proj1 (trim_loop_skips_equivalent (adapter_entry temps) source
      (globalenv p) locals entry memory E0 after final Out_normal)); exact SOURCE.
Qed.

Definition check_affine_empty_runtime_source live pool profile source previous :=
  match pool with
  | (root_cache,root_type)::(child_cache,child_type)::(result,result_type)::_=>
    if type_eq root_type type_int32s then if type_eq child_type type_int32s then if type_eq result_type type_int32s then
      match describe_observed_pointer_source source with
      | Some observed=>if source_observations_check [] (observed_source_loads observed) then
        match describe_affine_snapshot_source profile root_cache child_cache (observed_source_loop observed) with
        | Some site=>match check_affine_snapshot_capture site live with
          | Some capture=>let package:=snapshot_cached_package site in
            match compile_affine_empty_width (affine_inner_pointer_row (affine_inner_pointer_shape package))
              (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
              (affine_empty_signed_header_bounds site) (affine_inner_pointer_expression package) with
            | Some width=>if check_plan_resources (affine_empty_client_plan site (affine_empty_signed_tree site width))
                result live (affine_empty_client_yes site) (observed_source_loop observed) then
                pure (Some (affine_empty_runtime_target site (observed_source_loads observed)
                  (affine_empty_signed_tree site width) result (observed_source_suffix observed) previous))
              else pure None
            | None=>pure None end
          | None=>pure None end
        | None=>pure None end
        else pure None
      | None=>pure None end
    else pure None else pure None else pure None
  | _=>pure None end.

Theorem check_affine_empty_runtime_source_sound live pool profile source previous target :
  PrivateRegion.projected_region_contract live source previous ->
  mayReturn (check_affine_empty_runtime_source live pool profile source previous) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  intro PREVIOUS; unfold check_affine_empty_runtime_source.
  destruct pool as [|[root_cache root_type][|[child_cache child_type][|[result result_type]rest]]];
    try solve [intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (type_eq root_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (type_eq child_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (type_eq result_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_observed_pointer_source source) as [observed|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (source_observations_check _ _) eqn:PREFIX; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (describe_affine_snapshot_source _ _ _ _) as [site|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (check_affine_snapshot_capture site live) as [capture|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (compile_affine_empty_width _ _ _ _) as [width|] eqn:WIDTH; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (check_plan_resources _ _ _ _ _) eqn:RESOURCES; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; apply mayReturn_pure in RUN; injection RUN as <-.
  eapply flattened_projected_region_contract; [exact (observed_source_flat observed)|].
  eapply (@affine_empty_runtime_contract (observed_source_loop observed) site live capture
    (affine_empty_signed_tree site width)
    (fun fe=>@affine_empty_signed_condition (observed_source_loop observed) site width WIDTH fe
      fragment_observation (@eq fragment_observation)) result RESOURCES (observed_source_loads observed)
    (proj2 (source_observations_check_sound _ _ PREFIX)) (observed_source_suffix observed)
    (observed_source_suffix_quiet observed) previous).
  eapply flattened_projected_region_contract; [symmetry; exact (observed_source_flat observed)|exact PREVIOUS].
Qed.

Definition build_affine_empty_runtime_frontend profile public pool source previous :=
  check_affine_empty_runtime_source public pool profile (trim_loop_skips source) previous.
Theorem build_affine_empty_runtime_frontend_sound profile public pool source previous target :
  PrivateRegion.projected_region_contract public source previous ->
  mayReturn (build_affine_empty_runtime_frontend profile public pool source previous) (Some target) ->
  PrivateRegion.projected_region_contract public source target.
Proof.
  intros PREVIOUS RUN; apply word_nested_store_frontend_contract.
  eapply check_affine_empty_runtime_source_sound;
    [apply affine_empty_runtime_normalized_previous; exact PREVIOUS|exact RUN].
Qed.

(** Runtime refusal enters the previous certified target. Static refusal of
    this wrapper retains that target exactly; a site with no previous target
    uses the already installed standalone empty rewrite. *)
Definition build_affine_empty_runtime_extension existing profile public pool source :=
  BIND previous <- build_certified_region existing public pool source -;
  match previous with
  | Some previous=>
    BIND combined <- build_affine_empty_runtime_frontend profile public pool source previous -;
    pure (Some (match combined with Some target=>target | None=>previous end))
  | None=>build_certified_region
    (certified_region_or_else (certified_affine_empty_signed_builder profile)
      (certified_affine_empty_snapshot_planned_builder profile)) public pool source
  end.
Theorem build_affine_empty_runtime_extension_sound existing profile public pool source target :
  mayReturn (build_affine_empty_runtime_extension existing profile public pool source) (Some target) ->
  PrivateRegion.projected_region_contract public source target.
Proof.
  unfold build_affine_empty_runtime_extension; intro RUN; bind_imp_destruct RUN previous PREVIOUS.
  destruct previous as [previous|].
  - bind_imp_destruct RUN combined COMBINED; apply mayReturn_pure in RUN.
    destruct combined as [combined|]; injection RUN as <-.
    + eapply build_affine_empty_runtime_frontend_sound;
        [eapply build_certified_region_sound; exact PREVIOUS|exact COMBINED].
    + eapply build_certified_region_sound; exact PREVIOUS.
  - eapply build_certified_region_sound; exact RUN.
Qed.
Definition certified_affine_empty_runtime_extension existing profile : certified_region_builder :=
  {| build_certified_region:=build_affine_empty_runtime_extension existing profile;
     build_certified_region_sound:=@build_affine_empty_runtime_extension_sound existing profile |}.

Print Assumptions affine_empty_runtime_normalized_previous.
Print Assumptions check_affine_empty_runtime_source_sound.
Print Assumptions build_affine_empty_runtime_frontend_sound.
Print Assumptions build_affine_empty_runtime_extension_sound.
Print Assumptions certified_affine_empty_runtime_extension.
