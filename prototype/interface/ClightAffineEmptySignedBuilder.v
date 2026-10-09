From Stdlib Require Import List.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightAffineSnapshotSyntax ClightAffineSnapshotCaptureCandidate
  ClightAffineZeroSnapshotPreparation ClightAffineEmptyWidth ClightAffineEmptySignedCondition
  ClightAffineEmptyConditionCapture ClightCheckPlanFrame ClightAffineEmptySnapshotPlannedBuilder
  ClightObservedPointerSyntax ClightSourceObservation ClightSequenceContracts
  ClightCertifiedRegionBuilder ClightLoopAdministrative ClightWordNestedStoreFrontend.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** A checked conditional rewrite independent of a polyhedral candidate. The
    existing optimization registry keeps priority. Thus accepting this source
    family never hides a candidate previously installed by that registry. *)
Definition check_affine_empty_signed_source live pool profile source :=
  match pool with
  | (root_cache,root_type)::(child_cache,child_type)::(result,result_type)::_=>
    if type_eq root_type type_int32s then if type_eq child_type type_int32s then if type_eq result_type type_int32s then
      match describe_observed_pointer_source source with
      | Some observed=>match describe_affine_snapshot_source profile root_cache child_cache(observed_source_loop observed)with
        | Some site=>match check_affine_snapshot_capture site live with
          | Some capture=>let package:=snapshot_cached_package site in
            match compile_affine_empty_width(affine_inner_pointer_row(affine_inner_pointer_shape package))
              (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
              (affine_empty_signed_header_bounds site)(affine_inner_pointer_expression package)with
            | Some width=>if check_plan_resources(affine_empty_client_plan site(affine_empty_signed_tree site width))result live
                (affine_empty_client_yes site)(observed_source_loop observed)then pure(Some(Ssequence
                (Ssequence(source_load_prefix(observed_source_loads observed))(affine_empty_client_captured site(affine_empty_signed_tree site width)result))
                (observed_source_suffix observed)))else pure None
            | None=>pure None end
          | None=>pure None end
        | None=>pure None end
      | None=>pure None end
    else pure None else pure None else pure None
  | _=>pure None end.

Theorem check_affine_empty_signed_source_sound live pool profile source target :
  mayReturn(check_affine_empty_signed_source live pool profile source)(Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_affine_empty_signed_source; destruct pool as [|[root_cache root_type][|[child_cache child_type][|[result result_type]rest]]];
    try solve[intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(type_eq root_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(type_eq child_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(type_eq result_type type_int32s); [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(describe_observed_pointer_source source)as [observed|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(describe_affine_snapshot_source _ _ _ _)as [site|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(check_affine_snapshot_capture site live)as [capture|]; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(compile_affine_empty_width _ _ _ _)as [width|]eqn:WIDTH; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct(check_plan_resources _ _ _ _ _)eqn:RESOURCES; [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; apply mayReturn_pure in RUN; injection RUN as <-.
  eapply flattened_projected_region_contract; [exact(observed_source_flat observed)|].
  apply projected_region_quiet_suffix; [exact(observed_source_suffix_quiet observed)|].
  exact(@affine_empty_client_prefix_contract(observed_source_loop observed)site live capture
    (affine_empty_signed_tree site width)
    (fun fe=>@affine_empty_signed_condition(observed_source_loop observed)site width WIDTH fe fragment_observation
      (@eq fragment_observation))result RESOURCES
    (observed_source_loads observed)).
Qed.

Definition build_affine_empty_signed_frontend profile public pool source:=
  check_affine_empty_signed_source public pool profile(trim_loop_skips source).
Theorem build_affine_empty_signed_frontend_sound profile public pool source target :
  mayReturn(build_affine_empty_signed_frontend profile public pool source)(Some target) ->
  PrivateRegion.projected_region_contract public source target.
Proof.
  intro RUN; apply word_nested_store_frontend_contract;
    eapply check_affine_empty_signed_source_sound; exact RUN.
Qed.
Definition certified_affine_empty_signed_builder profile : certified_region_builder:=
  {|build_certified_region:=build_affine_empty_signed_frontend profile;
    build_certified_region_sound:=@build_affine_empty_signed_frontend_sound profile|}.
Definition certified_affine_empty_signed_extension existing profile:=
  certified_region_or_else existing
    (certified_region_or_else(certified_affine_empty_signed_builder profile)
      (certified_affine_empty_snapshot_planned_builder profile)).

Print Assumptions check_affine_empty_signed_source_sound.
Print Assumptions build_affine_empty_signed_frontend_sound.
Print Assumptions certified_affine_empty_signed_builder.
Print Assumptions certified_affine_empty_signed_extension.
