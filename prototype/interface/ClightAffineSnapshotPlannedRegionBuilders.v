From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardInterface Require Import ClightCertifiedRegionBuilder ClightLoopAdministrative
  ClightWordNestedStoreFrontend ClightAffineSnapshotPlannedCandidates.
Import CoreAlarmed.
Set Implicit Arguments.

(** Administrative normalization is an already proved language service. Site
    selection and progress continue to refer to the actual original source. *)
Definition build_affine_snapshot_planned_frontend profile propose public pool source :=
  check_affine_snapshot_planned_source public pool profile propose(trim_loop_skips source).
Theorem build_affine_snapshot_planned_frontend_sound profile propose public pool source target :
  mayReturn(build_affine_snapshot_planned_frontend profile propose public pool source)(Some target) ->
  PrivateRegion.projected_region_contract public source target.
Proof.
  intro RUN; apply word_nested_store_frontend_contract.
  eapply check_affine_snapshot_planned_source_sound; exact RUN.
Qed.
Definition certified_affine_snapshot_planned_builder profile propose : certified_region_builder :=
  {| build_certified_region:=build_affine_snapshot_planned_frontend profile propose;
     build_certified_region_sound:=@build_affine_snapshot_planned_frontend_sound profile propose |}.
Definition certified_affine_snapshot_planned_extension existing profile propose :=
  certified_region_or_else existing(certified_affine_snapshot_planned_builder profile propose).

Print Assumptions build_affine_snapshot_planned_frontend_sound.
Print Assumptions certified_affine_snapshot_planned_builder.
Print Assumptions certified_affine_snapshot_planned_extension.
