From Stdlib Require Import List.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardInterface Require Import ClightCertifiedRegionBuilder
  ClightLoopAdministrative ClightWordNestedStoreFrontend
  ClightPolyhedralRegionBuilders.
From GuardLoadedAffine Require Import ClightAffinePrivateLoadedCandidates.
Import CoreAlarmed.
Set Implicit Arguments.

(** The existing loaded-source factory proves its own snapshot, stability,
    source/model and public-exit obligations. This registration reuses the
    selected host; it does not identify the three source models. *)
Definition build_private_loaded_affine_frontend profile propose public pool source :=
  check_affine_private_loaded_source public pool profile propose (trim_loop_skips source).

Theorem build_private_loaded_affine_frontend_sound profile propose public pool source target :
  mayReturn (build_private_loaded_affine_frontend profile propose public pool source)
    (Some target) -> PrivateRegion.projected_region_contract public source target.
Proof.
  intro RUN; apply word_nested_store_frontend_contract.
  eapply check_affine_private_loaded_source_sound; exact RUN.
Qed.

Definition certified_private_loaded_affine_builder profile propose : certified_region_builder :=
  {| build_certified_region := build_private_loaded_affine_frontend profile propose;
     build_certified_region_sound := @build_private_loaded_affine_frontend_sound profile propose |}.

Definition certified_loaded_polyhedral_builder prepare word_describe cached_describe
    word_propose affine_describe affine_propose loaded_profile loaded_propose :=
  certified_region_or_else
    (certified_polyhedral_builder prepare word_describe cached_describe word_propose
      affine_describe affine_propose)
    (certified_private_loaded_affine_builder loaded_profile loaded_propose).

Print Assumptions build_private_loaded_affine_frontend_sound.
Print Assumptions certified_private_loaded_affine_builder.
Print Assumptions certified_loaded_polyhedral_builder.
