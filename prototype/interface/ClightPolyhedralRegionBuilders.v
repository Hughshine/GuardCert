From Stdlib Require Import List.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion.
From GuardInterface Require Import ClightCertifiedRegionBuilder
  ClightLoopAdministrative ClightWordNestedStoreFrontend
  ClightWordNestedStoreScanService ClightAffineNestMaterializedCompiler.
Import CoreAlarmed.
Set Implicit Arguments.

(** Existing proved factories supply the same Clight boundary guarantee.
    Their source models, guards and candidate validators are not identified. *)
Definition certified_word_nested_builder prepare describe describe_cached propose
    : certified_region_builder :=
  {| build_certified_region :=
       fun public pool => check_word_nested_store_scan_service_frontend_region
         prepare public pool describe describe_cached propose;
     build_certified_region_sound := fun public pool source target =>
       @check_word_nested_store_scan_service_frontend_region_contract
         prepare public pool describe describe_cached propose source target |}.

Definition build_affine_frontend_region describe propose public pool source :=
  check_materialized_affine_region public pool describe propose (trim_loop_skips source).

Theorem build_affine_frontend_region_sound describe propose public pool source target :
  mayReturn (build_affine_frontend_region describe propose public pool source) (Some target) ->
  PrivateRegion.projected_region_contract public source target.
Proof.
  intro RUN; apply word_nested_store_frontend_contract.
  eapply check_materialized_affine_region_sound; exact RUN.
Qed.

Definition certified_affine_builder describe propose : certified_region_builder :=
  {| build_certified_region := build_affine_frontend_region describe propose;
     build_certified_region_sound := @build_affine_frontend_region_sound describe propose |}.

Definition certified_polyhedral_builder prepare word_describe cached_describe word_propose
    affine_describe affine_propose :=
  certified_region_or_else
    (certified_word_nested_builder prepare word_describe cached_describe word_propose)
    (certified_affine_builder affine_describe affine_propose).

Print Assumptions build_affine_frontend_region_sound.
Print Assumptions certified_word_nested_builder.
Print Assumptions certified_affine_builder.
Print Assumptions certified_polyhedral_builder.
