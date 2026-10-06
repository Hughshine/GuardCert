From Stdlib Require Import List.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion ClightTempFootprint.
From GuardInterface Require Import ClightPrivateLoadedSource ClightAffineInnerPointerCandidates
  ClightAffinePlannedLoadedCandidates.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Reserve one private snapshot, then delegate all source-model, condition,
    dependence, lowering and candidate checks to the existing compiler path.
    Only the original source is installed as a rewrite-table key. *)
Definition check_affine_private_loaded_source live pool profile propose source :=
  match pool with
  | [] => pure None
  | (cache,_)::check_pool => match describe_loaded_snapshot_site source with
    | Some site =>
      if in_dec peq cache (statement_temps (snapshot_site_original site)++live) then pure None else
        check_affine_planned_loaded_source (cache::live) check_pool profile propose (snapshot_site_prepared site cache)
    | None => pure None end
  end.

Theorem check_affine_private_loaded_source_sound live pool profile propose source target :
  mayReturn (check_affine_private_loaded_source live pool profile propose source) (Some target) ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  unfold check_affine_private_loaded_source; destruct pool as [|[cache cache_type] check_pool];
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  destruct (describe_loaded_snapshot_site source) as [site|];
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (in_dec peq cache _) as [BAD|PRIVATE];
    [intro RUN; apply mayReturn_pure in RUN; discriminate|].
  intro RUN; eapply snapshot_site_prepared_contract; [exact PRIVATE|].
  eapply check_affine_planned_loaded_source_sound; exact RUN.
Qed.

Print Assumptions check_affine_private_loaded_source_sound.
