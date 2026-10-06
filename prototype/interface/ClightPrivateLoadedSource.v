From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightTempFootprint ClightStraightLine ClightPrivateRegion.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedSequenceProgress
  ClightLoadedSnapshotInsertion ClightObservedPointerSyntax ClightSourceObservation
  ClightCheckPlanFrame ClightSequenceContracts.
Import ListNotations.
Set Implicit Arguments.

(** The language selector locates an actual loaded header after a retained
    source prefix. It does not synthesize optimization premises or assume
    availability of future accesses. The optimizer consumes the checked
    intermediate source through its existing interface. *)
Record loaded_snapshot_site source := LoadedSnapshotSite {
  snapshot_site_observed : observed_pointer_source_package source;
  snapshot_site_row : ident;
  snapshot_site_pointer : ident;
  snapshot_site_body : statement;
  snapshot_site_loop_exact : observed_source_loop snapshot_site_observed =
    loaded_bound_loop snapshot_site_row snapshot_site_pointer snapshot_site_body;
  snapshot_site_frameable : check_plan_frameable
    (loaded_snapshot_original (observed_source_loads snapshot_site_observed)
      snapshot_site_row snapshot_site_pointer snapshot_site_body (observed_source_suffix snapshot_site_observed)) = true
}.

Definition snapshot_site_original source (site : loaded_snapshot_site source) :=
  loaded_snapshot_original (observed_source_loads (snapshot_site_observed site))
    (snapshot_site_row site) (snapshot_site_pointer site) (snapshot_site_body site)
    (observed_source_suffix (snapshot_site_observed site)).
Definition snapshot_site_prepared source (site : loaded_snapshot_site source) cache :=
  loaded_snapshot_prepared (observed_source_loads (snapshot_site_observed site))
    (snapshot_site_row site) (snapshot_site_pointer site) (snapshot_site_body site)
    (observed_source_suffix (snapshot_site_observed site)) cache.

Lemma snapshot_site_original_flat source (site : loaded_snapshot_site source) :
  flatten_region source = flatten_region (snapshot_site_original site).
Proof.
  rewrite (observed_source_flat (snapshot_site_observed site)),(snapshot_site_loop_exact site).
  unfold snapshot_site_original,loaded_snapshot_original; cbn [flatten_region]; rewrite app_assoc; reflexivity.
Qed.

Definition check_loaded_snapshot_site source (observed : observed_pointer_source_package source)
  row pointer body (EXACT : observed_source_loop observed = loaded_bound_loop row pointer body) :
  option (loaded_snapshot_site source).
Proof.
  destruct (Bool.bool_dec (check_plan_frameable (loaded_snapshot_original
    (observed_source_loads observed) row pointer body (observed_source_suffix observed))) true) as [FRAME|];
    [exact (Some (@LoadedSnapshotSite source observed row pointer body EXACT FRAME))|exact None].
Defined.

Definition describe_loaded_snapshot_site source : option (loaded_snapshot_site source).
Proof.
  destruct (describe_observed_pointer_source source) as [observed|]; [|exact None].
  destruct (checked_loaded_progress (observed_source_loop observed)) as [[[row pointer] body]|] eqn:LOOP;
    [exact (check_loaded_snapshot_site observed (@checked_loaded_progress_binds _ _ _ _ LOOP))|exact None].
Defined.

Theorem snapshot_site_prepared_contract live source (site : loaded_snapshot_site source) cache target :
  ~ In cache (statement_temps (snapshot_site_original site)++live) ->
  PrivateRegion.projected_region_contract (cache::live) (snapshot_site_prepared site cache) target ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  intros PRIVATE CONTRACT; eapply flattened_projected_region_contract;
    [exact (snapshot_site_original_flat site)|].
  eapply loaded_snapshot_insertion_contract;
    [exact (snapshot_site_frameable site)|exact PRIVATE|exact CONTRACT].
Qed.

Print Assumptions snapshot_site_original_flat.
Print Assumptions check_loaded_snapshot_site.
Print Assumptions describe_loaded_snapshot_site.
Print Assumptions snapshot_site_prepared_contract.
