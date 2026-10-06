From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightFrontendLoopProtocol ClightTempFootprint ClightStraightLine.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import ClightDependentLoadedSource ClightObservedPointerSyntax
  ClightSourceObservation ClightAffineInnerPointerCandidates ClightAffineDependentLoadedPrefix ClightDependentCaptureDomain.
Import ListNotations.
Set Implicit Arguments.

Record affine_dependent_region_package live source pointer_cache cache := AffineDependentRegionPackage {
  dependent_region_site : dependent_snapshot_site source;
  dependent_region_cached_source : statement;
  dependent_region_package : memory_affine_inner_pointer_package dependent_region_cached_source;
  dependent_region_cache_exact : affine_inner_pointer_bound (affine_inner_pointer_shape dependent_region_package) = cache;
  dependent_region_loop_exact : observed_source_loop (dependent_site_observed dependent_region_site) =
    affine_dependent_loaded_source dependent_region_package (dependent_site_root dependent_region_site);
  dependent_region_root_fresh :
    dependent_site_root dependent_region_site <> affine_inner_pointer_row (affine_inner_pointer_shape dependent_region_package) /\
    dependent_site_root dependent_region_site <> affine_inner_pointer_column (affine_inner_pointer_shape dependent_region_package) /\
    dependent_site_root dependent_region_site <> affine_inner_pointer_inner_bound (affine_inner_pointer_shape dependent_region_package);
  dependent_region_pointer_fresh :
    pointer_cache <> affine_inner_pointer_row (affine_inner_pointer_shape dependent_region_package) /\
    pointer_cache <> affine_inner_pointer_column (affine_inner_pointer_shape dependent_region_package) /\
    pointer_cache <> affine_inner_pointer_inner_bound (affine_inner_pointer_shape dependent_region_package);
  dependent_region_pointer_private : ~ In pointer_cache (statement_temps (dependent_site_original dependent_region_site)++live);
  dependent_region_cache_private : ~ In cache (statement_temps (dependent_site_original dependent_region_site)++live);
  dependent_region_capture_distinct : pointer_cache <> dependent_site_root dependent_region_site /\
    cache <> dependent_site_root dependent_region_site /\ cache <> pointer_cache;
  dependent_region_observations : source_observations_check (affine_inner_pointer_pointers dependent_region_package)
    (observed_source_loads (dependent_site_observed dependent_region_site)) = true
}.

Definition check_affine_dependent_region live source (site : dependent_snapshot_site source) pointer_cache cache
  cached_source (package : memory_affine_inner_pointer_package cached_source) :
  option (affine_dependent_region_package live source pointer_cache cache).
Proof.
  destruct (peq (affine_inner_pointer_bound (affine_inner_pointer_shape package)) cache) as [BOUND|]; [|exact None].
  destruct (statement_eq (observed_source_loop (dependent_site_observed site))
    (affine_dependent_loaded_source package (dependent_site_root site))) as [LOOP|]; [|exact None].
  destruct (peq (dependent_site_root site) (affine_inner_pointer_row (affine_inner_pointer_shape package))) as [|RR]; [exact None|].
  destruct (peq (dependent_site_root site) (affine_inner_pointer_column (affine_inner_pointer_shape package))) as [|RC]; [exact None|].
  destruct (peq (dependent_site_root site) (affine_inner_pointer_inner_bound (affine_inner_pointer_shape package))) as [|RK]; [exact None|].
  destruct (peq pointer_cache (affine_inner_pointer_row (affine_inner_pointer_shape package))) as [|PR]; [exact None|].
  destruct (peq pointer_cache (affine_inner_pointer_column (affine_inner_pointer_shape package))) as [|PC]; [exact None|].
  destruct (peq pointer_cache (affine_inner_pointer_inner_bound (affine_inner_pointer_shape package))) as [|PK]; [exact None|].
  destruct (in_dec peq pointer_cache (statement_temps (dependent_site_original site)++live)) as [|PP]; [exact None|].
  destruct (in_dec peq cache (statement_temps (dependent_site_original site)++live)) as [|CP]; [exact None|].
  destruct (peq pointer_cache (dependent_site_root site)) as [|POINTER_ROOT]; [exact None|].
  destruct (peq cache (dependent_site_root site)) as [|CACHE_ROOT]; [exact None|].
  destruct (peq cache pointer_cache) as [|DISTINCT]; [exact None|].
  destruct (source_observations_check (affine_inner_pointer_pointers package)
    (observed_source_loads (dependent_site_observed site))) eqn:OBSERVED; [|exact None].
  exact (Some (@AffineDependentRegionPackage live source pointer_cache cache site cached_source package BOUND LOOP
    (conj RR (conj RC RK)) (conj PR (conj PC PK)) PP CP (conj POINTER_ROOT (conj CACHE_ROOT DISTINCT)) OBSERVED)).
Defined.

Definition describe_affine_dependent_source live pointer_cache cache (profile : affine_inner_pointer_profiler) source :=
  match describe_dependent_snapshot_site source with
  | Some site => let cached := frontend_counted_loop (dependent_site_row site) cache (dependent_site_body site) in
    match profile cached with
    | Some metadata => match describe_affine_inner_pointer_at cached metadata with
      | Some package => check_affine_dependent_region live site pointer_cache cache package
      | None => None end
    | None => None end
  | None => None end.

Lemma dependent_site_load_pointer_temp source (site : dependent_snapshot_site source) identifier :
  In identifier (source_load_pointers (observed_source_loads (dependent_site_observed site))) ->
  In identifier (statement_temps (dependent_site_original site)).
Proof.
  intro MEMBER; unfold dependent_site_original; cbn [ClightDependentSnapshotInsertion.dependent_snapshot_original statement_temps].
  apply in_or_app; left; apply source_load_pointer_is_temp; exact MEMBER.
Qed.
Lemma dependent_region_pointer_no_load live source pointer_cache cache
  (region : affine_dependent_region_package live source pointer_cache cache) :
  ~ In pointer_cache (source_load_pointers (observed_source_loads (dependent_site_observed (dependent_region_site region)))).
Proof.
  intro MEMBER; apply (dependent_region_pointer_private region),in_or_app; left.
  apply dependent_site_load_pointer_temp; exact MEMBER.
Qed.
Lemma dependent_region_cache_no_load live source pointer_cache cache
  (region : affine_dependent_region_package live source pointer_cache cache) :
  ~ In cache (source_load_pointers (observed_source_loads (dependent_site_observed (dependent_region_site region)))).
Proof.
  intro MEMBER; apply (dependent_region_cache_private region),in_or_app; left.
  apply dependent_site_load_pointer_temp; exact MEMBER.
Qed.

Print Assumptions check_affine_dependent_region.
Print Assumptions describe_affine_dependent_source.
Print Assumptions dependent_region_pointer_no_load.
Print Assumptions dependent_region_cache_no_load.
