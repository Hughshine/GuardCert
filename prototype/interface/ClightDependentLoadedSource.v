From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightStraightLine ClightTempFootprint ClightPrivateRegion.
From GuardInterface Require Import ClightDependentBoundSyntax ClightDependentSnapshotInsertion
  ClightObservedPointerSyntax ClightSourceObservation ClightCheckPlanFrame ClightSequenceContracts.
Import ListNotations.
Set Implicit Arguments.

Definition propose_dependent_source_loop source :=
  match source with
  | Sloop (Ssequence (Ssequence Sskip (Sifthenelse
      (Ebinop Olt (Etempvar row _) (Ederef (Ederef (Etempvar root _) _) _) _) Sskip Sbreak)) body) _ =>
    Some (row,root,body)
  | _ => None end.
Definition checked_dependent_source_loop source :=
  match propose_dependent_source_loop source with
  | Some (row,root,body) => if statement_eq source (dependent_bound_loop row root body)
      then Some (row,root,body) else None
  | None => None end.
Lemma checked_dependent_source_loop_binds source row root body :
  checked_dependent_source_loop source = Some (row,root,body) -> source = dependent_bound_loop row root body.
Proof.
  unfold checked_dependent_source_loop.
  destruct (propose_dependent_source_loop source) as [[[i p] code]|]; [|discriminate].
  destruct (statement_eq source (dependent_bound_loop i p code)) as [EXACT|]; [|discriminate].
  intro SELECT; inversion SELECT; subst; reflexivity.
Qed.

Record dependent_snapshot_site source := DependentSnapshotSite {
  dependent_site_observed : observed_pointer_source_package source;
  dependent_site_row : ident;
  dependent_site_root : ident;
  dependent_site_body : statement;
  dependent_site_loop_exact : observed_source_loop dependent_site_observed =
    dependent_bound_loop dependent_site_row dependent_site_root dependent_site_body;
  dependent_site_frameable : check_plan_frameable
    (dependent_snapshot_original (source_load_prefix (observed_source_loads dependent_site_observed))
      dependent_site_row dependent_site_root dependent_site_body (observed_source_suffix dependent_site_observed)) = true
}.
Definition dependent_site_original source (site : dependent_snapshot_site source) :=
  dependent_snapshot_original (source_load_prefix (observed_source_loads (dependent_site_observed site)))
    (dependent_site_row site) (dependent_site_root site) (dependent_site_body site)
    (observed_source_suffix (dependent_site_observed site)).
Definition dependent_site_prepared source (site : dependent_snapshot_site source) pointer_cache bound_cache :=
  dependent_snapshot_prepared (source_load_prefix (observed_source_loads (dependent_site_observed site)))
    (dependent_site_row site) (dependent_site_root site) (dependent_site_body site)
    (observed_source_suffix (dependent_site_observed site)) pointer_cache bound_cache.
Lemma dependent_site_original_flat source (site : dependent_snapshot_site source) :
  flatten_region source = flatten_region (dependent_site_original site).
Proof.
  rewrite (observed_source_flat (dependent_site_observed site)),(dependent_site_loop_exact site).
  unfold dependent_site_original,dependent_snapshot_original; cbn [flatten_region]; rewrite app_assoc; reflexivity.
Qed.
Definition check_dependent_snapshot_site source (observed : observed_pointer_source_package source)
  row root body (EXACT : observed_source_loop observed = dependent_bound_loop row root body) :
  option (dependent_snapshot_site source).
Proof.
  destruct (Bool.bool_dec (check_plan_frameable (dependent_snapshot_original (source_load_prefix (observed_source_loads observed))
    row root body (observed_source_suffix observed))) true) as [FRAME|]; [|exact None].
  exact (Some (@DependentSnapshotSite source observed row root body EXACT FRAME)).
Defined.
Definition describe_dependent_snapshot_site source : option (dependent_snapshot_site source).
Proof.
  destruct (describe_observed_pointer_source source) as [observed|]; [|exact None].
  destruct (checked_dependent_source_loop (observed_source_loop observed)) as [[[row root] body]|] eqn:LOOP;
    [exact (check_dependent_snapshot_site observed (@checked_dependent_source_loop_binds _ _ _ _ LOOP))|exact None].
Defined.
Theorem dependent_site_prepared_contract live source (site : dependent_snapshot_site source) pointer_cache bound_cache target :
  ~ In pointer_cache (statement_temps (dependent_site_original site)++live) ->
  ~ In bound_cache (statement_temps (dependent_site_original site)++live) ->
  PrivateRegion.projected_region_contract ([pointer_cache;bound_cache]++live)
    (dependent_site_prepared site pointer_cache bound_cache) target ->
  PrivateRegion.projected_region_contract live source target.
Proof.
  intros POINTER BOUND CONTRACT; eapply flattened_projected_region_contract; [exact (dependent_site_original_flat site)|].
  eapply dependent_snapshot_insertion_contract; [exact (dependent_site_frameable site)|exact POINTER|exact BOUND|exact CONTRACT].
Qed.

Print Assumptions checked_dependent_source_loop_binds.
Print Assumptions dependent_site_original_flat.
Print Assumptions describe_dependent_snapshot_site.
Print Assumptions dependent_site_prepared_contract.
