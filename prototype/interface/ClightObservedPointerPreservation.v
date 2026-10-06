From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightTempFrame ClightTempFootprint
  ClightLoopSyntax ClightPrivateRegion.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightPrivateScanPreservation
  ClightSourceObservation ClightPrivateScanShortcut ClightParamPointerEnvelope.
Import ListNotations.
Set Implicit Arguments.

Definition observed_param_pointer_target live source (package : memory_param_pointer_region_package source)
  (rule : private_scan_preserving_rule live source) loads :=
  Ssequence (source_load_prefix loads)
    (private_scan_readonly_shortcut rule (param_pointer_envelope_tree package)).

(** The source prefix establishes the observation domain at the actual loop
    entry. The existing loop rule provides C_opt and the original scan; the
    envelope library provides C_derive/C_guard. Installation reuses the finite
    private-region host, with no base-valid premise added to the original D. *)
Theorem observed_param_pointer_region_contract live source (package : memory_param_pointer_region_package source)
  (rule : private_scan_preserving_rule live source) loads :
  scan_domain rule = memory_param_pointer_runtime_domain package ->
  scan_premise rule = memory_param_pointer_runtime_presumption package ->
  (forall identifier, In identifier (param_pointer_region_pointers package) ->
    In identifier (source_load_pointers loads)) ->
  (forall identifier, In identifier (source_load_targets loads) -> ~ In identifier (source_load_pointers loads)) ->
  PrivateRegion.projected_region_contract live
    (Ssequence (source_load_prefix loads) source) (observed_param_pointer_target package rule loads).
Proof.
  intros DOMAIN PREMISE COVER FRESH; unfold observed_param_pointer_target.
  apply source_prefix_region_contract with
    (writes:=source_load_targets loads++scan_writes rule)
    (domain:=observed_pointer_domain (param_pointer_region_pointers package)).
  - apply source_load_prefix_supported.
  - constructor.
    + eapply writes_only_weaken; [intros identifier MEMBER; apply in_or_app; left; exact MEMBER|apply source_load_prefix_writes].
    + eapply writes_only_weaken; [intros identifier MEMBER; apply in_or_app; right; exact MEMBER|apply scan_source_writes].
  - intros temps p locals entry memory middle after final PREFIX BODY.
    destruct (@source_load_prefix_observations loads (adapter_entry temps) (globalenv p) locals entry memory
      E0 middle memory Out_normal FRESH PREFIX) as [_ [_ [_ OBSERVED]]].
    intros identifier MEMBER; apply OBSERVED,COVER; exact MEMBER.
  - intros temps p locals entry memory after final SCOPE OBSERVED SOURCE.
    refine (@private_scan_shortcut_preservation live source rule
      (observed_pointer_domain (param_pointer_region_pointers package)) (param_pointer_envelope_tree package)
      _ temps p locals entry memory after final SCOPE OBSERVED SOURCE).
    intro mode; rewrite DOMAIN,PREMISE; apply param_pointer_envelope_condition.
Qed.

Print Assumptions observed_param_pointer_region_contract.
