From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightTempFrame ClightTempFootprint CompCertMemoryEquivalence ClightPrivateRegion.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightPrivateScanHost ClightPrivateScanPreservation ClightSourceObservation.
Set Implicit Arguments.

Definition private_scan_readonly_shortcut live source (rule : private_scan_preserving_rule live source) tree :=
  tree_statement tree (scan_candidate rule)
    (select (private_scan_host (adapter_entry false) (scan_public_observe live))
      (scan_condition rule) (scan_candidate rule) source).

(** The optimization's local proof and the original safe fallback scan are
    reused. Only the new readonly sufficient condition and its permitted
    observations are supplied by the domain service. *)
Theorem private_scan_shortcut_preservation live source (rule : private_scan_preserving_rule live source)
  receipt tree
  (CHECK : forall temps, readonly_condition
    (readonly_clight_host (adapter_entry temps) (scan_public_observe live))
    (fun entry => scan_domain rule entry /\ receipt entry) (scan_premise rule) tree)
  temps (p : Clight.program) locals entry memory after final :
  statement_scope live source -> receipt (Entry (globalenv p) locals entry memory) ->
  exec_stmt (adapter_entry temps) (globalenv p) locals entry memory source E0 after final Out_normal ->
  exists exit result,
    exec_stmt (adapter_entry temps) (globalenv p) locals entry memory
      (private_scan_readonly_shortcut rule tree) E0 exit result Out_normal /\
    temp_agree live after exit /\ memory_equivalent final result.
Proof.
  intros SCOPE RECEIPT SOURCE.
  set (host := readonly_clight_host (adapter_entry temps) (scan_public_observe live)).
  set (domain := fun state => entry_ge state = globalenv p /\ scan_domain rule state /\ receipt state).
  set (fallback := select (private_scan_host (adapter_entry temps) (scan_public_observe live))
    (scan_condition rule) (scan_candidate rule) source).
  assert (LOCAL : preservation_certificate host domain (scan_premise rule) eq eq eq
    source (scan_candidate rule) fallback).
  { constructor.
    - intros original checked observed [GE [DOMAIN RECEIPT']] PREMISE SAME [raw [RUN OBSERVE]].
      subst checked; destruct original as [ge env le m]; cbn in GE; subst ge.
      destruct OBSERVE as [TRACE [OUTCOME [PUBLIC MEMORY]]].
      unfold clight_fragment_run in RUN; cbn in RUN; rewrite TRACE,OUTCOME in RUN.
      destruct (scan_local rule SCOPE RUN PREMISE) as [exit [result [EXEC [EXIT RESULT]]]].
      exists observed; split; [|reflexivity].
      exists (FragmentObservation E0 exit result Out_normal); split; [exact EXEC|].
      split; [reflexivity|split; [reflexivity|split]].
      + eapply temp_agree_trans; eassumption.
      + eapply memory_equivalent_trans; eassumption.
    - intros original checked observed [GE [DOMAIN RECEIPT']] SAME RUN; subst checked.
      exists observed; split; [|reflexivity].
      apply (@scan_guarded_source_preservation live source rule temps p SCOPE original observed);
        [split; assumption|exact RUN]. }
  assert (CONDITION : readonly_condition host domain (scan_premise rule) tree).
  { apply readonly_condition_restrict with (domain:=fun state => scan_domain rule state /\ receipt state).
    - exact (CHECK temps).
    - intros state [_ DOMAIN]; exact DOMAIN. }
  assert (DOMAIN : domain (Entry (globalenv p) locals entry memory)).
  { split; [reflexivity|split; [eapply scan_source_domain; exact SOURCE|exact RECEIPT]]. }
  assert (ORIGINAL : runs host source (Entry (globalenv p) locals entry memory) (after,final)).
  { exists (FragmentObservation E0 after final Out_normal); split; [exact SOURCE|].
    split; [reflexivity|split; [reflexivity|split; [apply temp_agree_refl|apply memory_equivalent_refl]]]. }
  destruct (@guardify_preservation _ host domain (scan_premise rule) eq eq eq source
    (scan_candidate rule) fallback tree (readonly_guard_certificate CONDITION) LOCAL _ _ DOMAIN ORIGINAL)
    as [observed [RUN SAME]]; subst observed.
  destruct RUN as [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
  exists (fragment_temps raw),(fragment_memory raw); split; [|split; assumption].
  unfold clight_fragment_run in RUN; rewrite TRACE,OUTCOME in RUN; exact RUN.
Qed.

Print Assumptions private_scan_shortcut_preservation.
