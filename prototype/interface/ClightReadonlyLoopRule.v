From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightRegionProgress.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightLoopBridge ClightReadonlyCompiler.
Set Implicit Arguments.

(** An author can reuse a forward execution proof for a quiet loop. The
    completion witness is a ghost obtained from an actual source execution;
    the runtime condition only depends on the author's base entry domain.
    The resulting rule preserves raw exits, so it fits the current global
    compiler adapter. Projected private exits need a different context bridge. *)
Definition readonly_forward_loop_rule source candidate guard domain premise
  (SOURCE_QUIET : quiet_statement source = true)
  (CANDIDATE_QUIET : quiet_statement candidate = true)
  (CHECK : forall temps,
    readonly_condition (readonly_clight_host (adapter_entry temps) (@eq fragment_observation))
      domain premise guard)
  (FORWARD : forall temps entry observed, domain entry -> premise entry ->
    clight_fragment_run (adapter_entry temps) source entry observed ->
    clight_fragment_run (adapter_entry temps) candidate entry observed)
  (ENTRY : forall temps (p : Clight.program) e le m le' m',
    exec_stmt (adapter_entry temps) (Clight.globalenv p) e le m source E0 le' m' Out_normal ->
    domain (Entry (Clight.globalenv p) e le m)) : readonly_clight_rule source.
Proof.
  refine {| readonly_candidate := candidate; readonly_guard := guard;
    readonly_domain := fun entry => domain entry /\ quiet_source_completion source entry;
    readonly_premise := premise |}.
  - intro temps; eapply readonly_condition_restrict;
      [apply CHECK|intros entry [DOMAIN _]; exact DOMAIN].
  - intro temps; apply quiet_forward_loop_equivalent.
    + intros entry [_ COMPLETE] _; exact COMPLETE.
    + exact CANDIDATE_QUIET.
    + intros entry observed [DOMAIN _] PREMISE RUN; exact (FORWARD temps entry observed DOMAIN PREMISE RUN).
  - intros temps p e le m le' m' RUN; split.
    + exact (ENTRY temps p e le m le' m' RUN).
    + exact (@quiet_source_completion_from_run source (adapter_entry temps)
        (Entry (Clight.globalenv p) e le m) (FragmentObservation E0 le' m' Out_normal)
        SOURCE_QUIET RUN).
Defined.

Print Assumptions readonly_forward_loop_rule.
