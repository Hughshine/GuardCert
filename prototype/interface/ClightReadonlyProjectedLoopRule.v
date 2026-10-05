From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightRegionProgress ClightTempFrame.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightRegionBoundary ClightLoopBridge ClightReadonlyProjectedCompiler.
Set Implicit Arguments.

Definition readonly_projected_forward_loop_rule live source candidate guard domain premise writes
  (WRITES : writes_only writes source)
  (SOURCE_QUIET : quiet_statement source = true)
  (CANDIDATE_QUIET : quiet_statement candidate = true)
  (CHECK : forall temps,
    readonly_condition (readonly_clight_host (adapter_entry temps) (boundary_observe (public_exit_ports live)))
      domain premise guard)
  (FORWARD : forall temps entry observed, domain entry -> premise entry ->
    clight_fragment_run (adapter_entry temps) source entry observed -> exists transformed,
      clight_fragment_run (adapter_entry temps) candidate entry transformed /\
      boundary_observe (public_exit_ports live) observed transformed)
  (ENTRY : forall temps (p : Clight.program) e le m le' m',
    exec_stmt (adapter_entry temps) (Clight.globalenv p) e le m source E0 le' m' Out_normal ->
    domain (Entry (Clight.globalenv p) e le m)) : readonly_projected_clight_rule live source.
Proof.
  refine {| projected_candidate := candidate; projected_guard := guard;
    projected_domain := fun entry => domain entry /\ quiet_source_completion source entry;
    projected_premise := premise; projected_source_writes := writes;
    projected_source_write_bound := WRITES |}.
  - intro temps; eapply readonly_condition_restrict;
      [apply CHECK|intros entry [DOMAIN _]; exact DOMAIN].
  - intro temps; apply quiet_observed_forward_loop_equivalent.
    + apply boundary_observe_sym.
    + apply boundary_observe_trans.
    + intros entry [_ COMPLETE] _; exact COMPLETE.
    + exact CANDIDATE_QUIET.
    + intros entry observed [DOMAIN _] PREMISE SOURCE; exact (FORWARD temps entry observed DOMAIN PREMISE SOURCE).
  - intros temps p e le m le' m' SOURCE; split.
    + exact (ENTRY temps p e le m le' m' SOURCE).
    + exact (@quiet_source_completion_from_run source (adapter_entry temps)
        (Entry (Clight.globalenv p) e le m) (FragmentObservation E0 le' m' Out_normal) SOURCE_QUIET SOURCE).
Defined.

Print Assumptions readonly_projected_forward_loop_rule.
