From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightRegionProgress ClightPrivateRegion ClightTempFrame
  ClightTempFootprint ClightProjectedExecution CompCertMemoryEquivalence.
From GuardInterface Require Import GuardInterface ClightReadonlyRewrite ClightPrivateScanHost.
Set Implicit Arguments.

Definition scan_public_observe live (raw : fragment_observation) (observed : temp_env * mem) :=
  fragment_trace raw = E0 /\ fragment_outcome raw = Out_normal /\
  temp_agree live (fst observed) (fragment_temps raw) /\
  memory_equivalent (snd observed) (fragment_memory raw).

(** Domain instances supply the encoder and the conditional local theorem.
    This language adapter transports the source across private entry writes
    and installs the kernel's preservation result in actual Clight control. *)
Record private_scan_preserving_rule (live : list ident) (source : statement) := {
  scan_candidate : statement;
  scan_condition : private_scan_test;
  scan_domain : clight_entry -> Prop;
  scan_premise : clight_entry -> Prop;
  scan_ports : list ident;
  scan_ports_live : forall identifier, In identifier live -> In identifier scan_ports;
  scan_writes : list ident;
  scan_source_writes : writes_only scan_writes source;
  scan_condition_certificate : forall temps,
    guard_certificate (private_scan_host (adapter_entry temps) (scan_public_observe live))
      scan_domain scan_premise (private_scan_entry_frame scan_ports)
      (private_scan_entry_frame scan_ports) scan_condition;
  scan_premise_frame : forall entry checked,
    scan_domain entry -> scan_premise entry -> private_scan_entry_frame scan_ports entry checked -> scan_premise checked;
  scan_local : forall temps p locals le memory after final,
    statement_scope live source ->
    exec_stmt (adapter_entry temps) (globalenv p) locals le memory source E0 after final Out_normal ->
    scan_premise (Entry (globalenv p) locals le memory) ->
    exists exit mem,
      exec_stmt (adapter_entry temps) (globalenv p) locals le memory scan_candidate E0 exit mem Out_normal /\
      temp_agree live after exit /\ memory_equivalent final mem;
  scan_source_domain : forall temps p locals le memory after final,
    exec_stmt (adapter_entry temps) (globalenv p) locals le memory source E0 after final Out_normal ->
    scan_domain (Entry (globalenv p) locals le memory)
}.

Section PRESERVATION.
Variable live : list ident.
Variable source : statement.
Variable rule : private_scan_preserving_rule live source.
Variable temps : bool.
Variable p : Clight.program.
Hypothesis SCOPE : statement_scope live source.
Let host := private_scan_host (adapter_entry temps) (scan_public_observe live).
Definition scan_program_domain entry := entry_ge entry = globalenv p /\ scan_domain rule entry.

Definition scan_program_guard_certificate :
  guard_certificate host scan_program_domain (scan_premise rule)
    (private_scan_entry_frame (scan_ports rule)) (private_scan_entry_frame (scan_ports rule)) (scan_condition rule).
Proof.
  constructor.
  - intros entry [_ DOMAIN]; exact (check_safety (scan_condition_certificate rule temps) entry DOMAIN).
  - intros entry [_ DOMAIN]; exact (check_available (scan_condition_certificate rule temps) entry DOMAIN).
  - intros entry accepted checked [_ DOMAIN] CHECK.
    exact (check_sound (scan_condition_certificate rule temps) entry accepted checked DOMAIN CHECK).
Defined.

Lemma scan_source_transport entry checked original :
  scan_program_domain entry -> private_scan_entry_frame (scan_ports rule) entry checked ->
  runs host source entry original -> runs host source checked original.
Proof.
  destruct entry as [ge locals le memory], checked as [current_ge current_locals current current_memory].
  intros [GE DOMAIN] [CHECK_GE [CHECK_ENV [CHECK_MEMORY AGREE]]] [raw [RUN OBSERVE]].
  cbn [entry_ge entry_env entry_memory entry_temps] in *; subst ge current_ge current_locals current_memory.
  destruct OBSERVE as [TRACE [OUTCOME [PUBLIC MEMORY]]].
  unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_temps entry_memory] in RUN.
  rewrite TRACE, OUTCOME in RUN.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory source
    E0 (fragment_temps raw) (fragment_memory raw) Out_normal RUN live current
    (scan_writes rule) (scan_source_writes rule) SCOPE
    ltac:(eapply temp_agree_weaken; [exact (scan_ports_live rule)|exact AGREE])) as [after [EXEC FRAME]].
  exists (FragmentObservation E0 after (fragment_memory raw) Out_normal); split; [exact EXEC|].
  split; [reflexivity|split; [reflexivity|split; [eapply temp_agree_trans; eassumption|exact MEMORY]]].
Qed.

Definition scan_local_preservation_certificate :
  preservation_certificate host scan_program_domain (scan_premise rule)
    (private_scan_entry_frame (scan_ports rule)) (private_scan_entry_frame (scan_ports rule))
    eq source (scan_candidate rule) source.
Proof.
  constructor.
  - intros entry checked original DOMAIN PREMISE FRAME SOURCE.
    pose proof (scan_source_transport DOMAIN FRAME SOURCE) as TRANSPORTED.
    pose proof (scan_premise_frame rule (proj2 DOMAIN) PREMISE FRAME) as CHECKED_PREMISE.
    destruct TRANSPORTED as [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
    destruct entry as [ge locals le memory], checked as [current_ge current_locals current current_memory].
    destruct DOMAIN as [GE DOMAIN]; destruct FRAME as [CHECK_GE [CHECK_ENV [CHECK_MEMORY AGREE]]].
    cbn [entry_ge entry_env entry_memory entry_temps] in *; subst ge current_ge current_locals current_memory.
    unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_memory entry_temps] in RUN.
    rewrite TRACE, OUTCOME in RUN.
    destruct (scan_local rule SCOPE RUN CHECKED_PREMISE) as [after [final [EXEC [EXIT RESULT]]]].
    exists original; split; [|reflexivity].
    exists (FragmentObservation E0 after final Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split]].
    + eapply temp_agree_trans; eassumption.
    + eapply memory_equivalent_trans; eassumption.
  - intros entry checked original DOMAIN FRAME SOURCE.
    exists original; split; [eapply scan_source_transport; eassumption|reflexivity].
Defined.

Theorem scan_guarded_source_preservation entry original :
  scan_program_domain entry -> runs host source entry original ->
  runs host (select host (scan_condition rule) (scan_candidate rule) source) entry original.
Proof.
  intros DOMAIN SOURCE.
  destruct (@guardify_preservation _ host scan_program_domain (scan_premise rule)
    (private_scan_entry_frame (scan_ports rule)) (private_scan_entry_frame (scan_ports rule))
    eq source (scan_candidate rule) source (scan_condition rule)
    scan_program_guard_certificate scan_local_preservation_certificate entry original DOMAIN SOURCE)
    as [target [RUN SAME]]; subst target; exact RUN.
Qed.
End PRESERVATION.

Theorem private_scan_preserving_region_contract live source (rule : private_scan_preserving_rule live source) :
  PrivateRegion.projected_region_contract live source
    (select (private_scan_host (adapter_entry false) (scan_public_observe live))
      (scan_condition rule) (scan_candidate rule) source).
Proof.
  intros temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory source
    E0 after final Out_normal SOURCE live current (scan_writes rule) (scan_source_writes rule) SCOPE AGREE)
    as [middle [EXEC FRAME]].
  assert (DOMAIN : scan_program_domain rule p (Entry (globalenv p) locals current memory)).
  { split; [reflexivity|eapply scan_source_domain; exact EXEC]. }
  assert (ORIGINAL : runs (private_scan_host (adapter_entry temps) (scan_public_observe live)) source
    (Entry (globalenv p) locals current memory) (after,final)).
  { exists (FragmentObservation E0 middle final Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [exact FRAME|apply memory_equivalent_refl]]]. }
  destruct (@scan_guarded_source_preservation live source rule temps p SCOPE _ _ DOMAIN ORIGINAL)
    as [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
  unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_memory entry_temps] in RUN.
  rewrite TRACE, OUTCOME in RUN.
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ RUN fn continuation)
    as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists (fragment_temps raw),(fragment_memory raw); auto.
Qed.

Print Assumptions scan_program_guard_certificate.
Print Assumptions scan_source_transport.
Print Assumptions scan_local_preservation_certificate.
Print Assumptions scan_guarded_source_preservation.
Print Assumptions private_scan_preserving_region_contract.
