From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightPrivateRegion ClightTempFrame
  ClightTempFootprint ClightProjectedExecution CompCertMemoryEquivalence.
From GuardInterface Require Import GuardInterface ClightReadonlyRewrite ClightMaterializedCheck
  ClightPrivateScanHost ClightPrivateScanPreservation.
Set Implicit Arguments.

(** The premise stays at the original entry. The local theorem explicitly
    transports to the checked entry; no premise-stability law is required. *)
Record materialized_preserving_rule (live : list ident) (source : statement) := {
  materialized_candidate : statement;
  materialized_test : materialized_check;
  materialized_domain : clight_entry -> Prop;
  materialized_premise : clight_entry -> Prop;
  materialized_ports : list ident;
  materialized_ports_live : incl live materialized_ports;
  materialized_writes : list ident;
  materialized_source_writes : writes_only materialized_writes source;
  materialized_certificate : forall temps,
    guard_certificate (materialized_host (adapter_entry temps) (scan_public_observe live))
      materialized_domain materialized_premise
      (private_scan_entry_frame materialized_ports) (private_scan_entry_frame materialized_ports) materialized_test;
  materialized_local : forall temps p locals le memory current after final,
    statement_scope live source ->
    exec_stmt (adapter_entry temps) (globalenv p) locals le memory source E0 after final Out_normal ->
    materialized_premise (Entry (globalenv p) locals le memory) ->
    temp_agree materialized_ports le current ->
    exists exit result,
      exec_stmt (adapter_entry temps) (globalenv p) locals current memory materialized_candidate
        E0 exit result Out_normal /\ temp_agree live after exit /\ memory_equivalent final result;
  materialized_source_domain : forall temps p locals le memory after final,
    exec_stmt (adapter_entry temps) (globalenv p) locals le memory source E0 after final Out_normal ->
    materialized_domain (Entry (globalenv p) locals le memory)
}.

Section PRESERVATION.
Variable live : list ident.
Variable source : statement.
Variable rule : materialized_preserving_rule live source.
Variable temps : bool.
Variable p : Clight.program.
Hypothesis SCOPE : statement_scope live source.
Let host := materialized_host (adapter_entry temps) (scan_public_observe live).
Definition materialized_program_domain entry := entry_ge entry=globalenv p /\ materialized_domain rule entry.

Definition materialized_program_certificate :
  guard_certificate host materialized_program_domain (materialized_premise rule)
    (private_scan_entry_frame (materialized_ports rule)) (private_scan_entry_frame (materialized_ports rule)) (materialized_test rule).
Proof.
  constructor.
  - intros entry [_ DOMAIN]; exact (check_safety (materialized_certificate rule temps) entry DOMAIN).
  - intros entry [_ DOMAIN]; exact (check_available (materialized_certificate rule temps) entry DOMAIN).
  - intros entry accepted checked [_ DOMAIN] CHECK.
    exact (check_sound (materialized_certificate rule temps) entry accepted checked DOMAIN CHECK).
Defined.

Definition materialized_local_certificate :
  preservation_certificate host materialized_program_domain (materialized_premise rule)
    (private_scan_entry_frame (materialized_ports rule)) (private_scan_entry_frame (materialized_ports rule))
    eq source (materialized_candidate rule) source.
Proof.
  constructor.
  - intros entry checked original [GE DOMAIN] PREMISE FRAME [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
    destruct entry as [ge locals le memory],checked as [current_ge current_locals current current_memory].
    destruct FRAME as [CHECK_GE [CHECK_ENV [CHECK_MEMORY AGREE]]].
    cbn [entry_ge entry_env entry_memory entry_temps] in *; subst ge current_ge current_locals current_memory.
    unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_memory entry_temps] in RUN.
    rewrite TRACE,OUTCOME in RUN.
    destruct (materialized_local rule SCOPE RUN PREMISE AGREE) as [after [final [EXEC [EXIT RESULT]]]].
    exists original; split; [|reflexivity].
    exists (FragmentObservation E0 after final Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split]].
    + eapply temp_agree_trans; eassumption.
    + eapply memory_equivalent_trans; eassumption.
  - intros entry checked original [GE DOMAIN] [CHECK_GE [CHECK_ENV [CHECK_MEMORY AGREE]]]
      [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
    destruct entry as [ge locals le memory],checked as [current_ge current_locals current current_memory].
    cbn [entry_ge entry_env entry_memory entry_temps] in *; subst ge current_ge current_locals current_memory.
    unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_memory entry_temps] in RUN.
    rewrite TRACE,OUTCOME in RUN.
    destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory source
      E0 (fragment_temps raw) (fragment_memory raw) Out_normal RUN live current
      (materialized_writes rule) (materialized_source_writes rule) SCOPE
      (@temp_agree_weaken live (materialized_ports rule) _ _ (materialized_ports_live rule) AGREE))
      as [after [EXEC EXIT]].
    exists original; split; [|reflexivity].
    exists (FragmentObservation E0 after (fragment_memory raw) Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [eapply temp_agree_trans; eassumption|exact MEMORY]]].
Defined.

Theorem materialized_guarded_preservation entry original :
  materialized_program_domain entry -> runs host source entry original ->
  runs host (select host (materialized_test rule) (materialized_candidate rule) source) entry original.
Proof.
  intros DOMAIN SOURCE.
  destruct (@guardify_preservation _ host materialized_program_domain (materialized_premise rule)
    (private_scan_entry_frame (materialized_ports rule)) (private_scan_entry_frame (materialized_ports rule))
    eq source (materialized_candidate rule) source (materialized_test rule)
    materialized_program_certificate materialized_local_certificate entry original DOMAIN SOURCE)
    as [target [RUN SAME]]; subst target; exact RUN.
Qed.
End PRESERVATION.

Theorem materialized_preserving_region_contract live source (rule : materialized_preserving_rule live source) :
  PrivateRegion.projected_region_contract live source
    (materialized_select (materialized_test rule) (materialized_candidate rule) source).
Proof.
  intros temps p locals le current memory after final SCOPE AGREE SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals le memory source
    E0 after final Out_normal SOURCE live current (materialized_writes rule) (materialized_source_writes rule) SCOPE AGREE)
    as [middle [EXEC FRAME]].
  assert (DOMAIN : materialized_program_domain rule p (Entry (globalenv p) locals current memory)).
  { split; [reflexivity|eapply materialized_source_domain; exact EXEC]. }
  assert (ORIGINAL : runs (materialized_host (adapter_entry temps) (scan_public_observe live)) source
    (Entry (globalenv p) locals current memory) (after,final)).
  { exists (FragmentObservation E0 middle final Out_normal); split; [exact EXEC|].
    split; [reflexivity|split; [reflexivity|split; [exact FRAME|apply memory_equivalent_refl]]]. }
  destruct (@materialized_guarded_preservation live source rule temps p SCOPE _ _ DOMAIN ORIGINAL)
    as [raw [RUN [TRACE [OUTCOME [PUBLIC MEMORY]]]]].
  unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_memory entry_temps] in RUN.
  rewrite TRACE,OUTCOME in RUN.
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ RUN fn continuation) as [finish [STEPS EXIT]].
  inversion EXIT; subst finish; exists (fragment_temps raw),(fragment_memory raw); auto.
Qed.

Print Assumptions materialized_program_certificate.
Print Assumptions materialized_local_certificate.
Print Assumptions materialized_guarded_preservation.
Print Assumptions materialized_preserving_region_contract.
