From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightTempFrame ClightTempFootprint
  ClightPrivateRegion CompCertMemoryEquivalence.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyPreservation ClightReadonlyProjectedCompiler ClightGuardRealization.
Set Implicit Arguments.

(** A language adapter for normal public exits. It turns an existing one-way
    local execution certificate into the kernel's preservation certificate;
    the program host still owns scope, progress and installation. *)
Definition readonly_normal_public_observe live(raw:fragment_observation)(observed:temp_env*mem) :=
  fragment_trace raw=E0 /\ fragment_outcome raw=Out_normal /\
  temp_agree live(fst observed)(fragment_temps raw) /\
  memory_equivalent(snd observed)(fragment_memory raw).

Section KERNEL.
Variable live : list ident.
Variable source : statement.
Variable rule : readonly_preserving_clight_rule live source.
Variable temps : bool.
Variable p : Clight.program.
Hypothesis SCOPE : statement_scope live source.
Let host:=readonly_clight_host(adapter_entry temps)(readonly_normal_public_observe live).
Definition readonly_preservation_domain entry := entry_ge entry=Clight.globalenv p /\ preserving_domain rule entry.

Definition readonly_preservation_condition : readonly_condition host readonly_preservation_domain
  (preserving_premise rule)(preserving_guard rule).
Proof.
  constructor.
  - intros entry [_ DOMAIN]; exact(readonly_safe(preserving_check rule temps)entry DOMAIN).
  - intros entry [_ DOMAIN]; exact(readonly_available(preserving_check rule temps)entry DOMAIN).
  - intros entry accepted checked [_ DOMAIN] RUN; exact(readonly_sound(preserving_check rule temps)entry accepted checked DOMAIN RUN).
Defined.

Definition readonly_local_preservation_certificate : preservation_certificate host readonly_preservation_domain
  (preserving_premise rule)eq eq eq source(preserving_candidate rule)source.
Proof.
  constructor.
  - intros entry checked original [GE DOMAIN] PREMISE SAME [raw [RUN [TRACE [NORMAL [PUBLIC MEMORY]]]]]; subst checked.
    destruct entry as [ge locals le memory]; cbn [entry_ge entry_env entry_temps entry_memory] in *; subst ge.
    unfold clight_fragment_run in RUN; cbn [entry_ge entry_env entry_temps entry_memory] in RUN.
    rewrite TRACE,NORMAL in RUN.
    destruct(preserving_local rule SCOPE RUN DOMAIN PREMISE)as [after [final [TARGET [EXIT RESULT]]]].
    exists original; split; [|reflexivity].
    exists(FragmentObservation E0 after final Out_normal); split; [exact TARGET|].
    split; [reflexivity|split; [reflexivity|split]].
    + eapply temp_agree_trans; [exact PUBLIC|exact EXIT].
    + eapply memory_equivalent_trans; [exact MEMORY|exact RESULT].
  - intros entry checked original DOMAIN SAME RUN; subst checked; exists original; split; [exact RUN|reflexivity].
Defined.

Theorem readonly_kernel_guarded_preservation entry original : readonly_preservation_domain entry ->
  runs host source entry original ->
  runs host(select host(preserving_guard rule)(preserving_candidate rule)source)entry original.
Proof.
  intros DOMAIN RUN.
  destruct(@guardify_preservation _ host readonly_preservation_domain(preserving_premise rule)eq eq eq
    source(preserving_candidate rule)source(preserving_guard rule)
    (readonly_guard_certificate readonly_preservation_condition)readonly_local_preservation_certificate
    entry original DOMAIN RUN)as [target [TARGET SAME]]; subst target; exact TARGET.
Qed.
End KERNEL.

Theorem readonly_kernel_selected_execution live source(rule:readonly_preserving_clight_rule live source)
    temps p locals le memory after final :
  statement_scope live source ->
  exec_stmt(adapter_entry temps)(Clight.globalenv p)locals le memory source E0 after final Out_normal ->
  projected_selected_execution live(preserving_guard rule)(preserving_candidate rule)source
    temps p locals le memory after final.
Proof.
  intros SCOPE SOURCE.
  assert(DOMAIN:readonly_preservation_domain rule p(Entry(Clight.globalenv p)locals le memory)).
  { split; [reflexivity|eapply preserving_entry; exact SOURCE]. }
  assert(VISIBLE:runs(readonly_clight_host(adapter_entry temps)(readonly_normal_public_observe live))
    source(Entry(Clight.globalenv p)locals le memory)(after,final)).
  { exists(FragmentObservation E0 after final Out_normal); split; [exact SOURCE|].
    split; [reflexivity|split; [reflexivity|split; [apply temp_agree_refl|apply memory_equivalent_refl]]]. }
  destruct(@readonly_kernel_guarded_preservation live source rule temps p SCOPE _ _ DOMAIN VISIBLE)
    as [raw [RUN [TRACE [NORMAL [PUBLIC MEMORY]]]]].
  apply readonly_tree_execution_exact in RUN as [accepted [CHECK RUN]].
  exists accepted,(fragment_temps raw),(fragment_memory raw); split; [exact CHECK|split; [|split; assumption]].
  unfold clight_fragment_run in RUN; rewrite TRACE,NORMAL in RUN; exact RUN.
Qed.

Theorem readonly_kernel_realized_region_contract live source(rule:readonly_preserving_clight_rule live source)
    (R:clight_normal_realization live(preserving_guard rule)(preserving_candidate rule)source) :
  PrivateRegion.projected_region_contract live source(realization_code(normal_realization R)).
Proof.
  eapply realized_projected_selection_contract; [exact(preserving_source_writes rule)|].
  intros; apply readonly_kernel_selected_execution; assumption.
Qed.
Print Assumptions readonly_preservation_condition.
Print Assumptions readonly_local_preservation_certificate.
Print Assumptions readonly_kernel_guarded_preservation.
Print Assumptions readonly_kernel_selected_execution.
Print Assumptions readonly_kernel_realized_region_contract.
