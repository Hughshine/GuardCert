From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightPrivateRegion
  ClightTempFrame ClightTempFootprint ClightProjectedExecution
  ClightRegionProgress CompCertMemoryEquivalence.
Import ListNotations.
Set Implicit Arguments.

(** A language-level alternative above the local semantic kernel. On acceptance,
    the new branch reproduces the source's public exit. On refusal, the producer
    supplies a source entry related to the checked state, so an existing projected
    contract can be reused even when the prelude changed private temporaries or
    repeated a source read prefix. The original source execution is proof input;
    it is not a runtime pre-execution. *)
Definition projected_dispatch_prelude live source prelude test fast : Prop :=
  forall temps p locals entry memory after final,
  exec_stmt (adapter_entry temps) (globalenv p) locals entry memory source E0
    after final Out_normal ->
  exists checked answer,
    exec_stmt (adapter_entry temps) (globalenv p) locals entry memory prelude E0
      checked memory Out_normal /\
    expression_test test (Entry (globalenv p) locals checked memory) answer /\
    if answer then
      exists exit, exec_stmt (adapter_entry temps) (globalenv p) locals checked memory
        fast E0 exit final Out_normal /\ temp_agree live after exit
    else
      exists replay, temp_agree live replay checked /\
        exec_stmt (adapter_entry temps) (globalenv p) locals replay memory source E0
          after final Out_normal.

Definition projected_runtime_dispatch prelude test fast previous :=
  Ssequence prelude (Sifthenelse test fast previous).

(** The previous target is opaque: its certificate gives small-step execution,
    not necessarily a big-step execution or a frameable AST. Source progress,
    placement and private-resource checks remain installation obligations. *)
Theorem projected_runtime_dispatch_contract live source prelude test fast previous :
  writes_only (statement_temps source) source ->
  projected_dispatch_prelude live source prelude test fast ->
  PrivateRegion.projected_region_contract live source previous ->
  PrivateRegion.projected_region_contract live source
    (projected_runtime_dispatch prelude test fast previous).
Proof.
  intros WRITES PRELUDE PREVIOUS temps p locals entry current memory after final
    SCOPE AGREE SOURCE fn continuation.
  destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p)
    locals entry memory source E0 after final Out_normal SOURCE live current
    (statement_temps source) WRITES SCOPE AGREE) as [public_after [ACTUAL PUBLIC]].
  destruct (PRELUDE temps p locals current memory public_after final ACTUAL)
    as [checked [answer [PREPARE [TEST BRANCH]]]].
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ PREPARE fn
    (Kseq (Sifthenelse test fast previous) continuation))
    as [finish [PREPARE_STEPS FINISH]]; inversion FINISH; subst finish.
  assert (CHOSEN : exists exit target_memory,
    star (adapter_step temps) (globalenv p)
      (State fn (if answer then fast else previous) continuation locals checked memory)
      E0 (State fn Sskip continuation locals exit target_memory) /\
    temp_agree live public_after exit /\ memory_equivalent final target_memory).
  { destruct answer.
    - destruct BRANCH as [exit [EXECUTE FRAME]].
      destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ EXECUTE fn continuation)
        as [finish [STEPS DONE]]; inversion DONE; subst finish.
      exists exit,final; split; [exact STEPS|split; [exact FRAME|apply memory_equivalent_refl]].
    - destruct BRANCH as [replay [FRAME REPLAY]].
      exact (PREVIOUS temps p locals replay checked memory public_after final SCOPE FRAME
        REPLAY fn continuation). }
  destruct CHOSEN as [exit [target_memory [STEPS [EXIT MEMORY]]]].
  exists exit,target_memory; split; [|split; [eapply temp_agree_trans; eassumption|exact MEMORY]].
  unfold projected_runtime_dispatch.
  eapply star_left with (t1:=E0) (t2:=E0).
  - unfold adapter_step; apply step_seq.
  - eapply star_trans with (t1:=E0) (t2:=E0); [exact PREPARE_STEPS| |reflexivity].
    eapply star_left with (t1:=E0) (t2:=E0).
    + unfold adapter_step; apply step_skip_seq.
    + destruct TEST as [value [EVAL BOOL]].
      eapply star_left with (t1:=E0) (t2:=E0).
      * unfold adapter_step; eapply step_ifthenelse; [exact EVAL|exact BOOL].
      * exact STEPS.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Print Assumptions projected_runtime_dispatch_contract.
