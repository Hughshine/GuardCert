From Stdlib Require Import List.
From compcert.common Require Import AST Events Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardInterface Require Import ClightSourceObservation ClightPrivateScan ClightSourcePrefixReplay.
Import ListNotations.
Set Implicit Arguments.

Lemma source_prefix_region_execution loads source suffix fe ge locals entry memory after final :
  exec_stmt fe ge locals entry memory
    (Ssequence (Ssequence (source_load_prefix loads) source) suffix) E0 after final Out_normal ->
  exists middle body_after body_memory,
    exec_stmt fe ge locals entry memory (source_load_prefix loads) E0 middle memory Out_normal /\
    exec_stmt fe ge locals middle memory source E0 body_after body_memory Out_normal /\
    exec_stmt fe ge locals body_after body_memory suffix E0 after final Out_normal.
Proof.
  intro SOURCE; inversion SOURCE; subst; [|contradiction].
  match goal with EMPTY : _ ** _ = E0 |- _ =>
    apply Eapp_E0_inv in EMPTY as [LEFT RIGHT]; subst end.
  match goal with BODY : exec_stmt _ _ _ _ _ (Ssequence _ source) _ _ _ _ |- _ =>
    inversion BODY; subst end; [|contradiction].
  match goal with EMPTY : _ ** _ = E0 |- _ =>
    apply Eapp_E0_inv in EMPTY as [LEFT RIGHT]; subst end.
  match goal with PREFIX : exec_stmt _ _ _ _ _ (source_load_prefix loads) _ _ _ _ |- _ =>
    destruct (@private_scan_completed_shape _ _ _ _ _ _ _ _ _ _ PREFIX
      (source_load_prefix_supported loads)) as [_ [SAME _]]; subst end.
  do 3 eexists; repeat split; eassumption.
Qed.

Theorem source_prefix_region_replay loads source suffix fe ge locals entry memory middle
    body_after body_memory after final :
  (forall id, In id (source_load_targets loads) -> ~ In id (source_load_pointers loads)) ->
  exec_stmt fe ge locals entry memory (source_load_prefix loads) E0 middle memory Out_normal ->
  exec_stmt fe ge locals middle memory source E0 body_after body_memory Out_normal ->
  exec_stmt fe ge locals body_after body_memory suffix E0 after final Out_normal ->
  exec_stmt fe ge locals middle memory
    (Ssequence (Ssequence (source_load_prefix loads) source) suffix) E0 after final Out_normal.
Proof.
  intros FRESH PREFIX BODY SUFFIX.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [|exact SUFFIX].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [|exact BODY].
  eapply source_prefix_replay; eassumption.
Qed.

Print Assumptions source_prefix_region_execution.
Print Assumptions source_prefix_region_replay.
