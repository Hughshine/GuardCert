(** Checked-state transport reads only store addresses and observer addresses.
    Source RHS values are not dependencies of the readonly probe. *)
From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint.
From GuardInterface Require Import ClightWordArithmeticTransport ClightWordCoordinateRename
  ClightDirectWordObservation ClightRenamedWordObservation ClightAffineJointObservation
  ClightStorePermissions ClightWordStoreSequence.
Import ListNotations.
Set Implicit Arguments.

Definition word_store_sequence_address_reads rename sites :=
  flat_map (fun site => wss_pointer site :: expression_temps (word_rename rename (wss_index site))) sites.
Definition word_store_sequence_probe_reads rename sites observers :=
  word_store_sequence_address_reads rename sites ++
  flat_map (fun observer => expression_temps (word_observer_address observer)) observers.

Lemma word_store_sequence_site_reads rename sites observers site identifier :
  In site sites -> In identifier (wss_pointer site :: expression_temps (word_rename rename (wss_index site))) ->
  In identifier (word_store_sequence_probe_reads rename sites observers).
Proof.
  intros SITE READ; apply in_or_app; left; apply in_flat_map; exists site; split; assumption.
Qed.

Lemma word_store_sequence_site_frame_checked rename site before first second live :
  word_arithmetic (wss_index site) -> word_store_site_frame rename site before first ->
  incl (wss_pointer site :: expression_temps (word_rename rename (wss_index site))) live ->
  temp_agree live first second -> word_store_site_frame rename site before second.
Proof.
  intros WORD [POINTER INDEX] SCOPE FRAME; split.
  - rewrite FRAME by (apply SCOPE; left; reflexivity); exact POINTER.
  - intros identifier MEMBER; rewrite FRAME.
    + apply INDEX; exact MEMBER.
    + apply SCOPE; right; rewrite word_rename_temps by exact WORD; apply in_map; exact MEMBER.
Qed.

Theorem word_store_sequence_checked_domain fe rename sites observers ge locals before current memory :
  Forall (fun site => word_arithmetic (wss_index site)) sites ->
  word_store_sequence_domain fe rename sites observers (Entry ge locals before memory) ->
  temp_agree (word_store_sequence_probe_reads rename sites observers) before current ->
  word_store_sequence_domain fe rename sites observers (Entry ge locals current memory).
Proof.
  intros WORDS [READS [source [source_memory [after [final [FRAMES [BACK SOURCE]]]]]]] FRAME.
  split.
  - apply Forall_forall; intros observer MEMBER.
    eapply word_observer_receipt_frame with (live:=word_store_sequence_probe_reads rename sites observers).
    + rewrite Forall_forall in READS; apply READS; exact MEMBER.
    + intros identifier READ; apply in_or_app; right; apply in_flat_map;
        exists observer; split; assumption.
    + exact FRAME.
  - exists source,source_memory,after,final; split; [|split; assumption].
    apply Forall_forall; intros site MEMBER; eapply word_store_sequence_site_frame_checked.
    + rewrite Forall_forall in WORDS; apply WORDS; exact MEMBER.
    + rewrite Forall_forall in FRAMES; apply FRAMES; exact MEMBER.
    + intros identifier READ; eapply word_store_sequence_site_reads; eassumption.
    + exact FRAME.
Qed.

Lemma word_store_sequence_checked_flag rename sites observers ge locals before current memory :
  Forall (fun site => word_arithmetic (wss_index site)) sites ->
  temp_agree (word_store_sequence_probe_reads rename sites observers) before current ->
  word_store_sequence_flag rename sites observers (Entry ge locals current memory) =
    word_store_sequence_flag rename sites observers (Entry ge locals before memory).
Proof.
  intros WORDS FRAME; revert FRAME; induction WORDS as [|site rest WORD WORDS IH]; intro FRAME;
    cbn [word_store_sequence_flag forallb]; [reflexivity|]; f_equal.
  - unfold word_store_site_flag,renamed_word_point_flag; cbn [entry_temps].
    rewrite word_address_evaluate_frame with (before:=before); [reflexivity| |].
    + apply word_rename_arithmetic; exact WORD.
    + intros identifier READ; apply FRAME; eapply word_store_sequence_site_reads;
        [left; reflexivity|exact READ].
  - apply IH; intros identifier READ; apply FRAME.
    unfold word_store_sequence_probe_reads,word_store_sequence_address_reads in READ |- *;
      cbn [flat_map List.In]; repeat rewrite in_app_iff in READ; repeat rewrite in_app_iff; tauto.
Qed.

Theorem word_store_sequence_runtime_check fe rename sites observers ge locals before current memory flag :
  Forall (fun site => word_arithmetic (wss_index site)) sites ->
  word_store_sequence_domain fe rename sites observers (Entry ge locals before memory) ->
  temp_agree (word_store_sequence_probe_reads rename sites observers) before current ->
  exec_stmt fe ge locals current memory (word_store_sequence_check_code rename sites observers flag) E0
    (PTree.set flag (Vint (if word_store_sequence_flag rename sites observers (Entry ge locals before memory)
      then Int.one else Int.zero)) current) memory Out_normal.
Proof.
  intros WORDS DOMAIN FRAME.
  pose proof (@word_store_sequence_check_execution fe rename sites observers
    (Entry ge locals current memory) flag WORDS
    (word_store_sequence_checked_domain WORDS DOMAIN FRAME)) as RUN.
  rewrite (@word_store_sequence_checked_flag rename sites observers ge locals before current memory WORDS FRAME)
    in RUN; exact RUN.
Qed.

Print Assumptions word_store_sequence_site_reads.
Print Assumptions word_store_sequence_site_frame_checked.
Print Assumptions word_store_sequence_checked_domain.
Print Assumptions word_store_sequence_checked_flag.
Print Assumptions word_store_sequence_runtime_check.
