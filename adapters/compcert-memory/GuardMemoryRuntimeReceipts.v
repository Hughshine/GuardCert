From Stdlib Require Import List ZArith.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions CompCertStoreSchedule.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryLoopTrace GuardMemoryFiniteFootprint.
From GuardInterface Require Import ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.

Definition memory_cell_access (locations : cell_locations) memory cell permission := exists location,
  locations cell = Some location /\
  Mem.valid_access memory (location_chunk location) (location_block location) (location_offset location) permission.
Definition memory_event_access_receipt locations memory event :=
  memory_cell_access locations memory (exact_cell (instruction_write (event_instruction event)) (event_arguments event)) Writable /\
  Forall (fun cell => memory_cell_access locations memory cell Readable)
    (map (fun access => exact_cell access (event_arguments event)) (instruction_reads (event_instruction event))).

Lemma memory_cell_access_back locations before after cell permission :
  memory_accesses_back before after -> memory_cell_access locations after cell permission ->
  memory_cell_access locations before cell permission.
Proof.
  intros BACK [location [RESOLVE ACCESS]]; exists location; split; [exact RESOLVE|apply BACK; exact ACCESS].
Qed.
Lemma memory_cell_access_readable locations memory cell :
  memory_cell_access locations memory cell Writable -> memory_cell_access locations memory cell Readable.
Proof.
  intros [location [RESOLVE ACCESS]]; exists location; split; [exact RESOLVE|].
  eapply Mem.valid_access_implies; [exact ACCESS|constructor].
Qed.
Lemma memory_event_access_receipt_back locations before after event :
  memory_accesses_back before after -> memory_event_access_receipt locations after event ->
  memory_event_access_receipt locations before event.
Proof.
  intros BACK [WRITE READS]; split; [eapply memory_cell_access_back; eassumption|].
  eapply Forall_impl; [|exact READS]; intros cell ACCESS; eapply memory_cell_access_back; eassumption.
Qed.

Lemma memory_resolved_reads_access locations cells memory resolved loaded :
  resolve_cells cells locations = Some resolved -> load_locations resolved memory = Some loaded ->
  Forall (fun cell => memory_cell_access locations memory cell Readable) cells.
Proof.
  revert resolved loaded; induction cells as [|cell cells IH]; intros resolved loaded RESOLVE LOADS; [constructor|].
  cbn [resolve_cells] in RESOLVE; destruct (locations cell) as [location|] eqn:LOCATION; [|discriminate].
  destruct (resolve_cells cells locations) as [tail|] eqn:TAIL; [|discriminate].
  inversion RESOLVE; subst resolved; cbn [load_locations] in LOADS.
  destruct (location_load location memory) as [value|] eqn:READ; [|discriminate].
  destruct (load_locations tail memory) as [values|] eqn:REST; [|discriminate].
  constructor.
  - exists location; split; [exact LOCATION|eapply Mem.load_valid_access; exact READ].
  - eapply IH; [reflexivity|exact REST].
Qed.

(** Actual instruction steps are concrete stores. They preserve permissions,
    including for cells whose values they initialize or overwrite. *)
Lemma memory_receipt_event_locations event before after :
  memory_event_step event before after -> runtime_locations after = runtime_locations before.
Proof.
  intros [writes [reads [_ [_ [write [resolved [_ [_ [FRAME ACTION]]]]]]]]]; exact FRAME.
Qed.
Lemma memory_receipt_event_accesses_back event before after :
  memory_event_step event before after -> memory_accesses_back (runtime_memory before) (runtime_memory after).
Proof.
  intros [writes [reads [_ [_ [write [resolved [_ [_ [_ [loaded [value [_ [_ STORE]]]]]]]]]]]]].
  eapply store_memory_accesses_back; exact STORE.
Qed.
Lemma memory_event_current_access_receipt event before after :
  memory_event_step event before after ->
  memory_event_access_receipt (runtime_locations before) (runtime_memory before) event.
Proof.
  intros [writes [reads [WRITES [READS [write [resolved [LOCATION [RESOLVE [_ [loaded [value [LOADS [_ STORE]]]]]]]]]]]]].
  subst reads; split.
  - exists write; split; [exact LOCATION|eapply Mem.store_valid_access_3; exact STORE].
  - eapply memory_resolved_reads_access; eassumption.
Qed.

Theorem memory_trace_accesses_back events before after :
  Iter.iter_semantics memory_event_step events before after ->
  memory_accesses_back (runtime_memory before) (runtime_memory after).
Proof.
  intro RUN; induction RUN; [apply memory_accesses_back_refl|].
  eapply memory_accesses_back_trans; [eapply memory_receipt_event_accesses_back; exact H|exact IHRUN].
Qed.

(** All source trace events supply permissions at the original entry. This
    theorem makes no statement about entry loaded values or RHS definedness. *)
Theorem memory_trace_entry_access_receipts events before after :
  Iter.iter_semantics memory_event_step events before after ->
  Forall (memory_event_access_receipt (runtime_locations before) (runtime_memory before)) events.
Proof.
  intro RUN; induction RUN; [constructor|].
  constructor; [eapply memory_event_current_access_receipt; exact H|].
  pose proof (@memory_receipt_event_locations _ _ _ H) as FRAME.
  rewrite FRAME in IHRUN; eapply Forall_impl; [|exact IHRUN].
  intros event RECEIPT; eapply memory_event_access_receipt_back;
    [eapply memory_receipt_event_accesses_back; exact H|exact RECEIPT].
Qed.

Theorem memory_loop_entry_access_receipts loop parameters before after :
  L.loop_semantics loop parameters before after ->
  Forall (memory_event_access_receipt (runtime_locations before) (runtime_memory before)) (memory_loop_trace loop parameters).
Proof.
  intro RUN; apply memory_loop_trace_correct in RUN; eapply memory_trace_entry_access_receipts; exact RUN.
Qed.

Lemma memory_receipts_footprint_readable locations memory events :
  Forall (memory_event_access_receipt locations memory) events ->
  Forall (fun cell => memory_cell_access locations memory cell Readable) (memory_events_footprint events).
Proof.
  intro RECEIPTS; apply Forall_forall; intros cell MEMBER; apply in_flat_map in MEMBER as [event [EVENT MEMBER]].
  apply Forall_forall with (x := event) in RECEIPTS; [|exact EVENT].
  destruct RECEIPTS as [WRITE READS]; destruct MEMBER as [SAME|READ].
  - subst cell; apply memory_cell_access_readable; exact WRITE.
  - apply Forall_forall with (x := cell) in READS; assumption.
Qed.

Theorem memory_loop_entry_footprint_readable loop parameters before after :
  L.loop_semantics loop parameters before after ->
  Forall (fun cell => memory_cell_access (runtime_locations before) (runtime_memory before) cell Readable)
    (memory_events_footprint (memory_loop_trace loop parameters)).
Proof.
  intro RUN; apply memory_receipts_footprint_readable; eapply memory_loop_entry_access_receipts; exact RUN.
Qed.

Print Assumptions memory_cell_access_back.
Print Assumptions memory_cell_access_readable.
Print Assumptions memory_event_access_receipt_back.
Print Assumptions memory_resolved_reads_access.
Print Assumptions memory_receipt_event_locations.
Print Assumptions memory_receipt_event_accesses_back.
Print Assumptions memory_event_current_access_receipt.
Print Assumptions memory_trace_accesses_back.
Print Assumptions memory_trace_entry_access_receipts.
Print Assumptions memory_loop_entry_access_receipts.
Print Assumptions memory_receipts_footprint_readable.
Print Assumptions memory_loop_entry_footprint_readable.
