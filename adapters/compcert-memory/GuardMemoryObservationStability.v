From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryFootprintCapabilities GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryBufferOffsets
  GuardMemoryMultiPointerCompute GuardMemoryMultiPointerSequence.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** An external observation is separated from writes, not from all reads.
    No property of the observed value, or its stability, is assumed here. *)
Definition memory_event_write event := exact_cell (instruction_write (event_instruction event)) (event_arguments event).
Definition memory_writes_apart_observation locations events observation :=
  forall event, In event events -> forall write,
    locations (memory_event_write event) = Some write -> location_disjoint write observation.

Lemma memory_event_observation_preserved event before after observation :
  (forall write, runtime_locations before (memory_event_write event) = Some write ->
    location_disjoint write observation) ->
  memory_event_step event before after ->
  location_load observation (runtime_memory after) = location_load observation (runtime_memory before).
Proof.
  intros APART [writes [reads [WRITES [READS STEP]]]].
  destruct STEP as [write [resolved [WRITE [RESOLVE [FRAME ACTION]]]]].
  destruct ACTION as [loaded [value [LOAD [COMPUTE STORE]]]].
  eapply location_load_store_other; [exact STORE|apply APART; exact WRITE].
Qed.
Theorem memory_trace_observation_preserved locations events observation before after :
  runtime_locations before = locations ->
  memory_writes_apart_observation locations events observation ->
  Iter.iter_semantics memory_event_step events before after ->
  location_load observation (runtime_memory after) = location_load observation (runtime_memory before).
Proof.
  intros LOCATION APART RUN; revert LOCATION APART; induction RUN; intros LOCATION APART.
  - reflexivity.
  - rewrite IHRUN.
    + eapply memory_event_observation_preserved; [|exact H].
      intros write WRITE; rewrite LOCATION in WRITE; apply APART with (event:=x); [cbn; auto|exact WRITE].
    + rewrite (memory_event_locations_preserved H); exact LOCATION.
    + intros event MEMBER; apply APART; cbn; auto.
Qed.
Theorem memory_loop_observation_preserved loop parameters locations before after observation :
  memory_writes_apart_observation locations (memory_loop_trace loop parameters) observation ->
  L.loop_semantics loop parameters (RuntimeState locations before) (RuntimeState locations after) ->
  location_load observation after = location_load observation before.
Proof.
  intros APART RUN; apply memory_loop_trace_correct in RUN.
  exact (@memory_trace_observation_preserved locations (memory_loop_trace loop parameters) observation
    (RuntimeState locations before) (RuntimeState locations after) eq_refl APART RUN).
Qed.

(** Actual pointer-body adapter. A domain condition supplies these byte
    separations at reached coordinates; the language store law supplies load
    preservation for the decoded physical sequence, including aliasing reads. *)
Definition memory_pointer_writes_apart_observation temps values operations observation :=
  forall operation, In operation operations -> forall block base,
    temps ! (memory_nary_access_array (memory_nary_compute_write operation)) = Some (Vptr block base) ->
    location_disjoint (MemoryLocation Mint32 block (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values))) observation.
Lemma memory_pointer_operation_observation_preserved temps values operation observation before after :
  memory_pointer_writes_apart_observation temps values [operation] observation ->
  memory_multi_pointer_compute_physical temps values operation before after ->
  location_load observation after = location_load observation before.
Proof.
  intros APART [block [base [loaded [value [POINTER [LOAD [COMPUTE STORE]]]]]]].
  eapply (@location_load_store_other (MemoryLocation Mint32 block (memory_pointer_buffer_offset base
    (memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values)))
    value before after observation); [exact STORE|apply APART with (operation:=operation); [cbn; auto|exact POINTER]].
Qed.
Theorem memory_pointer_sequence_observation_preserved temps values operations observation before after :
  memory_pointer_writes_apart_observation temps values operations observation ->
  memory_multi_pointer_sequence_physical temps values operations before after ->
  location_load observation after = location_load observation before.
Proof.
  intros APART RUN; induction RUN.
  - reflexivity.
  - rewrite IHRUN.
    + eapply memory_pointer_operation_observation_preserved; [|exact H].
      intros item MEMBER; cbn in MEMBER; destruct MEMBER as [<-|[]]; apply APART; cbn; auto.
    + intros item MEMBER; apply APART; cbn; auto.
Qed.

Print Assumptions memory_event_observation_preserved.
Print Assumptions memory_trace_observation_preserved.
Print Assumptions memory_loop_observation_preserved.
Print Assumptions memory_pointer_operation_observation_preserved.
Print Assumptions memory_pointer_sequence_observation_preserved.
