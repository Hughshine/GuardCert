From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryLoopTrace GuardMemoryNamedRegistrySource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Source execution supplies permission only for actual access cells. These
    facts are transported back to the guard entry through stores; no guessed
    allocation length is used. *)
Definition memory_locations_int32 (locations : cell_locations) := forall cell location,
  locations cell = Some location -> location_chunk location = Mint32.
Definition memory_cell_capable (locations : cell_locations) memory cell := exists location,
  locations cell = Some location /\ location_chunk location = Mint32 /\
  Mem.valid_pointer memory (location_block location) (location_offset location) = true /\
  (4 | location_offset location).
Definition memory_event_cells event :=
  exact_cell (instruction_write (event_instruction event)) (event_arguments event) ::
  map (fun access => exact_cell access (event_arguments event))
    (instruction_reads (event_instruction event)).
Lemma memory_int32_load_capable location memory value :
  location_chunk location = Mint32 -> location_load location memory = Some value ->
  Mem.valid_pointer memory (location_block location) (location_offset location) = true /\
  (4 | location_offset location).
Proof.
  intros CHUNK LOAD; unfold location_load in LOAD; rewrite CHUNK in LOAD.
  pose proof (Mem.load_valid_access _ _ _ _ _ LOAD) as [PERMISSION ALIGNMENT].
  split; [|exact ALIGNMENT].
  apply Mem.valid_pointer_nonempty_perm; eapply Mem.perm_implies;
    [apply PERMISSION; change (location_offset location <= location_offset location < location_offset location+4); lia|constructor].
Qed.
Lemma memory_resolved_loaded_cell cells locations resolved memory loaded cell :
  resolve_cells cells locations = Some resolved -> load_locations resolved memory = Some loaded ->
  In cell cells -> exists location value,
    locations cell = Some location /\ location_load location memory = Some value.
Proof.
  revert resolved loaded; induction cells as [|head tail IH]; intros resolved loaded RESOLVE LOAD MEMBER;
    [contradiction|].
  cbn [resolve_cells] in RESOLVE; destruct (locations head) as [location|] eqn:HEAD; [|discriminate].
  destruct (resolve_cells tail locations) as [rest|] eqn:TAIL; [|discriminate].
  inversion RESOLVE; subst resolved; cbn [load_locations] in LOAD.
  destruct (location_load location memory) as [value|] eqn:VALUE; [|discriminate].
  destruct (load_locations rest memory) as [values|] eqn:VALUES; [|discriminate].
  destruct MEMBER as [SAME|MEMBER]; [subst cell; exists location,value; auto|].
  exact (IH rest values eq_refl VALUES MEMBER).
Qed.
Lemma memory_event_locations_preserved event before after :
  memory_event_step event before after -> runtime_locations after = runtime_locations before.
Proof. intros [writes [reads [_ [_ [write [loaded [_ [_ [FRAME RUN]]]]]]]]]; exact FRAME. Qed.
Lemma memory_event_valid_pointer_preserved event before after block offset :
  memory_event_step event before after ->
  (Mem.valid_pointer (runtime_memory before) block offset = true <->
   Mem.valid_pointer (runtime_memory after) block offset = true).
Proof.
  intros [writes [reads [_ [_ [write [loaded [_ [_ [_ [values [value [LOAD [COMPUTE STORE]]]]]]]]]]]]].
  eapply memory_store_valid_pointer; exact STORE.
Qed.
Theorem memory_event_access_capabilities event before after :
  memory_locations_int32 (runtime_locations before) -> memory_event_step event before after ->
  Forall (memory_cell_capable (runtime_locations before) (runtime_memory before)) (memory_event_cells event).
Proof.
  intros INT32 [writes [reads [WRITES [READS [write [resolved [WRITE [RESOLVE [FRAME [loaded [value [LOAD [COMPUTE STORE]]]]]]]]]]]]].
  subst writes reads; unfold memory_event_cells; constructor.
  - exists write; split; [exact WRITE|].
    assert (CHUNK : location_chunk write = Mint32) by (eapply INT32; exact WRITE).
    split; [exact CHUNK|].
    change (Mem.store (location_chunk write) (runtime_memory before) (location_block write)
      (location_offset write) value = Some (runtime_memory after)) in STORE.
    rewrite CHUNK in STORE; pose proof (Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as [PERMISSION ALIGNMENT].
    split; [|exact ALIGNMENT].
    apply Mem.valid_pointer_nonempty_perm; eapply Mem.perm_implies;
      [apply PERMISSION; change (location_offset write <= location_offset write < location_offset write+4); lia|constructor].
  - apply Forall_forall; intros cell MEMBER.
    destruct (@memory_resolved_loaded_cell _ (runtime_locations before) resolved (runtime_memory before)
      loaded cell RESOLVE LOAD MEMBER) as [location [old [LOCATION VALUE]]].
    exists location; split; [exact LOCATION|].
    assert (CHUNK : location_chunk location = Mint32) by (eapply INT32; exact LOCATION).
    split; [exact CHUNK|eapply memory_int32_load_capable; eassumption].
Qed.
Lemma memory_cell_capable_backwards event before after cell :
  memory_event_step event before after ->
  memory_cell_capable (runtime_locations after) (runtime_memory after) cell ->
  memory_cell_capable (runtime_locations before) (runtime_memory before) cell.
Proof.
  intros RUN [location [LOC [CHUNK [VALID ALIGN]]]].
  rewrite (memory_event_locations_preserved RUN) in LOC.
  exists location; split; [exact LOC|]; split; [exact CHUNK|]; split; [|exact ALIGN].
  apply (proj2 (@memory_event_valid_pointer_preserved event before after _ _ RUN)); exact VALID.
Qed.
Theorem memory_trace_access_capabilities events before after :
  memory_locations_int32 (runtime_locations before) ->
  Iter.iter_semantics memory_event_step events before after ->
  Forall (fun event => Forall (memory_cell_capable (runtime_locations before) (runtime_memory before))
    (memory_event_cells event)) events.
Proof.
  intros INT32 RUN; revert INT32; induction RUN; intro INT32; [constructor|].
  constructor.
  - eapply memory_event_access_capabilities; eassumption.
  - assert (MIDDLE : memory_locations_int32 (runtime_locations st2)).
    { rewrite (memory_event_locations_preserved H); exact INT32. }
    pose proof (IHRUN MIDDLE) as CAPABILITIES.
    eapply Forall_impl; [|exact CAPABILITIES]; intros event CELLS.
    eapply Forall_impl; [|exact CELLS]; intros cell CAPABLE.
    eapply memory_cell_capable_backwards; eassumption.
Qed.
Theorem memory_loop_source_capabilities loop parameters before after :
  memory_locations_int32 (runtime_locations before) -> L.loop_semantics loop parameters before after ->
  Forall (fun event => Forall (memory_cell_capable (runtime_locations before) (runtime_memory before))
    (memory_event_cells event)) (memory_loop_trace loop parameters).
Proof.
  intros INT32 RUN; eapply memory_trace_access_capabilities;
    [exact INT32|apply memory_loop_trace_correct; exact RUN].
Qed.
Print Assumptions memory_event_access_capabilities.
Print Assumptions memory_trace_access_capabilities.
Print Assumptions memory_loop_source_capabilities.
