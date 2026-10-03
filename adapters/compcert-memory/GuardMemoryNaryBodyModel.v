From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightLoopSyntax ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryLayoutRegistry GuardMemoryNaryRanges
  GuardMemoryNaryCompute GuardMemoryNarySequence GuardMemoryNaryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_nary_body_model limits (layout : list ident) body := MemoryNaryBodyModel {
  nary_body_descriptors : list memory_array_descriptor;
  nary_body_instructions : list memory_instruction;
  nary_body_point : genv -> env -> list Z -> mem -> mem -> Prop;
  nary_body_normal : normal_statement body = true;
  nary_body_quiet : quiet_statement body = true;
  nary_body_writes : writes_only [] body;
  nary_body_decode : forall fe ge locals le before after final valuation,
    memory_nary_ranges limits (map valuation layout) ->
    (forall identifier, In identifier layout -> le ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
    exec_stmt fe ge locals le before body E0 after final Out_normal ->
    nary_body_point ge locals (map valuation layout) before final /\ after = le;
  nary_body_registry : forall ge locals before after,
    nary_body_point ge locals (repeat 0 (length layout)) before after ->
    exists entries, Forall2 (memory_descriptor_binding ge locals) nary_body_descriptors entries /\
      NoDup (map memory_array_id entries) /\
      Forall (fun entry => Mem.valid_pointer before (memory_array_block entry) 0 = true) entries;
  nary_body_correspondence : forall entries ge locals values before after,
    Forall2 (memory_descriptor_binding ge locals) nary_body_descriptors entries ->
    NoDup (map memory_array_id entries) -> memory_nary_ranges limits values ->
    (nary_body_point ge locals values before after <->
      memory_nary_sequence_point nary_body_instructions values
        (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after))
}.
Definition memory_nary_compute_body_model limits operations layout body
  (CERT : Forall (memory_nary_compute_valid limits layout) operations)
  (COVER : memory_descriptors_cover (memory_unique_descriptors (memory_nary_compute_sequence_anchors operations))
    (memory_nary_compute_sequence_requests operations))
  (BODY : flatten_region body = map memory_nary_compute_statement operations) : memory_nary_body_model limits layout body.
Proof.
  refine {| nary_body_descriptors := memory_unique_descriptors (memory_nary_compute_sequence_anchors operations);
    nary_body_instructions := map memory_nary_compute_instruction operations;
    nary_body_point := fun ge locals values => memory_nary_compute_sequence_physical ge locals values operations;
    nary_body_normal := @memory_nary_compute_sequence_normal operations body BODY;
    nary_body_quiet := @memory_nary_compute_sequence_quiet operations body BODY;
    nary_body_writes := @memory_nary_compute_sequence_writes operations body BODY |}.
  - intros fe ge locals le before after final valuation RANGE WORDS RUN.
    apply flatten_region_execution in RUN; rewrite BODY in RUN.
    eapply memory_nary_compute_sequence_tail_inverse; eassumption.
  - intros ge locals before after RUN; eapply memory_nary_compute_sequence_registry; eassumption.
  - intros entries ge locals values before after ARRAYS UNIQUE RANGE.
    apply memory_nary_compute_sequence_point_execution with (limits := limits) (layout := layout)
      (descriptors := memory_unique_descriptors (memory_nary_compute_sequence_anchors operations)); auto.
    apply memory_nary_compute_sequence_cover; exact COVER.
Defined.
Print Assumptions memory_nary_compute_body_model.
