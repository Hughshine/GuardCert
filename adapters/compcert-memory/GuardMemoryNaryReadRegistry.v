From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightRectangularStore CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRegistryBackend GuardMemoryMultipleArrays
  GuardMemoryLayoutRegistry GuardMemoryNaryAffineExpressions GuardMemoryNaryAffineAccess GuardMemoryNarySourceValues.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_nary_read_location ge locals point_values access location :=
  exists block, rect_array_binding (memory_nary_access_shape access) ge locals (memory_nary_access_array access) block /\
    location = MemoryLocation Mint32 block (4*memory_nary_index_value (memory_nary_access_index access) point_values).
Lemma memory_nary_reads_resolve descriptors entries ge locals point_values accesses :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  NoDup (map memory_array_id entries) ->
  memory_descriptors_cover descriptors (map memory_nary_access_descriptor accesses) ->
  Forall (fun access => 0 <= memory_nary_index_value (memory_nary_access_index access) point_values <
    rectangle_extent (memory_nary_access_shape access)) accesses ->
  exists locations,
    Forall2 (memory_nary_read_location ge locals point_values) accesses locations /\
    resolve_cells (map (fun access => exact_cell (memory_nary_access_instruction access) point_values) accesses)
      (memory_array_registry entries) = Some locations.
Proof.
  intros ARRAYS UNIQUE COVER BOUNDS; induction accesses as [|access accesses IH].
  - exists []; split; [constructor|reflexivity].
  - inversion COVER; inversion BOUNDS; subst.
    assert (SINGLE : memory_descriptors_cover descriptors [memory_nary_access_descriptor access])
      by (constructor; [assumption|constructor]).
    destruct (@memory_registry_requested_array descriptors [memory_nary_access_descriptor access] entries ge locals
      (memory_nary_access_array access) (memory_nary_access_shape access) ARRAYS SINGLE ltac:(cbn; auto))
      as [entry [MEMBER [ID [EXTENT ARRAY]]]].
    destruct (IH ltac:(assumption) ltac:(assumption)) as [locations [RELATED RESOLVE]].
    exists (MemoryLocation Mint32 (memory_array_block entry)
      (4*memory_nary_index_value (memory_nary_access_index access) point_values)::locations); split.
    + constructor; [exists (memory_array_block entry); auto|exact RELATED].
    + cbn [map resolve_cells].
      rewrite (@memory_nary_access_registry descriptors entries ge locals access point_values (memory_array_block entry)
        ARRAYS SINGLE UNIQUE ARRAY ltac:(assumption)),RESOLVE; reflexivity.
Qed.
Theorem memory_nary_reads_loads ge locals point_values accesses locations :
  Forall2 (memory_nary_read_location ge locals point_values) accesses locations ->
  forall memory values,
    Forall2 (memory_nary_source_access_loaded ge locals point_values memory) accesses values <->
    load_locations locations memory = Some values.
Proof.
  intro RELATED; induction RELATED as [|access location accesses locations HEAD RELATED IH]; intros memory values.
  - split; intro LOAD; [inversion LOAD; reflexivity|cbn in LOAD; inversion LOAD; constructor].
  - destruct HEAD as [block [ARRAY ->]]; cbn [load_locations location_load location_chunk location_block location_offset].
    unfold CompCertMemoryActions.location_load; cbn [location_chunk location_block location_offset].
    split; intro LOAD.
    + inversion LOAD; subst; match goal with H : memory_nary_source_access_loaded _ _ _ _ access _ |- _ =>
        destruct H as [actual [BINDING FIRST]];
        assert (actual=block) by (eapply rect_array_binding_unique; eassumption); subst actual end.
      rewrite FIRST; match goal with REST : Forall2 (memory_nary_source_access_loaded _ _ _ _) accesses _ |- _ =>
        apply (proj1 (IH memory _)) in REST; rewrite REST end; reflexivity.
    + destruct (Mem.load Mint32 memory block (4*memory_nary_index_value (memory_nary_access_index access) point_values)) as [value|] eqn:VALUE;
        [|discriminate].
      destruct (load_locations locations memory) as [tail|] eqn:TAIL; [|discriminate].
      inversion LOAD; subst values; constructor; [exists block; auto|apply IH; exact TAIL].
Qed.
Print Assumptions memory_nary_reads_resolve.
Print Assumptions memory_nary_reads_loads.
