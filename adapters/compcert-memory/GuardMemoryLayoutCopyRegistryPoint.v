From Stdlib Require Import List ZArith.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryLayoutRegistry GuardMemoryLayoutCopy GuardMemoryLayoutCopyInstruction
  GuardMemoryLayoutCopyRegistry.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Theorem memory_layout_copy_general_registry_point descriptors entries ge locals ws rs wa ra i j before after :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  memory_descriptors_cover descriptors (memory_layout_copy_descriptors ws rs wa ra) ->
  NoDup (map memory_array_id entries) ->
  0 <= i*rectangle_stride ws+j < rectangle_extent ws ->
  0 <= i*rectangle_stride rs+j < rectangle_extent rs ->
  (memory_layout_copy_point ge locals ws rs wa ra i j before after <->
    memory_point (memory_layout_copy_instruction ws rs wa ra) i j
      (RuntimeState (memory_array_registry entries) before) (RuntimeState (memory_array_registry entries) after)).
Proof.
  intros ARRAYS COVER UNIQUE WINDEX RINDEX.
  destruct (@memory_registry_requested_array descriptors (memory_layout_copy_descriptors ws rs wa ra) entries ge locals wa ws
    ARRAYS COVER ltac:(cbn; auto)) as [write_entry [WENTRY [WID [WEXTENT WRITE]]]].
  destruct (@memory_registry_requested_array descriptors (memory_layout_copy_descriptors ws rs wa ra) entries ge locals ra rs
    ARRAYS COVER ltac:(cbn; auto)) as [read_entry [RENTRY [RID [REXTENT READ]]]].
  unfold memory_layout_copy_point.
  rewrite <- WID in WRITE; rewrite <- RID in READ.
  rewrite <- WID,<- RID.
  rewrite (@memory_layout_copy_registry_execution entries write_entry read_entry ws rs i j before after
    UNIQUE WENTRY RENTRY WEXTENT REXTENT WINDEX RINDEX).
  split.
  - intros [wb [rb [WB [RB RUN]]]].
    assert (WSAME : wb = memory_array_block write_entry) by (eapply rect_array_binding_unique; eauto).
    assert (RSAME : rb = memory_array_block read_entry) by (eapply rect_array_binding_unique; eauto).
    subst wb rb; exact RUN.
  - intro RUN; exists (memory_array_block write_entry),(memory_array_block read_entry); repeat split; assumption.
Qed.
Print Assumptions memory_layout_copy_general_registry_point.
