From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions
  GuardMemoryWindowCompute GuardMemoryWindowAccess GuardMemoryMultiPointerIdentifiers.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestLeafModel AffineNestScanAccesses.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_package_scan_access source parameters live proposal
  (package:affine_guard_package source parameters live proposal) access :
  In access(affine_scan_accesses(affine_proposed_operations proposal)) ->
  In(memory_nary_access_array access)(affine_proposed_pointers proposal) /\
  window_access_valid(affine_proposed_leaf_bounds proposal)(affine_proposed_window_lower proposal)
    (affine_proposed_window_upper proposal)(affine_proposal_layout proposal parameters) access.
Proof.
  intro MEMBER; unfold affine_scan_accesses in MEMBER; apply in_flat_map in MEMBER as [operation [OPERATION MEMBER]].
  pose proof(affine_leaf_valid(affine_package_leaf package)) as VALID.
  pose proof(affine_leaf_covered(affine_package_leaf package)) as COVERED.
  apply Forall_forall with(x:=operation) in VALID,COVERED; [|exact OPERATION|exact OPERATION].
  destruct VALID as [WRITE [READS REST]]; destruct COVERED as [OWN_WRITE OWN_READS].
  unfold affine_scan_operation_accesses in MEMBER; destruct MEMBER as [<-|MEMBER]; [auto|].
  apply Forall_forall with(x:=access) in READS,OWN_READS; [auto|exact MEMBER|exact MEMBER].
Qed.

Theorem affine_package_scan_access_reads source parameters live proposal
  (package:affine_guard_package source parameters live proposal) access identifier :
  In access(affine_scan_accesses(affine_proposed_operations proposal)) ->
  In identifier(memory_source_affine_reads(memory_nary_access_expression access)) ->
  In identifier(affine_nest_iterators(affine_proposal_nest proposal)++parameters).
Proof.
  intros ACCESS READ.
  destruct(@affine_package_scan_access source parameters live proposal package access ACCESS)
    as [POINTER [_ [_ [ENCODE RANGE]]]].
  eapply memory_encode_nary_index_reads; eassumption.
Qed.
Print Assumptions affine_package_scan_access_reads.
