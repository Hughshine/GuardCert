From Stdlib Require Import List ZArith.
From compcert.common Require Import AST.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryRectangularFootprint
  GuardMemoryAffineSourceExpressions GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryCompute GuardMemoryWindowAccess GuardMemoryWindowCompute.
Import ListNotations.
Set Implicit Arguments.

Definition affine_scan_operation_accesses operation :=
  memory_nary_compute_write operation::memory_nary_compute_reads operation.
Definition affine_scan_accesses operations := flat_map affine_scan_operation_accesses operations.
Definition affine_scan_access_cell valuation access :=
  point_cell(memory_nary_access_array access)(memory_source_affine_math valuation(memory_nary_access_expression access)).

Lemma affine_scan_access_exact bounds lower upper layout access valuation :
  window_access_valid bounds lower upper layout access ->
  exact_cell(memory_nary_access_instruction access)(map valuation layout)=affine_scan_access_cell valuation access.
Proof.
  intros [_ [_ [ENCODE RANGE]]]; rewrite memory_nary_access_cell.
  unfold affine_scan_access_cell; rewrite <-(@memory_encode_nary_index_value _ _ _ valuation ENCODE); reflexivity.
Qed.

Lemma affine_scan_operation_footprint bounds lower upper layout scalars operation valuation :
  window_compute_valid bounds lower upper layout scalars operation ->
  memory_instruction_footprint(memory_nary_compute_instruction operation)(map valuation layout)=
    map(affine_scan_access_cell valuation)(affine_scan_operation_accesses operation).
Proof.
  intros [WRITE [READS REST]]; unfold memory_instruction_footprint,affine_scan_operation_accesses.
  cbn [memory_nary_compute_instruction instruction_write instruction_reads map]; rewrite map_map.
  rewrite(@affine_scan_access_exact bounds lower upper layout _ valuation WRITE).
  f_equal; apply map_ext_in; intros access MEMBER; apply affine_scan_access_exact with(bounds:=bounds)(lower:=lower)(upper:=upper).
  apply Forall_forall with(x:=access) in READS; assumption.
Qed.

Theorem affine_scan_point_footprint bounds lower upper layout scalars operations valuation :
  Forall(window_compute_valid bounds lower upper layout scalars) operations ->
  memory_point_footprint(map memory_nary_compute_instruction operations)(map valuation layout)=
    map(affine_scan_access_cell valuation)(affine_scan_accesses operations).
Proof.
  intro VALID; induction VALID; [reflexivity|].
  change(memory_instruction_footprint(memory_nary_compute_instruction x)(map valuation layout)++
    memory_point_footprint(map memory_nary_compute_instruction l)(map valuation layout)=
    map(affine_scan_access_cell valuation)(affine_scan_operation_accesses x++affine_scan_accesses l)).
  rewrite map_app.
  rewrite(@affine_scan_operation_footprint bounds lower upper layout scalars x valuation H),IHVALID; reflexivity.
Qed.
Print Assumptions affine_scan_point_footprint.
