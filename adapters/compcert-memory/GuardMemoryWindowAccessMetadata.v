From Stdlib Require Import List.
From GuardMemory Require Import GuardMemoryLinearPointerSyntax GuardMemoryNaryAffineExpressions GuardMemoryMultiPointerCompute GuardMemoryRecursiveSource GuardMemoryNaryAffineAccess.
From GuardMemory Require Import GuardMemoryWindowPackage GuardMemoryWindowSyntax GuardMemoryWindowAccess GuardMemoryWindowCompute.
Import ListNotations.
Set Implicit Arguments.
Lemma window_accesses_valid source (package : window_region_package source) :
  Forall (window_access_valid
    (window_source_coordinate_bounds (window_region_root_lower package) (window_region_caps package)++window_region_parameter_bounds package)
    (window_region_lower package) (window_region_upper package)
    (memory_nest_iterators (window_region_nest package)++window_region_parameters package))
    (memory_linear_pointer_accesses (window_region_operations package)).
Proof.
  pose proof (window_source_operations (window_region_certificate package)) as OPS.
  induction OPS as [|operation operations [WRITE [READS VALUE]] REST IH]; cbn [memory_linear_pointer_accesses flat_map].
  - constructor.
  - apply Forall_app; split; [constructor; assumption|exact IH].
Qed.
Lemma window_accesses_encoding source (package : window_region_package source) access :
  In access (memory_linear_pointer_accesses (window_region_operations package)) ->
  memory_encode_nary_index (memory_nest_iterators (window_region_nest package)++window_region_parameters package)
    (memory_nary_access_expression access) = Some (memory_nary_access_index access).
Proof.
  intro MEMBER; pose proof (window_accesses_valid package) as VALID.
  apply Forall_forall with (x := access) in VALID; [|exact MEMBER].
  exact (proj1 (proj2 (proj2 VALID))).
Qed.
Lemma window_accesses_covered source (package : window_region_package source) :
  Forall (fun access => In (memory_nary_access_array access) (window_region_pointers package))
    (memory_linear_pointer_accesses (window_region_operations package)).
Proof.
  pose proof (window_source_covered (window_region_certificate package)) as OPS.
  induction OPS as [|operation operations [WRITE READS] REST IH]; cbn [memory_linear_pointer_accesses flat_map].
  - constructor.
  - apply Forall_app; split; [constructor; assumption|exact IH].
Qed.
Print Assumptions window_accesses_encoding.
Print Assumptions window_accesses_covered.
