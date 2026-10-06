From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryNaryCompute
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryMultiPointerCompute GuardMemoryLinearPointerSyntax
  GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryInstructionPadding
  GuardMemoryRectangularFootprint GuardMemoryMultiPointerFootprint.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Access footprints and signed entry values are independent of the loop
    shape. Rectangular and affine-inner instances consume the same lemmas. *)
Definition memory_param_axis_pointer_access_cell access coordinates :=
  point_cell (memory_nary_access_array access) (memory_nary_index_value (memory_nary_access_index access) coordinates).

Lemma memory_param_axis_pointer_point_footprint extra operations coordinates :
  memory_point_footprint (memory_pad_instructions extra (map memory_nary_compute_instruction operations)) coordinates =
    map (fun access => memory_param_axis_pointer_access_cell access coordinates) (memory_linear_pointer_accesses operations).
Proof.
  induction operations as [|operation operations IH]; [reflexivity|].
  cbn [memory_point_footprint memory_pad_instructions map flat_map].
  rewrite memory_pad_instruction_footprint.
  change (memory_instruction_footprint (memory_nary_compute_instruction operation) coordinates ++
    memory_point_footprint (memory_pad_instructions extra (map memory_nary_compute_instruction operations)) coordinates =
      map (fun access => memory_param_axis_pointer_access_cell access coordinates) (memory_linear_pointer_accesses (operation::operations))).
  rewrite IH; unfold memory_linear_pointer_accesses; cbn [flat_map]; rewrite map_app; f_equal.
  unfold memory_instruction_footprint; cbn [memory_nary_compute_instruction instruction_write instruction_reads].
  rewrite map_map; reflexivity.
Qed.

Lemma memory_param_axis_pointer_parameters identifiers values temps :
  memory_nest_bindings identifiers values temps -> Forall signed_range values ->
  memory_recursive_parameters identifiers temps = values.
Proof.
  intro WORDS; induction WORDS as [|identifier value identifiers values WORD WORDS IH]; intro RANGES.
  - reflexivity.
  - inversion RANGES; subst; unfold memory_recursive_parameters at 1; cbn [map].
    unfold temp_word at 1; rewrite WORD,Int.signed_repr by assumption.
    f_equal; apply IH; assumption.
Qed.

Print Assumptions memory_param_axis_pointer_point_footprint.
Print Assumptions memory_param_axis_pointer_parameters.
