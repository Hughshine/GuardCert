From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryNaryAffineExpressions GuardMemoryAxisBoundaryMath.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_param_boundary_specialize dimensions (term : constraint) parameters : constraint :=
  (resize dimensions (fst term),dot_product (skipn dimensions (fst term)) parameters+snd term).
Lemma memory_param_boundary_specialize_value dimensions term parameters coordinates :
  length coordinates = dimensions ->
  memory_nary_index_value term (coordinates++parameters) =
    memory_nary_index_value (memory_param_boundary_specialize dimensions term parameters) coordinates.
Proof.
  intro LENGTH; unfold memory_nary_index_value,memory_param_boundary_specialize; cbn.
  rewrite dot_product_app_right,LENGTH; ring.
Qed.

Definition memory_param_boundary_offset modulus base dimensions term parameters coordinates :=
  memory_axis_boundary_offset modulus base (fst (memory_param_boundary_specialize dimensions term parameters))
    (snd (memory_param_boundary_specialize dimensions term parameters)) coordinates.
Lemma memory_param_boundary_offset_value modulus base dimensions term parameters coordinates :
  length coordinates = dimensions ->
  memory_param_boundary_offset modulus base dimensions term parameters coordinates =
    (base+4*memory_nary_index_value term (coordinates++parameters)) mod modulus.
Proof.
  intro LENGTH; rewrite (@memory_param_boundary_specialize_value dimensions term parameters coordinates LENGTH).
  reflexivity.
Qed.
Theorem memory_param_boundary_overlap modulus first_base second_base dimensions first_term second_term parameters first second :
  resize dimensions (fst first_term) = resize dimensions (fst second_term) ->
  length first = dimensions -> length second = dimensions ->
  memory_param_boundary_offset modulus first_base dimensions first_term parameters first =
    memory_param_boundary_offset modulus second_base dimensions second_term parameters second ->
  memory_param_boundary_offset modulus first_base dimensions first_term parameters (memory_axis_boundary_left first second) =
    memory_param_boundary_offset modulus second_base dimensions second_term parameters (memory_axis_boundary_right first second).
Proof.
  intros COEFFICIENTS FIRST SECOND SAME.
  unfold memory_param_boundary_offset,memory_param_boundary_specialize in *; cbn in *.
  rewrite COEFFICIENTS in *.
  eapply memory_axis_boundary_overlap; [lia|exact SAME].
Qed.
Print Assumptions memory_param_boundary_specialize_value.
Print Assumptions memory_param_boundary_overlap.
