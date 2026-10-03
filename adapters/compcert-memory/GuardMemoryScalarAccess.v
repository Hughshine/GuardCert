From Stdlib Require Import List ZArith Lia.
From compcert.common Require Import AST.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryNaryAffineExpressions
  GuardMemoryNaryAffineAccess GuardMemoryNaryAccessCheck GuardMemoryNaryRanges GuardMemoryPointerCompute
  GuardMemoryPointerRegistry GuardMemoryBufferOffsets GuardMemoryAffineSourceLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_nary_unit_length dimensions position : length (memory_nary_unit dimensions position) = dimensions.
Proof.
  revert position; induction dimensions; intros [|position]; cbn; auto.
  rewrite repeat_length; reflexivity.
Qed.
Lemma memory_add_vector_length first second : length first = length second ->
  length (add_vector first second) = length first.
Proof.
  revert second; induction first; intros [|head second] SAME; cbn in *; try discriminate; auto.
Qed.
Lemma memory_encode_nary_index_length layout expression term : memory_encode_nary_index layout expression = Some term ->
  length (fst term) = length layout.
Proof.
  revert term; induction expression; intros term ENCODE; cbn [memory_encode_nary_index] in ENCODE.
  - destruct (memory_source_position identifier layout); cbn in ENCODE; [|discriminate].
    inversion ENCODE; subst; apply memory_nary_unit_length.
  - inversion ENCODE; subst; apply repeat_length.
  - destruct (memory_encode_nary_index layout expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_encode_nary_index layout expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion ENCODE; subst; cbn [add_constraint fst].
    rewrite memory_add_vector_length; [apply IHexpression1; reflexivity|].
    rewrite (IHexpression1 _ eq_refl),(IHexpression2 _ eq_refl); reflexivity.
  - destruct (memory_encode_nary_index layout expression1) as [first|] eqn:FIRST; [|discriminate].
    destruct (memory_encode_nary_index layout expression2) as [second|] eqn:SECOND; [|discriminate].
    inversion ENCODE; subst; cbn [add_constraint mult_constraint fst].
    rewrite memory_add_vector_length; [apply IHexpression1; reflexivity|].
    rewrite mult_vector_length,(IHexpression1 _ eq_refl),(IHexpression2 _ eq_refl); reflexivity.
  - destruct (memory_encode_nary_index layout expression) as [first|] eqn:FIRST; cbn in ENCODE; [|discriminate];
    inversion ENCODE; subst; cbn [mult_constraint fst]; rewrite mult_vector_length; apply IHexpression; reflexivity.
  - destruct (memory_encode_nary_index layout expression) as [first|] eqn:FIRST; cbn in ENCODE; [|discriminate];
    inversion ENCODE; subst; cbn [mult_constraint fst]; rewrite mult_vector_length; apply IHexpression; reflexivity.
Qed.
Lemma memory_dot_product_prefix coefficients coordinates values : (length coefficients <= length coordinates)%nat ->
  dot_product coefficients (coordinates++values) = dot_product coefficients coordinates.
Proof.
  revert coefficients; induction coordinates as [|coordinate coordinates IH]; intros [|coefficient coefficients] LENGTH.
  - rewrite !dot_product_nil_left; reflexivity.
  - cbn in LENGTH; lia.
  - rewrite !dot_product_nil_left; reflexivity.
  - cbn [length app dot_product] in *; rewrite IH by lia; reflexivity.
Qed.
Lemma memory_scalar_index_value term coordinates values : (length (fst term) <= length coordinates)%nat ->
  memory_nary_index_value term (coordinates++values) = memory_nary_index_value term coordinates.
Proof. intro LENGTH; unfold memory_nary_index_value; rewrite memory_dot_product_prefix by exact LENGTH; reflexivity. Qed.
Lemma memory_scalar_access_cell layout access coordinates values :
  memory_encode_nary_index layout (memory_nary_access_expression access) = Some (memory_nary_access_index access) ->
  length coordinates = length layout -> exact_cell (memory_nary_access_instruction access) (coordinates++values) =
    exact_cell (memory_nary_access_instruction access) coordinates.
Proof.
  intros ENCODE LENGTH; rewrite !memory_nary_access_cell,memory_scalar_index_value; [reflexivity|].
  rewrite (@memory_encode_nary_index_length layout _ _ ENCODE),LENGTH; reflexivity.
Qed.
Lemma memory_scalar_pointer_access_registry limits layout pointer extent access block base coordinates values :
  memory_pointer_access_valid limits layout pointer extent access -> memory_nary_ranges limits coordinates ->
  length coordinates = length layout ->
  memory_pointer_buffer_locations pointer block base extent (exact_cell (memory_nary_access_instruction access) (coordinates++values)) =
    Some (memory_pointer_read_location block base coordinates access).
Proof.
  intros VALID RANGES LENGTH.
  rewrite (@memory_scalar_access_cell layout access coordinates values (proj1 (proj2 (proj1 VALID))) LENGTH).
  eapply memory_pointer_access_registry; eassumption.
Qed.
Print Assumptions memory_scalar_access_cell.
Print Assumptions memory_scalar_pointer_access_registry.
