From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryArrayBackend GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryRegistryTransfer GuardMemoryLayoutRegistry GuardMemoryAffineSourceExpressions GuardMemoryAffineAccessExpressions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_affine_access := MemoryAffineAccess {
  memory_access_array : ident;
  memory_access_shape : rectangle_shape;
  memory_access_expression : memory_source_affine;
  memory_access_index : memory_affine_index
}.
Definition memory_access_descriptor access := MemoryArrayDescriptor
  (memory_access_array access) (memory_access_array access) (memory_access_shape access).
Definition memory_access_code access := memory_affine_access_lvalue
  (memory_access_shape access) (memory_access_array access) (memory_access_expression access).
Definition memory_access_instruction access :=
  (memory_access_array access, [([memory_index_row (memory_access_index access);
    memory_index_column (memory_access_index access)],memory_index_bias (memory_access_index access))]).
Lemma memory_affine_access_cell access i j :
  exact_cell (memory_access_instruction access) [i;j] =
    point_cell (memory_access_array access) (memory_index_value (memory_access_index access) i j).
Proof.
  change (point_cell (memory_access_array access)
    (memory_index_row (memory_access_index access)*i+(memory_index_column (memory_access_index access)*j+0)+memory_index_bias (memory_access_index access)) =
    point_cell (memory_access_array access) (memory_index_row (memory_access_index access)*i+memory_index_column (memory_access_index access)*j+memory_index_bias (memory_access_index access))).
  f_equal; ring.
Qed.

Definition memory_index_box_check rows columns extent term :=
  (0 <? rows) && (0 <? columns) && (0 <=? memory_index_row term) &&
  (0 <=? memory_index_column term) && (memory_index_bias term =? 0) &&
  (memory_index_value term (rows-1) (columns-1) <? extent).
Lemma memory_index_box_sound rows columns extent term :
  memory_index_box_check rows columns extent term = true ->
  forall i j, 0 <= i < rows -> 0 <= j < columns ->
    0 <= memory_index_value term i j < extent.
Proof.
  unfold memory_index_box_check; rewrite !andb_true_iff,!Z.ltb_lt,!Z.leb_le,Z.eqb_eq.
  intros [[[[[ROWS COLUMNS] ROW] COLUMN] BIAS] LAST] i j I J.
  unfold memory_index_value in *; rewrite BIAS in *; nia.
Qed.
Lemma memory_index_box_zero rows columns extent term :
  memory_index_box_check rows columns extent term = true -> memory_index_value term 0 0 = 0.
Proof.
  unfold memory_index_box_check; rewrite !andb_true_iff,Z.eqb_eq.
  intros [[[[[_ _] _] _] BIAS] _]; unfold memory_index_value; rewrite BIAS; ring.
Qed.

Theorem memory_affine_access_registry descriptors entries ge locals access i j block :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  memory_descriptors_cover descriptors [memory_access_descriptor access] ->
  NoDup (map memory_array_id entries) ->
  rect_array_binding (memory_access_shape access) ge locals (memory_access_array access) block ->
  0 <= memory_index_value (memory_access_index access) i j < rectangle_extent (memory_access_shape access) ->
  memory_array_registry entries (exact_cell (memory_access_instruction access) [i;j]) =
    Some (MemoryLocation Mint32 block (4*memory_index_value (memory_access_index access) i j)).
Proof.
  intros ARRAYS COVER UNIQUE BINDING BOUND.
  destruct (@memory_registry_requested_array descriptors [memory_access_descriptor access] entries ge locals
    (memory_access_array access) (memory_access_shape access) ARRAYS COVER ltac:(cbn; auto))
    as [entry [MEMBER [ID [EXTENT ARRAY]]]].
  assert (BLOCK : memory_array_block entry = block) by
    (eapply rect_array_binding_unique; eassumption).
  rewrite memory_affine_access_cell,<- ID.
  rewrite (@memory_array_registry_member entries entry
    (point_cell (memory_array_id entry) (memory_index_value (memory_access_index access) i j))
    UNIQUE MEMBER eq_refl),EXTENT,BLOCK.
  apply flat_array_location_at; exact BOUND.
Qed.
Print Assumptions memory_index_box_sound.
Print Assumptions memory_affine_access_registry.
