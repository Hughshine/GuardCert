From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightIndexedArray ClightRectangularStore CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultipleArrays
  GuardMemoryRegistryBackend GuardMemoryRegistryTransfer GuardMemoryLayoutRegistry GuardMemoryAffineSourceExpressions
  GuardMemoryNaryAffineExpressions GuardMemoryNaryRanges.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_nary_access := MemoryNaryAccess {
  memory_nary_access_array : ident;
  memory_nary_access_shape : rectangle_shape;
  memory_nary_access_expression : memory_source_affine;
  memory_nary_access_index : constraint
}.
Definition memory_nary_access_descriptor access := MemoryArrayDescriptor
  (memory_nary_access_array access) (memory_nary_access_array access) (memory_nary_access_shape access).
Definition memory_nary_access_code access := indexed_array_lvalue (memory_nary_access_shape access)
  (memory_nary_access_array access) (memory_source_affine_code (memory_nary_access_expression access)).
Definition memory_nary_access_instruction access := (memory_nary_access_array access,[memory_nary_access_index access]).
Lemma memory_nary_access_cell access values :
  exact_cell (memory_nary_access_instruction access) values =
  point_cell (memory_nary_access_array access) (memory_nary_index_value (memory_nary_access_index access) values).
Proof. reflexivity. Qed.
Theorem memory_nary_access_lvalue_inverse access layout valuation ge locals temps memory block offset field :
  rectangle_layout_valid (memory_nary_access_shape access) ->
  memory_encode_nary_index layout (memory_nary_access_expression access) = Some (memory_nary_access_index access) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  0 <= memory_nary_index_value (memory_nary_access_index access) (map valuation layout) < rectangle_extent (memory_nary_access_shape access) ->
  eval_lvalue ge locals temps memory (memory_nary_access_code access) block offset field ->
  rect_array_binding (memory_nary_access_shape access) ge locals (memory_nary_access_array access) block /\
  offset = Ptrofs.repr (4*memory_nary_index_value (memory_nary_access_index access) (map valuation layout)) /\ field = Full.
Proof.
  intros VALID ENCODE WORDS BOUND RUN.
  eapply indexed_array_lvalue_inverse; [exact VALID|apply memory_source_affine_type|apply memory_source_affine_pure|
    eapply memory_nary_index_expression_evaluation; eassumption|exact BOUND|exact RUN].
Qed.
Theorem memory_nary_access_load_inverse access layout valuation ge locals temps memory value :
  rectangle_layout_valid (memory_nary_access_shape access) ->
  memory_encode_nary_index layout (memory_nary_access_expression access) = Some (memory_nary_access_index access) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  0 <= memory_nary_index_value (memory_nary_access_index access) (map valuation layout) < rectangle_extent (memory_nary_access_shape access) ->
  eval_expr ge locals temps memory (memory_nary_access_code access) value ->
  exists block, rect_array_binding (memory_nary_access_shape access) ge locals (memory_nary_access_array access) block /\
    Mem.load Mint32 memory block (4*memory_nary_index_value (memory_nary_access_index access) (map valuation layout)) = Some value.
Proof.
  intros VALID ENCODE WORDS BOUND RUN.
  eapply indexed_array_load_inverse; [exact VALID|apply memory_source_affine_type|apply memory_source_affine_pure|
    eapply memory_nary_index_expression_evaluation; eassumption|exact BOUND|exact RUN].
Qed.
Theorem memory_nary_access_registry descriptors entries ge locals access values block :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  memory_descriptors_cover descriptors [memory_nary_access_descriptor access] ->
  NoDup (map memory_array_id entries) ->
  rect_array_binding (memory_nary_access_shape access) ge locals (memory_nary_access_array access) block ->
  0 <= memory_nary_index_value (memory_nary_access_index access) values < rectangle_extent (memory_nary_access_shape access) ->
  memory_array_registry entries (exact_cell (memory_nary_access_instruction access) values) =
    Some (MemoryLocation Mint32 block (4*memory_nary_index_value (memory_nary_access_index access) values)).
Proof.
  intros ARRAYS COVER UNIQUE BINDING BOUND.
  destruct (@memory_registry_requested_array descriptors [memory_nary_access_descriptor access] entries ge locals
    (memory_nary_access_array access) (memory_nary_access_shape access) ARRAYS COVER ltac:(cbn; auto))
    as [entry [MEMBER [ID [EXTENT ARRAY]]]].
  assert (BLOCK : memory_array_block entry = block) by (eapply rect_array_binding_unique; eassumption).
  rewrite memory_nary_access_cell,<- ID.
  rewrite (@memory_array_registry_member entries entry
    (point_cell (memory_array_id entry) (memory_nary_index_value (memory_nary_access_index access) values))
    UNIQUE MEMBER eq_refl),EXTENT,BLOCK.
  apply flat_array_location_at; exact BOUND.
Qed.
Print Assumptions memory_nary_access_load_inverse.
Print Assumptions memory_nary_access_registry.
