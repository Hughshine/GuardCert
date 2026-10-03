From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCountedLoop ClightRectangularStore CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryNaryAffineAccess
  GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck GuardMemoryNaryRanges GuardMemoryPointerNaryAccess
  GuardMemoryPointerAccess GuardMemoryPointerSourceAccess GuardMemoryBufferOffsets GuardMemoryMultiPointerCells GuardMemoryScalarAccess.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_multi_pointer_access_valid limits layout extent access :=
  memory_nary_access_valid limits layout access /\ rectangle_extent (memory_nary_access_shape access) = extent.
Definition memory_multi_pointer_access_loaded temps values memory access value :=
  exists block base, temps ! (memory_nary_access_array access) = Some (Vptr block base) /\
    Mem.load Mint32 memory block (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index access) values)) = Some value.
Lemma memory_multi_pointer_access_registry limits layout extent temps access block base values :
  memory_multi_pointer_access_valid limits layout extent access -> memory_nary_ranges limits values ->
  temps ! (memory_nary_access_array access) = Some (Vptr block base) ->
  memory_multi_pointer_locations temps extent (exact_cell (memory_nary_access_instruction access) values) =
    Some (MemoryLocation Mint32 block (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index access) values))).
Proof.
  intros [[SHAPE [ENCODE BOUNDS]] EXTENT] RANGE POINTER.
  rewrite memory_nary_access_cell; unfold memory_multi_pointer_locations; cbn [point_cell arr_id].
  rewrite POINTER; apply memory_pointer_buffer_location_at; rewrite <-EXTENT; apply BOUNDS; exact RANGE.
Qed.
Lemma memory_multi_pointer_loaded_unique temps values memory access first second :
  memory_multi_pointer_access_loaded temps values memory access first ->
  memory_multi_pointer_access_loaded temps values memory access second -> first = second.
Proof.
  intros [first_block [first_base [FIRST FIRST_LOAD]]] [second_block [second_base [SECOND SECOND_LOAD]]].
  rewrite FIRST in SECOND; inversion SECOND; subst second_block second_base; congruence.
Qed.
Theorem memory_multi_pointer_source_read_inverse access limits layout valuation ge locals temps memory value :
  memory_nary_access_valid limits layout access -> memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  eval_expr ge locals temps memory (memory_pointer_nary_code access) value ->
  memory_multi_pointer_access_loaded temps (map valuation layout) memory access value.
Proof. intros VALID RANGE WORDS READ; eapply memory_pointer_nary_load_inverse; eassumption. Qed.
Lemma memory_multi_pointer_reads_prefix limits layout scalars extent accesses temps memory valuation loaded :
  Forall (memory_multi_pointer_access_valid limits layout extent) accesses ->
  Forall2 (memory_multi_pointer_access_loaded temps (map valuation layout) memory) accesses loaded ->
  Forall2 (memory_multi_pointer_access_loaded temps (map valuation (layout++scalars)) memory) accesses loaded.
Proof.
  intros VALID LOAD; induction LOAD; [constructor|].
  inversion VALID; subst; constructor.
  - unfold memory_multi_pointer_access_loaded in *; destruct H as [block [base [POINTER LOADED]]].
    exists block,base; split; [exact POINTER|].
    rewrite map_app,memory_scalar_index_value; [exact LOADED|].
    match goal with HEAD : memory_multi_pointer_access_valid _ _ _ x |- _ =>
      destruct HEAD as [[SHAPE [ENCODE BOUND]] EXTENT];
      rewrite (@memory_encode_nary_index_length layout _ _ ENCODE),length_map; reflexivity end.
  - apply IHLOAD; assumption.
Qed.
Lemma memory_multi_pointer_loaded_registry limits layout extent temps access values memory value :
  memory_multi_pointer_access_valid limits layout extent access -> memory_nary_ranges limits values ->
  memory_multi_pointer_access_loaded temps values memory access value ->
  exists location, memory_multi_pointer_locations temps extent
    (exact_cell (memory_nary_access_instruction access) values) = Some location /\
    location_load location memory = Some value.
Proof.
  intros VALID RANGE [block [base [POINTER LOAD]]].
  exists (MemoryLocation Mint32 block (memory_pointer_buffer_offset base
    (memory_nary_index_value (memory_nary_access_index access) values))); split;
    [eapply memory_multi_pointer_access_registry; eassumption|exact LOAD].
Qed.
Lemma memory_multi_pointer_scalar_access_registry limits layout extent temps access block base coordinates values :
  memory_multi_pointer_access_valid limits layout extent access -> memory_nary_ranges limits coordinates ->
  length coordinates = length layout ->
  temps ! (memory_nary_access_array access) = Some (Vptr block base) ->
  memory_multi_pointer_locations temps extent
    (exact_cell (memory_nary_access_instruction access) (coordinates++values)) =
    Some (MemoryLocation Mint32 block (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index access) coordinates))).
Proof.
  intros VALID RANGE LENGTH POINTER.
  rewrite (@memory_scalar_access_cell layout access coordinates values (proj1 (proj2 (proj1 VALID))) LENGTH).
  eapply memory_multi_pointer_access_registry; eassumption.
Qed.
Lemma memory_multi_pointer_read_list_inverse limits layout extent accesses valuation ge locals temps memory loaded :
  Forall (memory_multi_pointer_access_valid limits layout extent) accesses ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  Forall2 (fun code value => eval_expr ge locals temps memory code value)
    (map memory_pointer_nary_code accesses) loaded ->
  Forall2 (memory_multi_pointer_access_loaded temps (map valuation layout) memory) accesses loaded.
Proof.
  intros VALID RANGE WORDS; revert loaded; induction VALID as [|access accesses [HEAD EXTENT] VALID IH];
    intros loaded READS; inversion READS; subst; constructor.
  - eapply memory_multi_pointer_source_read_inverse; eassumption.
  - apply IH; assumption.
Qed.
Print Assumptions memory_multi_pointer_access_registry.
Print Assumptions memory_multi_pointer_source_read_inverse.
Print Assumptions memory_multi_pointer_loaded_registry.
Print Assumptions memory_multi_pointer_scalar_access_registry.
