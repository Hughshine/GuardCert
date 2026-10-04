From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCountedLoop ClightPureExpr ClightRectangularStore CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryPointerAccess GuardMemoryPointerSourceAccess GuardMemoryBufferOffsets
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck
  GuardMemoryAffineSourceExpressions GuardMemoryPointerNaryAccess.
From GuardMemory Require Import GuardMemoryIntervalBox GuardMemorySignedWindow.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition window_access_valid bounds lower upper layout access :=
  signed_range lower /\ signed_range (upper-1) /\
  memory_encode_nary_index layout (memory_nary_access_expression access) = Some (memory_nary_access_index access) /\
  forall values, interval_ranges bounds values ->
    lower <= memory_nary_index_value (memory_nary_access_index access) values < upper.
Lemma window_pointer_index_evaluation access bounds lower upper layout valuation ge locals temps memory :
  window_access_valid bounds lower upper layout access -> interval_ranges bounds (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  eval_expr ge locals temps memory (memory_source_affine_code (memory_nary_access_expression access))
    (Vint (Int.repr (memory_nary_index_value (memory_nary_access_index access) (map valuation layout)))) /\
  signed_range (memory_nary_index_value (memory_nary_access_index access) (map valuation layout)).
Proof.
  intros [LOW [HIGH [ENCODE BOUND]]] RANGE WORDS; split.
  - eapply memory_nary_index_expression_evaluation; eassumption.
  - specialize (BOUND _ RANGE); unfold signed_range in *; lia.
Qed.
Lemma window_pointer_load_inverse access bounds lower upper layout valuation ge locals temps memory value :
  window_access_valid bounds lower upper layout access -> interval_ranges bounds (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  eval_expr ge locals temps memory (memory_pointer_nary_code access) value ->
  exists block base, temps ! (memory_nary_access_array access) = Some (Vptr block base) /\
    Mem.load Mint32 memory block
      (memory_pointer_buffer_offset base (memory_nary_index_value (memory_nary_access_index access) (map valuation layout))) = Some value.
Proof.
  intros VALID RANGE WORDS RUN.
  destruct (@window_pointer_index_evaluation access bounds lower upper layout valuation ge locals temps memory VALID RANGE WORDS) as [INDEX SIGNED].
  eapply memory_pointer_load_inverse; [apply memory_source_affine_type|apply memory_source_affine_pure|exact INDEX|exact SIGNED|exact RUN].
Qed.
Lemma window_access_registry access bounds lower upper layout block base values :
  window_access_valid bounds lower upper layout access -> interval_ranges bounds values ->
  interval_pointer_locations (memory_nary_access_array access) block base lower upper
    (exact_cell (memory_nary_access_instruction access) values) =
    Some (MemoryLocation Mint32 block (memory_pointer_buffer_offset base (memory_nary_index_value (memory_nary_access_index access) values))).
Proof.
  intros [LOW [HIGH [ENCODE BOUND]]] RANGE.
  rewrite memory_nary_access_cell; unfold interval_pointer_locations; cbn.
  rewrite Pos.eqb_refl.
  destruct (BOUND _ RANGE) as [LB UB].
  assert (LOWER : (lower <=? memory_nary_index_value (memory_nary_access_index access) values) = true) by (apply Z.leb_le; exact LB).
  assert (UPPER : (memory_nary_index_value (memory_nary_access_index access) values <? upper) = true) by (apply Z.ltb_lt; exact UB).
  rewrite LOWER,UPPER; reflexivity.
Qed.
Print Assumptions window_pointer_load_inverse.
Print Assumptions window_access_registry.

Lemma window_pointer_load_evaluation access bounds lower upper layout valuation ge locals temps memory block base value :
  window_access_valid bounds lower upper layout access -> interval_ranges bounds (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  temps ! (memory_nary_access_array access) = Some (Vptr block base) ->
  Mem.load Mint32 memory block
    (memory_pointer_buffer_offset base (memory_nary_index_value (memory_nary_access_index access) (map valuation layout))) = Some value ->
  eval_expr ge locals temps memory (memory_pointer_nary_code access) value.
Proof.
  intros VALID RANGE WORDS POINTER LOAD.
  destruct (@window_pointer_index_evaluation access bounds lower upper layout valuation ge locals temps memory VALID RANGE WORDS) as [INDEX SIGNED].
  unfold memory_pointer_nary_code; eapply memory_pointer_load_evaluation;
    [exact POINTER|apply memory_source_affine_type|exact INDEX|exact SIGNED|exact LOAD].
Qed.
Theorem window_pointer_load_correspondence access bounds lower upper layout valuation ge locals temps memory block base value :
  window_access_valid bounds lower upper layout access -> interval_ranges bounds (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  temps ! (memory_nary_access_array access) = Some (Vptr block base) ->
  (eval_expr ge locals temps memory (memory_pointer_nary_code access) value <->
   Mem.load Mint32 memory block
    (memory_pointer_buffer_offset base (memory_nary_index_value (memory_nary_access_index access) (map valuation layout))) = Some value).
Proof.
  intros VALID RANGE WORDS POINTER; split.
  - intro RUN; destruct (@window_pointer_load_inverse access bounds lower upper layout valuation ge locals temps memory value VALID RANGE WORDS RUN)
      as [actual_block [actual_base [ACTUAL LOAD]]].
    rewrite POINTER in ACTUAL; inversion ACTUAL; subst; exact LOAD.
  - intro LOAD; eapply window_pointer_load_evaluation; eassumption.
Qed.
Print Assumptions window_pointer_load_correspondence.

Lemma window_pointer_constant_store_execution access bounds lower upper layout valuation fe ge locals temps memory block base payload final :
  window_access_valid bounds lower upper layout access -> interval_ranges bounds (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  temps ! (memory_nary_access_array access) = Some (Vptr block base) ->
  Mem.store Mint32 memory block
    (memory_pointer_buffer_offset base (memory_nary_index_value (memory_nary_access_index access) (map valuation layout)))
    (Vint payload) = Some final ->
  exec_stmt fe ge locals temps memory
    (Sassign (memory_pointer_nary_code access) (Econst_int payload type_int32s)) E0 temps final Out_normal.
Proof.
  intros VALID RANGE WORDS POINTER STORE.
  destruct (@window_pointer_index_evaluation access bounds lower upper layout valuation ge locals temps memory VALID RANGE WORDS) as [INDEX SIGNED].
  eapply exec_Sassign with (loc := block)
    (ofs := Ptrofs.add base (Ptrofs.repr (4*memory_nary_index_value (memory_nary_access_index access) (map valuation layout))))
    (bf := Full) (v := Vint payload) (v2 := Vint payload).
  - unfold memory_pointer_nary_code; eapply memory_pointer_lvalue_evaluation;
      [exact POINTER|apply memory_source_affine_type|exact INDEX|exact SIGNED].
  - constructor.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite memory_pointer_buffer_address.
    pose proof (@memory_pointer_store_end memory final block base
      (memory_nary_index_value (memory_nary_access_index access) (map valuation layout)) (Vint payload) STORE) as END.
    destruct (zle (memory_pointer_buffer_offset base (memory_nary_index_value (memory_nary_access_index access) (map valuation layout))+size_chunk Mint32) Ptrofs.modulus);
      [exact STORE|lia].
Qed.
Print Assumptions window_pointer_constant_store_execution.

Lemma window_pointer_lvalue_inverse access bounds lower upper layout valuation ge locals temps memory block ofs field :
  window_access_valid bounds lower upper layout access -> interval_ranges bounds (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  eval_lvalue ge locals temps memory (memory_pointer_nary_code access) block ofs field ->
  exists base, temps ! (memory_nary_access_array access) = Some (Vptr block base) /\
    ofs = Ptrofs.add base (Ptrofs.repr
      (4*memory_nary_index_value (memory_nary_access_index access) (map valuation layout))) /\ field = Full.
Proof.
  intros VALID RANGE WORDS RUN.
  destruct (@window_pointer_index_evaluation access bounds lower upper layout valuation ge locals temps memory VALID RANGE WORDS)
    as [INDEX SIGNED].
  eapply memory_pointer_lvalue_inverse;
    [apply memory_source_affine_type|apply memory_source_affine_pure|exact INDEX|exact SIGNED|exact RUN].
Qed.
Print Assumptions window_pointer_lvalue_inverse.
