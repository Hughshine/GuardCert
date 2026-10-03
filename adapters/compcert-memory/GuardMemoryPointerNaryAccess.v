From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCountedLoop ClightPureExpr ClightRectangularStore.
From GuardMemory Require Import GuardMemoryPointerAccess GuardMemoryPointerSourceAccess GuardMemoryBufferOffsets
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck GuardMemoryNaryRanges
  GuardMemoryAffineSourceExpressions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The shape is a finite logical address window checked by the compiler.
    It is not an assertion that the caller allocated an array of that size. *)
Definition memory_pointer_nary_code access := memory_pointer_lvalue (memory_nary_access_array access)
  (memory_source_affine_code (memory_nary_access_expression access)).
Lemma memory_pointer_nary_index_evaluation access limits layout valuation ge locals temps memory :
  memory_nary_access_valid limits layout access -> memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  eval_expr ge locals temps memory (memory_source_affine_code (memory_nary_access_expression access))
    (Vint (Int.repr (memory_nary_index_value (memory_nary_access_index access) (map valuation layout)))) /\
  signed_range (memory_nary_index_value (memory_nary_access_index access) (map valuation layout)).
Proof.
  intros [VALID [ENCODE BOUND]] RANGE WORDS; split.
  - eapply memory_nary_index_expression_evaluation; eassumption.
  - eapply rect_index_signed; [exact VALID|apply BOUND; exact RANGE].
Qed.
Lemma memory_pointer_nary_lvalue_inverse access limits layout valuation ge locals temps memory block offset field :
  memory_nary_access_valid limits layout access -> memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  eval_lvalue ge locals temps memory (memory_pointer_nary_code access) block offset field ->
  exists base, temps ! (memory_nary_access_array access) = Some (Vptr block base) /\
    offset = Ptrofs.add base (Ptrofs.repr (4*memory_nary_index_value (memory_nary_access_index access) (map valuation layout))) /\ field = Full.
Proof.
  intros VALID RANGE WORDS RUN.
  destruct (@memory_pointer_nary_index_evaluation access limits layout valuation ge locals temps memory VALID RANGE WORDS) as [INDEX SIGNED].
  eapply memory_pointer_lvalue_inverse; [apply memory_source_affine_type|apply memory_source_affine_pure|exact INDEX|exact SIGNED|exact RUN].
Qed.
Lemma memory_pointer_nary_load_inverse access limits layout valuation ge locals temps memory value :
  memory_nary_access_valid limits layout access -> memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  eval_expr ge locals temps memory (memory_pointer_nary_code access) value ->
  exists block base, temps ! (memory_nary_access_array access) = Some (Vptr block base) /\
    Mem.load Mint32 memory block
      (memory_pointer_buffer_offset base (memory_nary_index_value (memory_nary_access_index access) (map valuation layout))) = Some value.
Proof.
  intros VALID RANGE WORDS RUN.
  destruct (@memory_pointer_nary_index_evaluation access limits layout valuation ge locals temps memory VALID RANGE WORDS) as [INDEX SIGNED].
  eapply memory_pointer_load_inverse; [apply memory_source_affine_type|apply memory_source_affine_pure|exact INDEX|exact SIGNED|exact RUN].
Qed.
Print Assumptions memory_pointer_nary_load_inverse.
