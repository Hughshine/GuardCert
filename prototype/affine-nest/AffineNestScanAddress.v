From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryBufferOffsets GuardMemoryPointerAccess
  GuardMemoryMultiPointerCells GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities GuardMemoryPointerCellComparison
  GuardMemoryAffineSourceExpressions GuardMemoryAffineRenaming GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestScanWords.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_scan_address pointer values expression :=
  Ebinop Oadd(Etempvar pointer(Tpointer type_int32s noattr))
    (memory_source_affine_code(memory_source_affine_rename values expression))(Tpointer type_int32s noattr).

Theorem affine_scan_address_binding expression values valuation ge locals original current memory lower upper pointer :
  signed_range lower -> signed_range(upper-1) -> current!pointer=original!pointer ->
  (forall identifier, In identifier(memory_source_affine_reads expression) ->
    current!(values identifier)=Some(Vint(Int.repr(valuation identifier)))) ->
  memory_cell_capable(window_multi_pointer_locations original lower upper) memory
    (point_cell pointer(memory_source_affine_math valuation expression)) ->
  memory_cell_address_binding(fun _=>affine_scan_address pointer values expression)
    (window_multi_pointer_locations original lower upper)(Entry ge locals current memory)
    (point_cell pointer(memory_source_affine_math valuation expression)).
Proof.
  intros LOWER UPPER FRAME WORDS [location [RESOLVE [CHUNK [VALID ALIGN]]]].
  set(index:=memory_source_affine_math valuation expression) in *.
  destruct(@window_multi_pointer_location_inverse original lower upper(point_cell pointer index) location RESOLVE)
    as [block [base [position [POINTER [CELL [RANGE SAME]]]]]].
  cbn [arr_index point_cell] in CELL; inversion CELL; subst position location.
  cbn [arr_id point_cell] in POINTER.
  assert(INDEX:signed_range index) by(unfold signed_range in *; lia).
  exists(MemoryLocation Mint32 block(memory_pointer_buffer_offset base index)),
    (Ptrofs.add base(Ptrofs.repr(4*index))).
  split; [exact RESOLVE|]; split; [reflexivity|].
  split; [cbn; symmetry; apply memory_pointer_buffer_address|].
  split.
  - unfold affine_scan_address; constructor; [constructor|apply memory_source_affine_pure].
  - split; [reflexivity|]; split.
    + unfold affine_scan_address; eapply eval_Ebinop with(v1:=Vptr block base)(v2:=Vint(Int.repr index)).
      * constructor; cbn [entry_temps]; rewrite FRAME; exact POINTER.
      * apply affine_scan_expression_evaluation; exact WORDS.
      * rewrite memory_source_affine_type; apply memory_pointer_add; exact INDEX.
    + rewrite memory_pointer_buffer_address; exact(conj VALID ALIGN).
Qed.
Print Assumptions affine_scan_address_binding.
