From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightPureExpr ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryBufferOffsets
  GuardMemoryArrayBackend GuardMemoryFlatArrayBackend GuardMemoryRectangles.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_pointer_lvalue pointer index :=
  Ederef (Ebinop Oadd (Etempvar pointer (Tpointer type_int32s noattr)) index
    (Tpointer type_int32s noattr)) type_int32s.
Lemma memory_pointer_add ge memory block base index : signed_range index ->
  sem_binary_operation ge Oadd (Vptr block base) (Tpointer type_int32s noattr)
    (Vint (Int.repr index)) type_int32s memory =
    Some (Vptr block (Ptrofs.add base (Ptrofs.repr (4*index)))).
Proof.
  intro RANGE.
  change (Some (Vptr block (Ptrofs.add base
    (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.repr (Int.signed (Int.repr index)))))) =
    Some (Vptr block (Ptrofs.add base (Ptrofs.repr (4*index))))).
  rewrite Int.signed_repr by exact RANGE.
  unfold Ptrofs.mul.
  apply f_equal; apply f_equal; apply f_equal.
  apply Ptrofs.eqm_samerepr; apply Ptrofs.eqm_mult;
    apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.
Lemma memory_pointer_lvalue_evaluation ge locals temps memory pointer block base index offset :
  temps ! pointer = Some (Vptr block base) -> typeof index = type_int32s ->
  eval_expr ge locals temps memory index (Vint (Int.repr offset)) -> signed_range offset ->
  eval_lvalue ge locals temps memory (memory_pointer_lvalue pointer index)
    block (Ptrofs.add base (Ptrofs.repr (4*offset))) Full.
Proof.
  intros POINTER TYPE INDEX RANGE; apply eval_Ederef.
  eapply eval_Ebinop with (v1 := Vptr block base) (v2 := Vint (Int.repr offset));
    [constructor; exact POINTER|exact INDEX|].
  cbn [typeof]; rewrite TYPE; apply memory_pointer_add; exact RANGE.
Qed.
Lemma memory_pointer_lvalue_inverse ge locals temps memory pointer index offset block ofs field :
  typeof index = type_int32s -> pure_scalar index ->
  eval_expr ge locals temps memory index (Vint (Int.repr offset)) -> signed_range offset ->
  eval_lvalue ge locals temps memory (memory_pointer_lvalue pointer index) block ofs field ->
  exists base, temps ! pointer = Some (Vptr block base) /\
    ofs = Ptrofs.add base (Ptrofs.repr (4*offset)) /\ field = Full.
Proof.
  intros TYPE PURE INDEX RANGE RUN; inversion RUN; subst.
  match goal with POINTER : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ => inversion POINTER; subst end;
    try match goal with BAD : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion BAD end.
  match goal with PTR : eval_expr _ _ _ _ (Etempvar _ _) _,
    ACTUAL : eval_expr _ _ _ _ index ?idx |- _ =>
    inversion PTR; subst;
    pose proof (@pure_scalar_determinate index PURE ge locals temps memory idx
      (Vint (Int.repr offset)) ACTUAL INDEX) as SAME; subst idx end.
  match goal with SEM : sem_binary_operation _ _ _ _ _ _ _ = Some _ |- _ =>
    cbn [typeof] in SEM; rewrite TYPE in SEM;
    destruct v1; try discriminate SEM;
    rewrite (@memory_pointer_add ge memory b i offset RANGE) in SEM;
    inversion SEM; subst end; eauto.
  all: try (destruct Archi.ptr64; discriminate).
  all: match goal with BAD : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion BAD end.
Qed.
Lemma memory_pointer_offset_range base index :
  0 <= memory_pointer_buffer_offset base index <= Ptrofs.max_unsigned.
Proof.
  unfold memory_pointer_buffer_offset,memory_buffer_offset,Ptrofs.max_unsigned.
  pose proof Ptrofs.modulus_pos; pose proof (Z.mod_pos_bound (Ptrofs.unsigned base+4*index) Ptrofs.modulus ltac:(lia)); lia.
Qed.
Lemma memory_pointer_aligned_end offset : 0 <= offset <= Ptrofs.max_unsigned ->
  (4 | offset) -> offset+size_chunk Mint32 <= Ptrofs.modulus.
Proof.
  intros RANGE [cells CELLS]; destruct memory_pointer_modulus_cells as [size SIZE].
  change (size_chunk Mint32) with 4; unfold Ptrofs.max_unsigned in RANGE; nia.
Qed.
Lemma memory_pointer_load_end memory block base index value :
  Mem.load Mint32 memory block (memory_pointer_buffer_offset base index) = Some value ->
  memory_pointer_buffer_offset base index+size_chunk Mint32 <= Ptrofs.modulus.
Proof.
  intro LOAD; apply memory_pointer_aligned_end; [apply memory_pointer_offset_range|].
  exact (proj2 (Mem.load_valid_access _ _ _ _ _ LOAD)).
Qed.
Lemma memory_pointer_store_end memory final block base index value :
  Mem.store Mint32 memory block (memory_pointer_buffer_offset base index) value = Some final ->
  memory_pointer_buffer_offset base index+size_chunk Mint32 <= Ptrofs.modulus.
Proof.
  intro STORE; apply memory_pointer_aligned_end; [apply memory_pointer_offset_range|].
  exact (proj2 (Mem.store_valid_access_3 _ _ _ _ _ _ STORE)).
Qed.
Lemma memory_pointer_buffer_location_inverse array block base extent index location :
  memory_pointer_buffer_locations array block base extent (point_cell array index) = Some location ->
  0 <= index < extent /\ location = MemoryLocation Mint32 block (memory_pointer_buffer_offset base index).
Proof.
  unfold memory_pointer_buffer_locations; cbn [point_cell arr_id arr_index]; rewrite Pos.eqb_refl.
  destruct ((0 <=? index) && (index <? extent)) eqn:RANGE; [|discriminate].
  rewrite andb_true_iff,Z.leb_le,Z.ltb_lt in RANGE; intro LOCATION; inversion LOCATION; auto.
Qed.
Lemma memory_pointer_buffer_location_at array block base extent index : 0 <= index < extent ->
  memory_pointer_buffer_locations array block base extent (point_cell array index) =
    Some (MemoryLocation Mint32 block (memory_pointer_buffer_offset base index)).
Proof.
  intro RANGE; unfold memory_pointer_buffer_locations; cbn [point_cell arr_id arr_index]; rewrite Pos.eqb_refl.
  assert (CHECK : (0 <=? index) && (index <? extent) = true) by (rewrite andb_true_iff,Z.leb_le,Z.ltb_lt; exact RANGE).
  rewrite CHECK; reflexivity.
Qed.
Print Assumptions memory_pointer_lvalue_inverse.
Print Assumptions memory_pointer_store_end.
