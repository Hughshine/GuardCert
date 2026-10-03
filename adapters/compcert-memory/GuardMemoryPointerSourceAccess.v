From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightPureExpr ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryPointerAccess GuardMemoryBufferOffsets.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_pointer_lvalue_has_base ge locals temps memory pointer index block offset field :
  typeof index = type_int32s ->
  eval_lvalue ge locals temps memory (memory_pointer_lvalue pointer index) block offset field ->
  exists base, temps ! pointer = Some (Vptr block base).
Proof.
  intros TYPE RUN; inversion RUN; subst.
  match goal with POINTER : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ => inversion POINTER; subst end;
    try match goal with BAD : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion BAD end.
  match goal with PTR : eval_expr _ _ _ _ (Etempvar _ _) _ |- _ => inversion PTR; subst end.
  all: try match goal with BAD : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion BAD end.
  match goal with SEM : sem_binary_operation _ _ ?left _ ?right _ _ = Some _ |- _ =>
    cbn [typeof] in SEM; rewrite TYPE in SEM; destruct left,right;
    cbn [sem_binary_operation sem_add classify_add sem_add_ptr_int] in SEM;
    try discriminate SEM; try (destruct Archi.ptr64; discriminate SEM);
    inversion SEM; subst; eauto end.
Qed.
Lemma memory_pointer_load_evaluation ge locals temps memory pointer block base index offset value :
  temps ! pointer = Some (Vptr block base) -> typeof index = type_int32s ->
  eval_expr ge locals temps memory index (Vint (Int.repr offset)) -> signed_range offset ->
  Mem.load Mint32 memory block (memory_pointer_buffer_offset base offset) = Some value ->
  eval_expr ge locals temps memory (memory_pointer_lvalue pointer index) value.
Proof.
  intros POINTER TYPE INDEX RANGE LOAD; eapply eval_Elvalue;
    [eapply memory_pointer_lvalue_evaluation; eassumption|].
  apply deref_loc_value with (chunk := Mint32); [reflexivity|].
  cbn [Mem.loadv]; rewrite memory_pointer_buffer_address.
  pose proof (@memory_pointer_load_end memory block base offset value LOAD) as END.
  destruct (zle (memory_pointer_buffer_offset base offset+size_chunk Mint32) Ptrofs.modulus); [exact LOAD|lia].
Qed.
Lemma memory_pointer_load_inverse ge locals temps memory pointer index offset value :
  typeof index = type_int32s -> pure_scalar index ->
  eval_expr ge locals temps memory index (Vint (Int.repr offset)) -> signed_range offset ->
  eval_expr ge locals temps memory (memory_pointer_lvalue pointer index) value ->
  exists block base, temps ! pointer = Some (Vptr block base) /\
    Mem.load Mint32 memory block (memory_pointer_buffer_offset base offset) = Some value.
Proof.
  intros TYPE PURE INDEX RANGE RUN; inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ _ _ (memory_pointer_lvalue _ _) _ _ _ |- _ =>
    destruct (@memory_pointer_lvalue_inverse ge locals temps memory pointer index offset _ _ _ TYPE PURE INDEX RANGE LVALUE)
      as [base [POINTER [OFFSET FIELD]]]; subst end.
  match goal with DEREF : deref_loc _ _ _ _ _ _ |- _ => inversion DEREF; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with LOAD : Mem.loadv _ _ _ = Some _ |- _ =>
    cbn [Mem.loadv] in LOAD; rewrite memory_pointer_buffer_address in LOAD;
    destruct (zle (memory_pointer_buffer_offset base offset+size_chunk Mint32) Ptrofs.modulus); try discriminate LOAD end; eauto.
Qed.
Print Assumptions memory_pointer_lvalue_has_base.
Print Assumptions memory_pointer_load_inverse.
