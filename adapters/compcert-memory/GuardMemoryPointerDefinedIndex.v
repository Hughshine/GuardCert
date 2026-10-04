From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From GuardMemory Require Import GuardMemoryPointerAccess GuardMemoryAffineSourceExpressions.
Import ListNotations.
Set Implicit Arguments.

Lemma memory_pointer_lvalue_index_word ge locals temps memory pointer index block offset field :
  typeof index = type_int32s ->
  eval_lvalue ge locals temps memory (memory_pointer_lvalue pointer index) block offset field ->
  exists word, eval_expr ge locals temps memory index (Vint word).
Proof.
  intros TYPE RUN; inversion RUN; subst.
  match goal with POINTER : eval_expr _ _ _ _ (Ebinop Oadd _ _ _) _ |- _ => inversion POINTER; subst end;
    try match goal with BAD : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion BAD end.
  match goal with SEM : sem_binary_operation _ _ ?left _ ?right _ _ = Some _ |- _ =>
    cbn [typeof] in SEM; rewrite TYPE in SEM; destruct left,right;
    cbn [sem_binary_operation sem_add classify_add sem_add_ptr_int] in SEM;
    try discriminate SEM; try (destruct Archi.ptr64; discriminate SEM); eauto end.
Qed.

Theorem memory_pointer_source_affine_used_word expression ge locals temps memory pointer block offset field :
  eval_lvalue ge locals temps memory
    (memory_pointer_lvalue pointer (memory_source_affine_code expression)) block offset field ->
  forall identifier, In identifier (memory_source_affine_reads expression) ->
    exists word, temps ! identifier = Some (Vint word).
Proof.
  intro RUN; destruct (@memory_pointer_lvalue_index_word ge locals temps memory pointer
    (memory_source_affine_code expression) block offset field (memory_source_affine_type expression) RUN) as [word INDEX].
  eapply memory_source_affine_defined_words; exact INDEX.
Qed.
Print Assumptions memory_pointer_source_affine_used_word.

Theorem memory_pointer_source_load_used_word expression ge locals temps memory pointer value :
  eval_expr ge locals temps memory
    (memory_pointer_lvalue pointer (memory_source_affine_code expression)) value ->
  forall identifier, In identifier (memory_source_affine_reads expression) ->
    exists word, temps ! identifier = Some (Vint word).
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ _ _ (memory_pointer_lvalue _ _) _ _ _ |- _ =>
    eapply memory_pointer_source_affine_used_word; exact LVALUE end.
Qed.
Print Assumptions memory_pointer_source_load_used_word.
