From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr ClightCountedLoop ClightTempFrame ClightLoopSyntax ClightRegionProgress ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryArrayBackend GuardMemoryFlatArrayBackend
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck GuardMemoryNaryRanges
  GuardMemoryNaryCompute GuardMemorySourceValueInterface GuardMemoryPointerAccess GuardMemoryPointerNaryAccess GuardMemoryBufferOffsets.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_pointer_register_codes layout := map (fun identifier => Etempvar identifier type_int32s) layout.
Lemma memory_pointer_register_operands ge locals temps memory layout valuation :
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  Forall2 (MemoryBody.operand_view ge locals temps memory) (memory_pointer_register_codes layout) (map valuation layout).
Proof.
  intro WORDS; induction layout as [|identifier layout IH]; cbn [memory_pointer_register_codes map]; constructor.
  - split; [reflexivity|constructor; apply WORDS; cbn; auto].
  - apply IH; intros key MEMBER; apply WORDS; cbn; auto.
Qed.
Lemma memory_pointer_register_types layout :
  Forall (fun code => typeof code = type_int32s) (memory_pointer_register_codes layout).
Proof. apply Forall_map,Forall_forall; intros; reflexivity. Qed.
Lemma memory_pointer_register_pure layout : Forall pure_scalar (memory_pointer_register_codes layout).
Proof. apply Forall_map,Forall_forall; intros; constructor. Qed.
Definition memory_pointer_compute_statement operation :=
  Sassign (memory_pointer_nary_code (memory_nary_compute_write operation)) (memory_nary_compute_source operation).
Definition memory_pointer_access_valid limits layout pointer extent access :=
  memory_nary_access_valid limits layout access /\ memory_nary_access_array access = pointer /\
    rectangle_extent (memory_nary_access_shape access) = extent.
Definition memory_pointer_compute_valid limits layout pointer extent operation :=
  memory_pointer_access_valid limits layout pointer extent (memory_nary_compute_write operation) /\
  Forall (memory_pointer_access_valid limits layout pointer extent) (memory_nary_compute_reads operation) /\
  compile_flat_value (memory_pointer_register_codes layout) (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation) = Some (memory_nary_compute_source operation) /\
  memory_source_reads_check (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation) = true.
Definition memory_pointer_access_loaded block base values memory access value :=
  Mem.load Mint32 memory block (memory_pointer_buffer_offset base (memory_nary_index_value (memory_nary_access_index access) values)) = Some value.
Definition memory_pointer_compute_physical block base values operation before after :=
  exists loaded value,
    Forall2 (memory_pointer_access_loaded block base values before) (memory_nary_compute_reads operation) loaded /\
    evaluate_value values loaded (instruction_value (memory_nary_compute_instruction operation)) = Some value /\
    Mem.store Mint32 before block (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) values)) value = Some after.

Lemma memory_pointer_source_read_decode limits layout pointer extent accesses ge locals temps memory valuation block base :
  Forall (memory_pointer_access_valid limits layout pointer extent) accesses ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  temps ! pointer = Some (Vptr block base) ->
  forall access value, In access accesses -> eval_expr ge locals temps memory (memory_pointer_nary_code access) value ->
  memory_pointer_access_loaded block base (map valuation layout) memory access value.
Proof.
  intros CERT RANGE WORDS POINTER access value MEMBER RUN.
  apply Forall_forall with (x := access) in CERT; [|exact MEMBER].
  destruct CERT as [VALID [ID EXTENT]].
  destruct (@memory_pointer_nary_load_inverse access limits layout valuation ge locals temps memory value VALID RANGE WORDS RUN)
    as [actual [offset [BOUND LOAD]]].
  rewrite ID,POINTER in BOUND; inversion BOUND; subst actual offset; exact LOAD.
Qed.

Lemma memory_pointer_source_read_list_decode limits layout pointer extent accesses ge locals temps memory valuation block base read_codes :
  Forall (memory_pointer_access_valid limits layout pointer extent) accesses ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  temps ! pointer = Some (Vptr block base) -> forall loaded,
  Forall2 (fun code value => In code read_codes /\ eval_expr ge locals temps memory code value)
    (map memory_pointer_nary_code accesses) loaded ->
  Forall2 (memory_pointer_access_loaded block base (map valuation layout) memory) accesses loaded.
Proof.
  intros CERT RANGE WORDS POINTER; induction CERT as [|access accesses [VALID [ID EXTENT]] CERT IH];
    intros loaded LOADS; cbn [map] in LOADS; inversion LOADS; subst; constructor.
  - match goal with READ : In _ read_codes /\ eval_expr _ _ _ _ _ _ |- _ => destruct READ as [_ RUN] end.
    destruct (@memory_pointer_nary_load_inverse access limits layout valuation ge locals temps memory _ VALID RANGE WORDS RUN)
      as [actual [offset [BOUND LOAD]]].
    try rewrite ID in BOUND; rewrite POINTER in BOUND; inversion BOUND; subst actual offset; exact LOAD.
  - apply IH; assumption.
Qed.

Theorem memory_pointer_compute_inverse limits layout pointer extent operation fe ge locals temps memory after final valuation block base :
  memory_pointer_compute_valid limits layout pointer extent operation ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  temps ! pointer = Some (Vptr block base) ->
  exec_stmt fe ge locals temps memory (memory_pointer_compute_statement operation) E0 after final Out_normal ->
  memory_pointer_compute_physical block base (map valuation layout) operation memory final /\ after = temps.
Proof.
  intros [[WRITE [WID WEXTENT]] [READS [COMPILE REFERENCED]]] RANGE WORDS POINTER RUN.
  assert (WID_PROOF : True -> memory_nary_access_array (memory_nary_compute_write operation) = pointer) by auto.
  clear WID WEXTENT.
  assert (READ_TYPES : Forall (fun code => typeof code = type_int32s)
    (map memory_pointer_nary_code (memory_nary_compute_reads operation))).
  { apply Forall_map,Forall_forall; intros; reflexivity. }
  assert (TYPE : typeof (memory_nary_compute_source operation) = type_int32s)
    by (eapply memory_source_flat_type; [apply memory_pointer_register_types|exact READ_TYPES|exact COMPILE]).
  inversion RUN; subst after.
  match goal with LVALUE : eval_lvalue _ _ ?current _ (memory_pointer_nary_code _) _ _ _ |- _ =>
    destruct (@memory_pointer_nary_lvalue_inverse (memory_nary_compute_write operation) limits layout valuation ge locals current memory _ _ _
      WRITE RANGE WORDS LVALUE) as [offset [BINDING [OFFSET FIELD]]]; subst end.
  rewrite (WID_PROOF I),POINTER in BINDING; inversion BINDING; subst loc offset.
  match goal with CAST : sem_cast ?old _ _ _ = Some _ |- _ =>
    rewrite TYPE in CAST; destruct old; try discriminate CAST; inversion CAST; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion ASSIGN; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE : Mem.storev _ _ _ _ = Some _ |- _ =>
    cbn [Mem.storev] in STORE; rewrite memory_pointer_buffer_address in STORE;
    destruct (zle (memory_pointer_buffer_offset base
      (memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) (map valuation layout))+
      size_chunk Mint32) Ptrofs.modulus); try discriminate STORE end.
  let read_codes := constr:(map memory_pointer_nary_code (memory_nary_compute_reads operation)) in
  let relation := constr:(fun code value => In code read_codes /\ eval_expr ge locals temps memory code value) in
  assert (UNIQUE : forall code first second, relation code first -> relation code second -> first = second).
  { intros code first second [MEMBER FIRST] [_ SECOND].
    apply in_map_iff in MEMBER as [access [CODE MEMBER]]; subst code.
    pose proof (@memory_pointer_source_read_decode limits layout pointer extent (memory_nary_compute_reads operation)
      ge locals temps memory valuation block base READS RANGE WORDS POINTER access first MEMBER FIRST) as LOAD1.
    pose proof (@memory_pointer_source_read_decode limits layout pointer extent (memory_nary_compute_reads operation)
      ge locals temps memory valuation block base READS RANGE WORDS POINTER access second MEMBER SECOND) as LOAD2.
    unfold memory_pointer_access_loaded in LOAD1,LOAD2; congruence. }
  match goal with VALUE : eval_expr _ _ ?current _ (memory_nary_compute_source operation) (Vint ?word) |- _ =>
    destruct (@memory_source_value_inverse ge locals current memory (memory_pointer_register_codes layout)
      (map memory_pointer_nary_code (memory_nary_compute_reads operation))
      (fun code value => In code (map memory_pointer_nary_code (memory_nary_compute_reads operation)) /\
        eval_expr ge locals current memory code value)
      (memory_pointer_register_types layout) READ_TYPES ltac:(intros; split; assumption) UNIQUE
      (map valuation layout) (memory_nary_compute_value operation) (memory_nary_compute_source operation) word
      (memory_pointer_register_pure layout) (@memory_pointer_register_operands ge locals current memory layout valuation WORDS)
      REFERENCED COMPILE VALUE) as [loaded [LOADS COMPUTE]] end.
  assert (PHYSICAL : Forall2 (memory_pointer_access_loaded block base (map valuation layout) memory)
    (memory_nary_compute_reads operation) loaded).
  { eapply memory_pointer_source_read_list_decode; eassumption. }
  split; [|reflexivity]; match type of COMPUTE with _ = Some ?computed => exists loaded,computed end; split; [exact PHYSICAL|]; split; [|assumption].
  cbn [instruction_value memory_nary_compute_instruction evaluate_value]; rewrite COMPUTE; cbn; rewrite Int.add_zero; reflexivity.
Qed.
Print Assumptions memory_pointer_compute_inverse.
