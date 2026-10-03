From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightPureExpr ClightCountedLoop ClightTempFrame ClightLoopSyntax ClightRegionProgress ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryArrayBackend GuardMemoryFlatArrayBackend
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck GuardMemoryNaryRanges
  GuardMemoryNaryCompute GuardMemorySourceValueInterface GuardMemoryPointerAccess GuardMemoryPointerNaryAccess GuardMemoryBufferOffsets.
From GuardMemory Require Import GuardMemoryPointerCompute GuardMemoryScalarAccess GuardMemorySourceParameters.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_scalar_pointer_compute_valid limits layout scalars pointer extent operation :=
  memory_pointer_access_valid limits layout pointer extent (memory_nary_compute_write operation) /\
  Forall (memory_pointer_access_valid limits layout pointer extent) (memory_nary_compute_reads operation) /\
  compile_flat_value (memory_pointer_register_codes (layout++scalars))
    (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation) = Some (memory_nary_compute_source operation) /\
  memory_source_reads_check (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation) = true.
Lemma memory_scalar_pointer_reads_prefix limits layout scalars pointer extent accesses memory valuation block base :
  Forall (memory_pointer_access_valid limits layout pointer extent) accesses -> forall loaded,
  Forall2 (memory_pointer_access_loaded block base (map valuation layout) memory) accesses loaded ->
  Forall2 (memory_pointer_access_loaded block base (map valuation (layout++scalars)) memory) accesses loaded.
Proof.
  intro CERT; induction CERT as [|access accesses [[VALID [ENCODE BOUND]] REST] CERT IH]; intros loaded LOADS;
    inversion LOADS; subst; constructor.
  - unfold memory_pointer_access_loaded; rewrite map_app,memory_scalar_index_value.
    + assumption.
    + rewrite (@memory_encode_nary_index_length layout _ _ ENCODE),length_map; reflexivity.
  - apply IH; assumption.
Qed.
Theorem memory_scalar_pointer_compute_inverse limits layout scalars pointer extent operation fe ge locals temps memory after final valuation block base :
  memory_scalar_pointer_compute_valid limits layout scalars pointer extent operation ->
  memory_nary_ranges limits (map valuation layout) ->
  (forall identifier, In identifier (layout++scalars) -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))) ->
  temps ! pointer = Some (Vptr block base) ->
  exec_stmt fe ge locals temps memory (memory_pointer_compute_statement operation) E0 after final Out_normal ->
  memory_pointer_compute_physical block base (map valuation (layout++scalars)) operation memory final /\ after = temps.
Proof.
  intros [[WRITE [WID WEXTENT]] [READS [COMPILE REFERENCED]]] RANGE WORDS_ALL POINTER RUN.
  assert (WORDS : forall identifier, In identifier layout -> temps ! identifier = Some (Vint (Int.repr (valuation identifier)))).
  { intros identifier MEMBER; apply WORDS_ALL; apply in_or_app; left; exact MEMBER. }
  assert (WINDEX : memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation))
    (map valuation (layout++scalars)) = memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation))
    (map valuation layout)).
  { rewrite map_app,memory_scalar_index_value; [reflexivity|].
    rewrite (@memory_encode_nary_index_length layout _ _ (proj1 (proj2 WRITE))),length_map; reflexivity. }
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
    destruct (@memory_source_value_inverse ge locals current memory (memory_pointer_register_codes (layout++scalars))
      (map memory_pointer_nary_code (memory_nary_compute_reads operation))
      (fun code value => In code (map memory_pointer_nary_code (memory_nary_compute_reads operation)) /\
        eval_expr ge locals current memory code value)
      (memory_pointer_register_types (layout++scalars)) READ_TYPES ltac:(intros; split; assumption) UNIQUE
      (map valuation (layout++scalars)) (memory_nary_compute_value operation) (memory_nary_compute_source operation) word
      (memory_pointer_register_pure (layout++scalars)) (@memory_pointer_register_operands ge locals current memory (layout++scalars) valuation WORDS_ALL)
      REFERENCED COMPILE VALUE) as [loaded [LOADS COMPUTE]] end.
  assert (PHYSICAL : Forall2 (memory_pointer_access_loaded block base (map valuation layout) memory)
    (memory_nary_compute_reads operation) loaded).
  { eapply memory_pointer_source_read_list_decode; eassumption. }
  assert (FULL_LOADS : Forall2 (memory_pointer_access_loaded block base (map valuation (layout++scalars)) memory)
    (memory_nary_compute_reads operation) loaded).
  { eapply memory_scalar_pointer_reads_prefix; [exact READS|exact PHYSICAL]. }
  split; [|reflexivity]; match type of COMPUTE with _ = Some ?computed => exists loaded,computed end; split; [exact FULL_LOADS|]; split;
    [|rewrite WINDEX; assumption].
  cbn [instruction_value memory_nary_compute_instruction evaluate_value]; rewrite COMPUTE; cbn; rewrite Int.add_zero; reflexivity.
Qed.
Print Assumptions memory_scalar_pointer_compute_inverse.

Theorem memory_scalar_pointer_used_register limits layout scalars pointer extent operation fe ge locals temps memory after final identifier index :
  memory_scalar_pointer_compute_valid limits layout scalars pointer extent operation ->
  nth_error (layout++scalars) index = Some identifier ->
  In index (memory_source_parameter_positions (memory_nary_compute_value operation)) ->
  exec_stmt fe ge locals temps memory (memory_pointer_compute_statement operation) E0 after final Out_normal ->
  exists word, temps ! identifier = Some (Vint word).
Proof.
  intros [WRITE [READS [COMPILE REFERENCED]]] LOOKUP USED RUN.
  assert (READ_TYPES : Forall (fun code => typeof code = type_int32s)
    (map memory_pointer_nary_code (memory_nary_compute_reads operation))).
  { apply Forall_map,Forall_forall; intros; reflexivity. }
  assert (TYPE : typeof (memory_nary_compute_source operation) = type_int32s)
    by (eapply memory_source_flat_type; [apply memory_pointer_register_types|exact READ_TYPES|exact COMPILE]).
  inversion RUN; subst after.
  match goal with CAST : sem_cast ?old _ _ _ = Some _ |- _ =>
    rewrite TYPE in CAST; destruct old; try discriminate CAST; inversion CAST; subst end.
  eapply memory_source_used_register_typed; eassumption.
Qed.
Print Assumptions memory_scalar_pointer_used_register.
