From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightPureExpr ClightSyntaxEquality ClightNoWrap ClightCountedLoop ClightTempFrame
  CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryArrayBackend
  GuardMemoryFlatArrayBackend GuardMemoryBufferOffsets GuardMemoryPointerAccess GuardMemoryPointerSourceAccess
  GuardMemoryPointerCompute GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryAffineSourceExpressions
  GuardMemorySourceValueInterface GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend
  GuardMemoryTensorSource GuardMemoryMultiTensorBackend.
From GuardInterface Require Import ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition multi_tensor_source_access dimensions layout := (ident*tensor_source_access dimensions layout)%type.
Definition multi_tensor_source_lvalue dimensions layout(access:multi_tensor_source_access dimensions layout) :=
  memory_pointer_lvalue(fst access)(tensor_source_index(snd access)).
Definition multi_tensor_source_terms dimensions layout(access:multi_tensor_source_access dimensions layout) :=
  (fst access,tensor_source_terms(snd access)).
Definition multi_tensor_source_available dimensions layout(access:multi_tensor_source_access dimensions layout) values sizes :=
  tensor_source_access_available(snd access)values sizes.
Arguments multi_tensor_source_lvalue {dimensions layout} access.
Arguments multi_tensor_source_terms {dimensions layout} access.
Arguments multi_tensor_source_available {dimensions layout} access values sizes.

(** This inverse obtains the needed pointer binding from the actual successful
    source read. Unused pointer temporaries need no entry typing assumption. *)
Theorem multi_tensor_source_read_inverse dimensions layout(access:multi_tensor_source_access dimensions layout)
    ge locals temps memory valuation sizes offset value :
  tensor_layout_flag sizes=true -> tensor_dimension_view dimensions sizes temps ->
  (forall id,In id layout -> temps!id=Some(Vint(Int.repr(valuation id)))) ->
  tensor_index sizes(affine_product(tensor_source_terms(snd access))(map valuation layout))=Some offset ->
  eval_expr ge locals temps memory(multi_tensor_source_lvalue access)value ->
  exists block base,temps!(fst access)=Some(Vptr block base) /\
    Mem.load Mint32 memory block(memory_pointer_buffer_offset base offset)=Some value.
Proof.
  intros LAYOUT DIMENSIONS WORDS INDEX RUN.
  unfold multi_tensor_source_lvalue in RUN.
  eapply memory_pointer_load_inverse; [apply tensor_source_access_type|apply tensor_source_access_pure| | |exact RUN].
  - eapply tensor_source_access_evaluation; eassumption.
  - pose proof(@tensor_index_bounds sizes _ offset INDEX).
    pose proof(@tensor_layout_flag_sound sizes LAYOUT); unfold signed_range; pose proof Int.min_signed_neg; lia.
Qed.

Record multi_tensor_source_operation dimensions layout(source:statement) := MultiTensorSourceOperation {
  mts_write:multi_tensor_source_access dimensions layout;
  mts_reads:list(multi_tensor_source_access dimensions layout);
  mts_value:value_expression;
  mts_rhs:expr;
  mts_rhs_compile:compile_flat_value(memory_pointer_register_codes layout)
    (map multi_tensor_source_lvalue mts_reads)mts_value=Some mts_rhs;
  mts_reads_used:memory_source_reads_check(map multi_tensor_source_lvalue mts_reads)mts_value=true;
  mts_exact:source=Sassign(multi_tensor_source_lvalue mts_write)mts_rhs
}.
Definition multi_tensor_source_instruction dimensions layout source
    (operation:multi_tensor_source_operation dimensions layout source) :=
  MemoryInstruction(multi_tensor_source_terms(mts_write operation))
    (map multi_tensor_source_terms(mts_reads operation))(mts_value operation).

Definition check_multi_tensor_source_operation dimensions layout source
    (write:multi_tensor_source_access dimensions layout)(reads:list(multi_tensor_source_access dimensions layout))(value:value_expression) :
  option(multi_tensor_source_operation dimensions layout source).
Proof.
  destruct(compile_flat_value(memory_pointer_register_codes layout)(map multi_tensor_source_lvalue reads)value)
    as [rhs|]eqn:RHS; [|exact None].
  destruct(memory_source_reads_check(map multi_tensor_source_lvalue reads)value)eqn:USED; [|exact None].
  destruct(statement_eq source(Sassign(multi_tensor_source_lvalue write)rhs))as [EXACT|]; [|exact None].
  exact(Some(@MultiTensorSourceOperation dimensions layout source write reads value rhs RHS USED EXACT)).
Defined.

Lemma multi_tensor_source_reads_resolve dimensions layout ge locals temps memory valuation sizes
    (accesses:list(multi_tensor_source_access dimensions layout))loaded :
  tensor_layout_flag sizes=true -> tensor_dimension_view dimensions sizes temps ->
  (forall id,In id layout -> temps!id=Some(Vint(Int.repr(valuation id)))) ->
  Forall(fun access=>multi_tensor_source_available access(map valuation layout)sizes)accesses ->
  Forall2(fun code value=>eval_expr ge locals temps memory code value)(map multi_tensor_source_lvalue accesses)loaded ->
  exists locations,resolve_cells(map(fun access=>exact_cell(multi_tensor_source_terms access)(map valuation layout))accesses)
    (multi_tensor_locations temps sizes)=Some locations /\ load_locations locations memory=Some loaded.
Proof.
  intros LAYOUT DIMENSIONS WORDS COVER; revert loaded;
    induction COVER as [|access accesses [offset INDEX] COVER IH]; intros loaded LOADS; cbn [map]in LOADS; inversion LOADS; subst.
  - exists []; split; reflexivity.
  - destruct(IH _ ltac:(eassumption))as [locations [RESOLVE LOAD]].
    match goal with READ:eval_expr _ _ _ _ (multi_tensor_source_lvalue access) ?value |- _=>
      destruct(@multi_tensor_source_read_inverse dimensions layout access ge locals temps memory valuation sizes offset value
        LAYOUT DIMENSIONS WORDS INDEX READ)as [block [base [POINTER VALUE]]] end.
    assert(LOCATION:multi_tensor_locations temps sizes
      (exact_cell(multi_tensor_source_terms access)(map valuation layout))=
      Some(MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset))).
    { apply multi_tensor_location_at; [exact POINTER|exact INDEX]. }
    exists(MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset)::locations); split.
    + cbn [map resolve_cells]; rewrite LOCATION,RESOLVE; reflexivity.
    + cbn [load_locations]; unfold location_load; cbn [location_chunk location_block location_offset].
      rewrite VALUE,LOAD; reflexivity.
Qed.

Theorem multi_tensor_source_operation_decode dimensions layout source
    (operation:multi_tensor_source_operation dimensions layout source)fe ge locals temps memory after final valuation sizes :
  tensor_layout_flag sizes=true -> tensor_dimension_view dimensions sizes temps ->
  (forall id,In id layout -> temps!id=Some(Vint(Int.repr(valuation id)))) ->
  Forall(fun access=>multi_tensor_source_available access(map valuation layout)sizes)(mts_write operation::mts_reads operation) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_nary_point(multi_tensor_source_instruction operation)(map valuation layout)
    (RuntimeState(multi_tensor_locations temps sizes)memory)(RuntimeState(multi_tensor_locations temps sizes)final) /\ after=temps.
Proof.
  intros LAYOUT DIMENSIONS WORDS COVER RUN.
  inversion COVER as [|write reads [offset INDEX] READS]; subst write reads.
  assert(TYPE:typeof(mts_rhs operation)=type_int32s).
  { eapply memory_source_flat_type; [apply memory_pointer_register_types| |exact(mts_rhs_compile operation)].
    apply Forall_map,Forall_forall; intros; reflexivity. }
  rewrite(mts_exact operation)in RUN; unfold multi_tensor_source_lvalue in RUN; inversion RUN; subst after.
  match goal with LVALUE:eval_lvalue _ _ _ _ (memory_pointer_lvalue _ _) _ _ _ |- _=>
    destruct(@memory_pointer_lvalue_inverse ge locals temps memory(fst(mts_write operation))
      (tensor_source_index(snd(mts_write operation)))offset _ _ _
      (tensor_source_access_type(snd(mts_write operation)))(tensor_source_access_pure(snd(mts_write operation)))
      (@tensor_source_access_evaluation dimensions layout(snd(mts_write operation))ge locals temps memory valuation sizes offset DIMENSIONS WORDS INDEX)
      ltac:(pose proof(@tensor_index_bounds sizes _ offset INDEX); pose proof(@tensor_layout_flag_sound sizes LAYOUT);
        unfold signed_range; pose proof Int.min_signed_neg; lia)LVALUE)as [base [POINTER [ADDRESS FIELD]]]; subst end.
  match goal with CAST:sem_cast ?old _ _ _=Some _ |- _=>rewrite TYPE in CAST;
    destruct old; cbn in CAST; try discriminate CAST; inversion CAST; subst end.
  match goal with ASSIGN:assign_loc _ _ _ _ _ _ _ _ |- _=>inversion ASSIGN; subst; try discriminate end.
  match goal with MODE:access_mode _=By_value _ |- _=>inversion MODE; subst end.
  match goal with STORE:Mem.storev _ _ _ _=Some _ |- _=>cbn [Mem.storev]in STORE;
    rewrite memory_pointer_buffer_address in STORE;
    destruct(zle(memory_pointer_buffer_offset base offset+size_chunk Mint32)Ptrofs.modulus); try discriminate STORE end.
  match goal with VALUE:eval_expr _ _ _ _ (mts_rhs operation)(Vint ?word) |- _=>
    destruct(@memory_source_value_inverse ge locals temps memory(memory_pointer_register_codes layout)
      (map multi_tensor_source_lvalue(mts_reads operation))(fun code value=>eval_expr ge locals temps memory code value)
      (memory_pointer_register_types layout)ltac:(apply Forall_map,Forall_forall; intros; reflexivity)
      ltac:(intros code w MEMBER EVAL; exact EVAL)
      ltac:(intros code a b A B; exact((proj1(expressions_determinate ge locals temps memory))code a A b B))
      (map valuation layout)(mts_value operation)(mts_rhs operation)word(memory_pointer_register_pure layout)
      (@memory_pointer_register_operands ge locals temps memory layout valuation WORDS)
      (mts_reads_used operation)(mts_rhs_compile operation)VALUE)as [loaded [LOADS COMPUTE]] end.
  destruct(@multi_tensor_source_reads_resolve dimensions layout ge locals temps memory valuation sizes(mts_reads operation)loaded
    LAYOUT DIMENSIONS WORDS READS LOADS)as [locations [RESOLVE LOAD]].
  split; [|reflexivity]; unfold memory_nary_point,GuardMemoryInstr.instr_semantics; split; [reflexivity|split; [reflexivity|]].
  exists(MemoryLocation Mint32 loc(memory_pointer_buffer_offset base offset)),locations.
  split; [apply multi_tensor_location_at; [exact POINTER|exact INDEX]|split].
  - unfold GuardMemoryRectangles.memory_read_cells,multi_tensor_source_instruction; cbn [instruction_reads runtime_locations].
    rewrite map_map; exact RESOLVE.
  - split; [reflexivity|]; exists loaded.
    match type of COMPUTE with _=Some ?value=>exists value end.
    split; [exact LOAD|split; [exact COMPUTE|assumption]].
Qed.

Print Assumptions multi_tensor_source_read_inverse.
Print Assumptions check_multi_tensor_source_operation.
Print Assumptions multi_tensor_source_reads_resolve.
Print Assumptions multi_tensor_source_operation_decode.
