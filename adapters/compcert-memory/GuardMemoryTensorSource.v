From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightPureExpr ClightCountedLoop ClightSyntaxEquality
  ClightTempFrame ClightLoopSyntax ClightRegionProgress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryArrayBackend
  GuardMemoryFlatArrayBackend GuardMemoryBufferOffsets GuardMemoryPointerAccess GuardMemoryPointerSourceAccess
  GuardMemoryPointerCompute GuardMemoryNaryCompute GuardMemoryAffineSourceExpressions
  GuardMemoryNaryAffineExpressions GuardMemorySourceValueInterface GuardMemorySourceParameters GuardMemoryPointerDefinedIndex GuardMemoryDynamicTensorLayout
  GuardMemoryDynamicTensorAccess GuardMemoryDynamicTensorBackend GuardMemoryTensorHorner.
From GuardInterface Require Import ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint tensor_encode_coordinates layout coordinates : option(list constraint) :=
  match coordinates with
  | [] => Some []
  | coordinate::rest => match memory_encode_nary_index layout coordinate,tensor_encode_coordinates layout rest with
    | Some term,Some terms => Some(term::terms) | _,_ => None end end.
Lemma tensor_encode_coordinates_sound layout coordinates terms :
  tensor_encode_coordinates layout coordinates=Some terms ->
  Forall2(fun coordinate term=>memory_encode_nary_index layout coordinate=Some term)coordinates terms.
Proof.
  revert terms; induction coordinates; intros terms ENCODE; cbn in ENCODE.
  - inversion ENCODE; constructor.
  - destruct(memory_encode_nary_index layout a)as [term|]eqn:TERM; [|discriminate].
    destruct(tensor_encode_coordinates layout coordinates)as [tail|]eqn:TAIL; [|discriminate].
    inversion ENCODE; subst; constructor; [exact TERM|apply IHcoordinates; reflexivity].
Qed.
Record tensor_source_access dimensions layout := TensorSourceAccess {
  tensor_source_coordinates : list memory_source_affine;
  tensor_source_terms : list constraint;
  tensor_source_index : expr;
  tensor_source_encoded : Forall2(fun coordinate term=>memory_encode_nary_index layout coordinate=Some term)
    tensor_source_coordinates tensor_source_terms;
  tensor_source_horner : tensor_horner_expression(map tensor_dimension_code dimensions)
    (map memory_source_affine_code tensor_source_coordinates)=Some tensor_source_index
}.
Definition describe_tensor_source_access dimensions layout (coordinates:list memory_source_affine) : option(tensor_source_access dimensions layout).
Proof.
  destruct(tensor_encode_coordinates layout coordinates)as [terms|]eqn:ENCODE; [|exact None].
  destruct(tensor_horner_expression(map tensor_dimension_code dimensions)(map memory_source_affine_code coordinates))as [code|]eqn:CODE;
    [|exact None].
  exact(Some(@TensorSourceAccess dimensions layout coordinates terms code
    (@tensor_encode_coordinates_sound layout coordinates terms ENCODE)CODE)).
Defined.
Definition tensor_source_access_available dimensions layout(access:tensor_source_access dimensions layout) values sizes :=
  exists offset,tensor_index sizes(affine_product(tensor_source_terms access)values)=Some offset.
Lemma tensor_source_coordinates_evaluation layout coordinates terms valuation ge locals temps memory :
  Forall2(fun coordinate term=>memory_encode_nary_index layout coordinate=Some term)coordinates terms ->
  (forall identifier,In identifier layout -> temps!identifier=Some(Vint(Int.repr(valuation identifier)))) ->
  Forall2(tensor_operand ge locals temps memory)(map memory_source_affine_code coordinates)
    (affine_product terms(map valuation layout)).
Proof.
  intros ENCODE WORDS; induction ENCODE as [|coordinate term coordinates terms HEAD REST IH]; cbn [map affine_product]; constructor.
  - split; [apply memory_source_affine_type|split; [apply memory_source_affine_pure|]].
    exact(@memory_nary_index_expression_evaluation coordinate layout term valuation ge locals temps memory HEAD WORDS).
  - exact IH.
Qed.
Lemma tensor_source_access_type dimensions layout(access:tensor_source_access dimensions layout) :
  typeof(tensor_source_index access)=type_int32s.
Proof.
  eapply tensor_horner_expression_type; [|exact(tensor_source_horner access)].
  apply Forall_map,Forall_forall; intros; apply memory_source_affine_type.
Qed.
Lemma tensor_source_access_pure dimensions layout(access:tensor_source_access dimensions layout) :
  pure_scalar(tensor_source_index access).
Proof.
  eapply tensor_horner_expression_pure; [| |exact(tensor_source_horner access)].
  - apply Forall_map,Forall_forall; intros source MEMBER; destruct source; cbn [tensor_dimension_code].
    + unfold ClightRectangularStore.rect_constant; destruct(z <? 0); repeat constructor.
    + constructor.
  - apply Forall_map,Forall_forall; intros; apply memory_source_affine_pure.
Qed.
Lemma tensor_source_access_evaluation dimensions layout(access:tensor_source_access dimensions layout)
    ge locals temps memory valuation sizes offset :
  tensor_dimension_view dimensions sizes temps ->
  (forall identifier,In identifier layout -> temps!identifier=Some(Vint(Int.repr(valuation identifier)))) ->
  tensor_index sizes(affine_product(tensor_source_terms access)(map valuation layout))=Some offset ->
  eval_expr ge locals temps memory(tensor_source_index access)(Vint(Int.repr offset)).
Proof.
  intros DIMENSIONS WORDS INDEX; eapply tensor_horner_expression_evaluation;
    [eapply tensor_dimension_view_evaluation; exact DIMENSIONS|
     eapply tensor_source_coordinates_evaluation; [exact(tensor_source_encoded access)|exact WORDS]|
     exact(tensor_source_horner access)|exact INDEX].
Qed.
Theorem tensor_source_access_load_inverse dimensions layout(access:tensor_source_access dimensions layout)
    pointer block base ge locals temps memory valuation sizes offset value :
  tensor_layout_flag sizes=true -> tensor_dimension_view dimensions sizes temps ->
  (forall identifier,In identifier layout -> temps!identifier=Some(Vint(Int.repr(valuation identifier)))) ->
  temps!pointer=Some(Vptr block base) ->
  tensor_index sizes(affine_product(tensor_source_terms access)(map valuation layout))=Some offset ->
  eval_expr ge locals temps memory(memory_pointer_lvalue pointer(tensor_source_index access))value ->
  Mem.load Mint32 memory block(memory_pointer_buffer_offset base offset)=Some value.
Proof.
  intros LAYOUT DIMENSIONS WORDS POINTER INDEX RUN.
  destruct(@memory_pointer_load_inverse ge locals temps memory pointer(tensor_source_index access)offset value
    (tensor_source_access_type access)(tensor_source_access_pure access)
    (@tensor_source_access_evaluation dimensions layout access ge locals temps memory valuation sizes offset DIMENSIONS WORDS INDEX)
    ltac:(pose proof(@tensor_index_bounds sizes _ offset INDEX); pose proof(@tensor_layout_flag_sound sizes LAYOUT);
      unfold signed_range; pose proof Int.min_signed_neg; lia) RUN)as [actual [address [BINDING LOAD]]].
  rewrite POINTER in BINDING; inversion BINDING; subst; exact LOAD.
Qed.

Record tensor_source_operation dimensions layout (pointer logical_array:ident) (source:statement) := TensorSourceOperation {
  tensor_source_write : tensor_source_access dimensions layout;
  tensor_source_reads : list(tensor_source_access dimensions layout);
  tensor_source_value : value_expression;
  tensor_source_rhs : expr;
  tensor_source_rhs_compile : compile_flat_value(memory_pointer_register_codes layout)
    (map(fun access=>memory_pointer_lvalue pointer(tensor_source_index access))tensor_source_reads)
    tensor_source_value=Some tensor_source_rhs;
  tensor_source_reads_used : memory_source_reads_check
    (map(fun access=>memory_pointer_lvalue pointer(tensor_source_index access))tensor_source_reads)tensor_source_value=true;
  tensor_source_exact : source=Sassign(memory_pointer_lvalue pointer(tensor_source_index tensor_source_write))tensor_source_rhs
}.
Definition tensor_source_instruction dimensions layout pointer logical_array source
    (operation:tensor_source_operation dimensions layout pointer logical_array source) :=
  MemoryInstruction(logical_array,tensor_source_terms(tensor_source_write operation))
    (map(fun access=>(logical_array,tensor_source_terms access))(tensor_source_reads operation))(tensor_source_value operation).
Definition check_tensor_source_operation dimensions layout pointer logical_array source
    (write:tensor_source_access dimensions layout) (reads:list(tensor_source_access dimensions layout)) (value:value_expression) :
    option(tensor_source_operation dimensions layout pointer logical_array source).
Proof.
  destruct(compile_flat_value(memory_pointer_register_codes layout)
    (map(fun access=>memory_pointer_lvalue pointer(tensor_source_index access))reads)value)as [rhs|]eqn:RHS; [|exact None].
  destruct(memory_source_reads_check(map(fun access=>memory_pointer_lvalue pointer(tensor_source_index access))reads)value)eqn:USED;
    [|exact None].
  destruct(statement_eq source(Sassign(memory_pointer_lvalue pointer(tensor_source_index write))rhs))as [EXACT|]; [|exact None].
  exact(Some(@TensorSourceOperation dimensions layout pointer logical_array source write reads value rhs RHS USED EXACT)).
Defined.
Lemma tensor_source_reads_resolve dimensions layout pointer logical_array block base ge locals temps memory valuation sizes
    (accesses:list(tensor_source_access dimensions layout))loaded :
  tensor_layout_flag sizes=true -> tensor_dimension_view dimensions sizes temps ->
  (forall identifier,In identifier layout -> temps!identifier=Some(Vint(Int.repr(valuation identifier)))) ->
  temps!pointer=Some(Vptr block base) ->
  Forall(fun access=>tensor_source_access_available access(map valuation layout)sizes)accesses ->
  Forall2(fun code value=>eval_expr ge locals temps memory code value)
    (map(fun access=>memory_pointer_lvalue pointer(tensor_source_index access))accesses)loaded ->
  exists locations,resolve_cells(map(fun access=>exact_cell(logical_array,tensor_source_terms access)(map valuation layout))accesses)
      (tensor_pointer_locations logical_array block base sizes)=Some locations /\ load_locations locations memory=Some loaded.
Proof.
  intros LAYOUT DIMENSIONS WORDS POINTER COVER; revert loaded; induction COVER as [|access accesses [offset INDEX] COVER IH];
    intros loaded LOADS; cbn [map] in LOADS; inversion LOADS; subst.
  - exists []; split; reflexivity.
  - destruct(IH _ ltac:(eassumption))as [locations [RESOLVE LOAD]].
    assert(LOCATION:tensor_pointer_locations logical_array block base sizes
      (exact_cell(logical_array,tensor_source_terms access)(map valuation layout))=
      Some(MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset))).
    { exact(@tensor_pointer_location_at logical_array block base sizes _ offset INDEX). }
    exists(MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset)::locations); split.
    + cbn [map resolve_cells]; rewrite LOCATION,RESOLVE;
        reflexivity.
    + cbn [load_locations]; unfold location_load; cbn [location_chunk location_block location_offset].
      rewrite(@tensor_source_access_load_inverse dimensions layout access pointer block base ge locals temps memory
        valuation sizes offset _ LAYOUT DIMENSIONS WORDS POINTER INDEX ltac:(eassumption)),LOAD; reflexivity.
Qed.

Theorem tensor_source_operation_decode dimensions layout pointer logical_array source
    (operation:tensor_source_operation dimensions layout pointer logical_array source)
    fe ge locals temps memory after final valuation sizes block base :
  tensor_layout_flag sizes=true -> tensor_dimension_view dimensions sizes temps ->
  (forall identifier,In identifier layout -> temps!identifier=Some(Vint(Int.repr(valuation identifier)))) ->
  temps!pointer=Some(Vptr block base) ->
  Forall(fun access=>tensor_source_access_available access(map valuation layout)sizes)
    (tensor_source_write operation::tensor_source_reads operation) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_nary_point(tensor_source_instruction operation)(map valuation layout)
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)memory)
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)final) /\ after=temps.
Proof.
  intros LAYOUT DIMENSIONS WORDS POINTER COVER RUN.
  inversion COVER as [|write reads [offset INDEX] READS]; subst write reads.
  assert(TYPE:typeof(tensor_source_rhs operation)=type_int32s).
  { eapply memory_source_flat_type; [apply memory_pointer_register_types| |exact(tensor_source_rhs_compile operation)].
    apply Forall_map,Forall_forall; intros; reflexivity. }
  rewrite(tensor_source_exact operation)in RUN; inversion RUN; subst after.
  match goal with LVALUE:eval_lvalue _ _ _ _ (memory_pointer_lvalue _ _) _ _ _ |- _ =>
    destruct(@memory_pointer_lvalue_inverse ge locals temps memory pointer(tensor_source_index(tensor_source_write operation))offset _ _ _
      (tensor_source_access_type(tensor_source_write operation))(tensor_source_access_pure(tensor_source_write operation))
      (@tensor_source_access_evaluation dimensions layout(tensor_source_write operation)ge locals temps memory valuation sizes offset DIMENSIONS WORDS INDEX)
      ltac:(pose proof(@tensor_index_bounds sizes _ offset INDEX); pose proof(@tensor_layout_flag_sound sizes LAYOUT);
        unfold signed_range; pose proof Int.min_signed_neg; lia)LVALUE)as [address [BINDING [ADDRESS FIELD]]]; subst end.
  rewrite POINTER in BINDING; inversion BINDING; subst loc address.
  match goal with CAST:sem_cast ?old _ _ _=Some _ |- _ => rewrite TYPE in CAST;
    destruct old; cbn in CAST; try discriminate CAST; inversion CAST; subst end.
  match goal with ASSIGN:assign_loc _ _ _ _ _ _ _ _ |- _ => inversion ASSIGN; subst; try discriminate end.
  match goal with MODE:access_mode _=By_value _ |- _ => inversion MODE; subst end.
  match goal with STORE:Mem.storev _ _ _ _=Some _ |- _ => cbn [Mem.storev]in STORE;
    rewrite memory_pointer_buffer_address in STORE;
    destruct(zle(memory_pointer_buffer_offset base offset+size_chunk Mint32)Ptrofs.modulus); try discriminate STORE end.
  match goal with VALUE:eval_expr _ _ _ _ (tensor_source_rhs operation)(Vint ?word) |- _ =>
    destruct(@memory_source_value_inverse ge locals temps memory(memory_pointer_register_codes layout)
      (map(fun access=>memory_pointer_lvalue pointer(tensor_source_index access))(tensor_source_reads operation))
      (fun code value=>eval_expr ge locals temps memory code value)
      (memory_pointer_register_types layout)ltac:(apply Forall_map,Forall_forall; intros; reflexivity)
      ltac:(intros code w MEMBER EVAL; exact EVAL)
      ltac:(intros code a b A B; exact((proj1(expressions_determinate ge locals temps memory))code a A b B))
      (map valuation layout)(tensor_source_value operation)(tensor_source_rhs operation)word
      (memory_pointer_register_pure layout)(@memory_pointer_register_operands ge locals temps memory layout valuation WORDS)
      (tensor_source_reads_used operation)(tensor_source_rhs_compile operation)VALUE)as [loaded [LOADS COMPUTE]] end.
  destruct(@tensor_source_reads_resolve dimensions layout pointer logical_array block base ge locals temps memory valuation sizes
    (tensor_source_reads operation)loaded LAYOUT DIMENSIONS WORDS POINTER READS LOADS)as [locations [RESOLVE LOAD]].
  split; [|reflexivity]; unfold memory_nary_point,GuardMemoryInstr.instr_semantics; split; [reflexivity|split; [reflexivity|]].
  exists(MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset)),locations.
  split; [exact(@tensor_pointer_location_at logical_array block base sizes _ offset INDEX)|].
  split.
  - unfold GuardMemoryRectangles.memory_read_cells,tensor_source_instruction; cbn [instruction_reads runtime_locations].
    rewrite map_map; exact RESOLVE.
  - split; [reflexivity|].
  exists loaded; match type of COMPUTE with _=Some ?value => exists value end.
  split; [exact LOAD|split; [exact COMPUTE|assumption]].
Qed.

Lemma tensor_dimension_codes_types dimensions : Forall(fun code=>typeof code=type_int32s)(map tensor_dimension_code dimensions).
Proof.
  apply Forall_map,Forall_forall; intros source MEMBER; destruct source; cbn [tensor_dimension_code];
    [apply ClightRectangularStore.rect_constant_type|reflexivity].
Qed.
Lemma tensor_dimension_codes_words dimensions ge locals temps memory :
  Forall(fun code=>exists word,eval_expr ge locals temps memory code(Vint word))(map tensor_dimension_code dimensions) ->
  forall identifier,In identifier(tensor_dimension_registers dimensions) -> exists word,temps!identifier=Some(Vint word).
Proof.
  induction dimensions as [|source dimensions IH]; cbn [map tensor_dimension_registers]; intros WORDS identifier MEMBER;
    [contradiction|].
  inversion WORDS as [|same rest [word WORD]TAIL]; subst.
  destruct source; cbn [tensor_dimension_registers] in MEMBER.
  - eapply IH; eassumption.
  - cbn in MEMBER; destruct MEMBER as [<-|MEMBER].
    + exists word; eapply scalar_temp_inv; exact WORD.
    + eapply IH; eassumption.
Qed.
Theorem tensor_source_access_defined_dimensions dimensions layout(access:tensor_source_access dimensions layout)
    pointer ge locals temps memory block offset field :
  eval_lvalue ge locals temps memory(memory_pointer_lvalue pointer(tensor_source_index access))block offset field ->
  forall identifier,In identifier(tensor_dimension_registers(tl dimensions)) -> exists word,temps!identifier=Some(Vint word).
Proof.
  intro RUN; destruct(@memory_pointer_lvalue_index_word ge locals temps memory pointer(tensor_source_index access)
    block offset field(tensor_source_access_type access)RUN)as [word INDEX].
  destruct(@tensor_horner_expression_words ge locals temps memory(map tensor_dimension_code dimensions)
    (map memory_source_affine_code(tensor_source_coordinates access))(tensor_source_index access)word
    (tensor_dimension_codes_types dimensions)ltac:(apply Forall_map,Forall_forall; intros; apply memory_source_affine_type)
    (tensor_source_horner access)INDEX)as [DIMENSIONS _].
  replace(tl(map tensor_dimension_code dimensions))with(map tensor_dimension_code(tl dimensions))in DIMENSIONS
    by(destruct dimensions; reflexivity).
  eapply tensor_dimension_codes_words; exact DIMENSIONS.
Qed.
Theorem tensor_source_operation_has_capability dimensions layout pointer logical_array source
    (operation:tensor_source_operation dimensions layout pointer logical_array source)fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  (exists block base,temps!pointer=Some(Vptr block base)) /\
  (forall identifier,In identifier(tensor_dimension_registers(tl dimensions)) -> exists word,temps!identifier=Some(Vint word)) /\
  (forall identifier index,nth_error layout index=Some identifier -> In index(memory_source_parameter_positions(tensor_source_value operation)) ->
    exists word,temps!identifier=Some(Vint word)).
Proof.
  intro RUN; rewrite(tensor_source_exact operation)in RUN; inversion RUN; subst.
  split.
  - exists loc; eapply memory_pointer_lvalue_has_base; [apply tensor_source_access_type|eassumption].
  - split.
    + eapply tensor_source_access_defined_dimensions; eassumption.
    + intros identifier index LOOKUP USED.
      assert(TYPE:typeof(tensor_source_rhs operation)=type_int32s).
      { eapply memory_source_flat_type; [apply memory_pointer_register_types| |exact(tensor_source_rhs_compile operation)].
        apply Forall_map,Forall_forall; intros; reflexivity. }
      match goal with CAST:sem_cast ?old _ _ _=Some _ |- _ => rewrite TYPE in CAST;
        destruct old; cbn in CAST; try discriminate CAST; inversion CAST; subst end.
      eapply memory_source_used_register_typed; [|exact LOOKUP|exact USED|exact(tensor_source_rhs_compile operation)|eassumption].
      apply Forall_map,Forall_forall; intros; reflexivity.
Qed.
Lemma tensor_source_operation_normal dimensions layout pointer logical_array source
    (operation:tensor_source_operation dimensions layout pointer logical_array source) : normal_statement source=true.
Proof. rewrite(tensor_source_exact operation); reflexivity. Qed.
Lemma tensor_source_operation_quiet dimensions layout pointer logical_array source
    (operation:tensor_source_operation dimensions layout pointer logical_array source) : quiet_statement source=true.
Proof. rewrite(tensor_source_exact operation); reflexivity. Qed.
Lemma tensor_source_operation_writes dimensions layout pointer logical_array source
    (operation:tensor_source_operation dimensions layout pointer logical_array source) : writes_only [] source.
Proof. rewrite(tensor_source_exact operation); constructor. Qed.

Print Assumptions describe_tensor_source_access.
Print Assumptions tensor_source_coordinates_evaluation.
Print Assumptions tensor_source_access_load_inverse.
Print Assumptions check_tensor_source_operation.
Print Assumptions tensor_source_operation_decode.
Print Assumptions tensor_source_access_defined_dimensions.
Print Assumptions tensor_source_operation_has_capability.
