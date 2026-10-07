From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightRectangularStore
  ClightCountedLoop ClightTempFrame CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral
  GuardMemoryArrayBackend GuardMemoryFlatArrayBackend GuardMemoryBufferOffsets GuardMemoryPointerAccess
  GuardMemoryPointerBackend GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorAccess.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Layout values remain in ordinary expressions. The descriptor exposes exactly
    the temporaries protected by structured lowering; it carries no execution or
    preservation callback. Runtime dimensions are never enumerated as constants. *)
Inductive tensor_dimension_source :=
| TensorDimensionConstant : Z -> tensor_dimension_source
| TensorDimensionTemp : ident -> tensor_dimension_source.
Definition tensor_dimension_code source := match source with
  | TensorDimensionConstant z => rect_constant z
  | TensorDimensionTemp identifier => Etempvar identifier type_int32s end.
Fixpoint tensor_dimension_registers sources := match sources with
  | [] => []
  | TensorDimensionConstant _::rest => tensor_dimension_registers rest
  | TensorDimensionTemp identifier::rest => identifier::tensor_dimension_registers rest end.
Definition tensor_dimension_value temps source value := match source with
  | TensorDimensionConstant z => value=Int.signed(Int.repr z)
  | TensorDimensionTemp identifier => temps ! identifier=Some(Vint(Int.repr value)) end.
Definition tensor_dimension_view sources values temps := Forall2(tensor_dimension_value temps)sources values.

Lemma tensor_dimension_view_frame sources values before after :
  temp_agree(tensor_dimension_registers sources)before after ->
  tensor_dimension_view sources values before -> tensor_dimension_view sources values after.
Proof.
  intros FRAME VIEW; revert after FRAME; induction VIEW as [|source value sources values WORD VIEW IH];
    intros after FRAME; [constructor|constructor].
  - destruct source; cbn [tensor_dimension_value] in *; [exact WORD|].
    rewrite FRAME by(cbn; auto); exact WORD.
  - apply IH; eapply temp_agree_weaken; [|exact FRAME].
    intros identifier MEMBER; destruct source; cbn; auto.
Qed.
Lemma tensor_dimension_view_evaluation ge locals temps memory sources dimensions :
  tensor_dimension_view sources dimensions temps ->
  Forall2(tensor_operand ge locals temps memory)(map tensor_dimension_code sources)dimensions.
Proof.
  intro VIEW; induction VIEW as [|source value sources values WORD VIEW IH]; cbn [map]; [constructor|constructor; [|exact IH]].
  destruct source; unfold tensor_operand; cbn [tensor_dimension_code tensor_dimension_value] in *.
  - subst value; split; [apply rect_constant_type|split; [|rewrite Int.repr_signed; apply rect_constant_evaluation]].
    unfold rect_constant; destruct(z <? 0); repeat constructor.
  - split; [reflexivity|split; [constructor|constructor; exact WORD]].
Qed.

(** This direction needs only actual integer operands, including non-scalar
    expressions if a caller supplies them. Purity is required for separate
    inverse/transport services, not for forward evaluation of the lowered body. *)
Lemma tensor_index_words_evaluation ge locals temps memory dimension_codes coordinate_codes dimensions coordinates code offset :
  Forall2(tensor_operand ge locals temps memory)dimension_codes dimensions ->
  Forall2(MemoryBody.operand_view ge locals temps memory)coordinate_codes coordinates ->
  tensor_index_expression dimension_codes coordinate_codes=Some code ->
  tensor_index dimensions coordinates=Some offset ->
  eval_expr ge locals temps memory code(Vint(Int.repr offset)).
Proof.
  intro DS; revert coordinate_codes coordinates code offset; induction DS as
    [|dimension_code dimension dimension_codes dimensions DIM DS IH];
    intros coordinate_codes coordinates code offset CS CODE INDEX.
  - inversion CS; subst; cbn in INDEX,CODE; try discriminate.
    inversion INDEX; inversion CODE; subst; constructor.
  - inversion CS as [|coordinate_code coordinate tail coordinates' COORD REST]; subst; cbn in INDEX,CODE; try discriminate.
    destruct((0 <=? coordinate)&&(coordinate <? dimension)); [|discriminate].
    destruct(tensor_index dimensions coordinates') as [suffix|] eqn:SUFFIX; [|discriminate].
    destruct(tensor_index_expression dimension_codes tail) as [suffix_code|] eqn:SUFFIX_CODE; [|discriminate].
    inversion INDEX; inversion CODE; subst code offset.
    apply operand_sum_evaluation; [reflexivity|eapply tensor_index_expression_type; exact SUFFIX_CODE| |].
    + apply tensor_product_evaluation; [exact(proj1 COORD)|apply tensor_volume_expression_type|exact(proj2 COORD)|].
      apply tensor_volume_expression_evaluation; exact DS.
    + eapply IH; eassumption.
Qed.
Lemma tensor_affine_coordinates_evaluation ge locals temps memory codes parameters coordinates :
  Forall2(MemoryBody.operand_view ge locals temps memory)codes parameters ->
  Forall2(MemoryBody.operand_view ge locals temps memory)
    (map(flat_affine_expression codes)coordinates)(affine_product coordinates parameters).
Proof.
  intro WORDS; induction coordinates as [|coordinate rest IH]; cbn [map affine_product]; [constructor|constructor].
  - split; [apply flat_affine_type|apply flat_affine_evaluation; exact WORDS].
  - exact IH.
Qed.

Definition tensor_lower_access logical_array dimensions access codes : option expr :=
  if Pos.eqb(fst access)logical_array then
    tensor_index_expression(map tensor_dimension_code dimensions)(map(flat_affine_expression codes)(snd access))
  else None.
Fixpoint tensor_lower_reads logical_array dimensions accesses codes : option(list expr) :=
  match accesses with
  | [] => Some []
  | access::rest => match tensor_lower_access logical_array dimensions access codes,
      tensor_lower_reads logical_array dimensions rest codes with
    | Some index,Some indices => Some(index::indices) | _,_ => None end end.
Definition tensor_lower_instruction pointer logical_array dimensions instruction codes : option statement :=
  if flat_integer_result(instruction_value instruction) then
    match tensor_lower_access logical_array dimensions(instruction_write instruction)codes,
      tensor_lower_reads logical_array dimensions(instruction_reads instruction)codes with
    | Some write,Some reads => match compile_flat_value codes
        (map(memory_pointer_lvalue pointer)reads)(instruction_value instruction) with
      | Some value => Some(Sassign(memory_pointer_lvalue pointer write)value) | None => None end
    | _,_ => None end
  else None.

Lemma tensor_backend_access_evaluation logical_array block base dimension_sources dimensions
    ge locals temps memory access codes parameters code location :
  tensor_dimension_view dimension_sources dimensions temps ->
  Forall2(MemoryBody.operand_view ge locals temps memory)codes parameters ->
  tensor_lower_access logical_array dimension_sources access codes=Some code ->
  tensor_pointer_locations logical_array block base dimensions(exact_cell access parameters)=Some location ->
  exists offset,tensor_index dimensions(affine_product(snd access)parameters)=Some offset /\
    location=MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset) /\
    typeof code=type_int32s /\ eval_expr ge locals temps memory code(Vint(Int.repr offset)).
Proof.
  intros DIMENSIONS WORDS COMPILE RESOLVE; destruct access as [array coordinates].
  unfold tensor_lower_access in COMPILE; cbn [fst snd] in COMPILE.
  destruct(Pos.eqb array logical_array)eqn:ARRAY; [|discriminate].
  apply Pos.eqb_eq in ARRAY; subst array.
  unfold tensor_pointer_locations,exact_cell in RESOLVE; cbn [arr_id arr_index] in RESOLVE; rewrite Pos.eqb_refl in RESOLVE.
  destruct(tensor_index dimensions(affine_product coordinates parameters))as [offset|]eqn:INDEX; [|discriminate].
  inversion RESOLVE; subst location; exists offset; split; [exact INDEX|split; [reflexivity|split]].
  - eapply tensor_index_expression_type; exact COMPILE.
  - exact(@tensor_index_words_evaluation ge locals temps memory(map tensor_dimension_code dimension_sources)
      (map(flat_affine_expression codes)coordinates)dimensions(affine_product coordinates parameters)code offset
      (tensor_dimension_view_evaluation ge locals memory DIMENSIONS)
      (tensor_affine_coordinates_evaluation coordinates WORDS)COMPILE INDEX).
Qed.

Lemma tensor_backend_reads_evaluation pointer logical_array block base dimension_sources dimensions
    ge locals temps memory accesses codes parameters indices locations loaded :
  tensor_layout_flag dimensions=true -> temps ! pointer=Some(Vptr block base) ->
  tensor_dimension_view dimension_sources dimensions temps ->
  Forall2(MemoryBody.operand_view ge locals temps memory)codes parameters ->
  tensor_lower_reads logical_array dimension_sources accesses codes=Some indices ->
  resolve_cells(map(fun access=>exact_cell access parameters)accesses)
    (tensor_pointer_locations logical_array block base dimensions)=Some locations ->
  load_locations locations memory=Some loaded ->
  Forall2(flat_value_view ge locals temps memory)(map(memory_pointer_lvalue pointer)indices)loaded.
Proof.
  intros LAYOUT POINTER DIMENSIONS WORDS; revert indices locations loaded; induction accesses as [|access rest IH];
    intros indices locations loaded COMPILE RESOLVE LOAD.
  - cbn in COMPILE,RESOLVE; inversion COMPILE; inversion RESOLVE; subst; cbn in LOAD; inversion LOAD; constructor.
  - cbn [tensor_lower_reads] in COMPILE.
    destruct(tensor_lower_access logical_array dimension_sources access codes)as [index|]eqn:INDEX; [|discriminate].
    destruct(tensor_lower_reads logical_array dimension_sources rest codes)as [indices'|]eqn:REST; [|discriminate].
    inversion COMPILE; subst indices; cbn [map resolve_cells] in RESOLVE.
    destruct(tensor_pointer_locations logical_array block base dimensions(exact_cell access parameters))
      as [location|]eqn:LOCATION; [|discriminate].
    destruct(resolve_cells(map(fun access=>exact_cell access parameters)rest)
      (tensor_pointer_locations logical_array block base dimensions))as [locations'|]eqn:TAIL; [|discriminate].
    inversion RESOLVE; subst locations; cbn [load_locations] in LOAD.
    destruct(location_load location memory)as [value|]eqn:VALUE; [|discriminate].
    destruct(load_locations locations' memory)as [loaded'|]eqn:VALUES; [|discriminate].
    inversion LOAD; subst loaded; cbn [map]; constructor.
    + destruct(@tensor_backend_access_evaluation logical_array block base dimension_sources dimensions ge locals temps memory
        access codes parameters index location DIMENSIONS WORDS INDEX LOCATION)as [offset [BOUND [SAME [TYPE EVAL]]]]; subst location.
      split; [reflexivity|]; eapply eval_Elvalue.
      * eapply memory_pointer_lvalue_evaluation; [exact POINTER|exact TYPE|exact EVAL|].
        pose proof(@tensor_index_bounds dimensions(affine_product(snd access)parameters)offset BOUND).
        pose proof(@tensor_layout_flag_sound dimensions LAYOUT); unfold signed_range; pose proof Int.min_signed_neg; lia.
      * apply deref_loc_value with(chunk:=Mint32); [reflexivity|].
        cbn [Mem.loadv]; rewrite memory_pointer_buffer_address.
        pose proof(@memory_pointer_load_end memory block base offset value VALUE)as END.
        destruct(zle(memory_pointer_buffer_offset base offset+size_chunk Mint32)Ptrofs.modulus); [exact VALUE|lia].
    + exact(IH indices' locations' loaded' eq_refl eq_refl VALUES).
Qed.

Section BACKEND.
Variable dimensions : list Z.
Hypothesis LAYOUT : tensor_layout_flag dimensions=true.
Variable dimension_sources : list tensor_dimension_source.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable pointer logical_array : ident.
Variable block : Values.block.
Variable base : ptrofs.
Definition tensor_buffer_view state memory := state=RuntimeState(tensor_pointer_locations logical_array block base dimensions)memory.
Definition tensor_buffer_protected := pointer::tensor_dimension_registers dimension_sources.
Definition tensor_buffer_capability temps := temps ! pointer=Some(Vptr block base) /\
  tensor_dimension_view dimension_sources dimensions temps.
Lemma tensor_buffer_capability_frame before after : temp_agree tensor_buffer_protected before after ->
  tensor_buffer_capability before -> tensor_buffer_capability after.
Proof.
  intros FRAME [POINTER DIMENSIONS]; split.
  - rewrite FRAME by(cbn; auto); exact POINTER.
  - eapply tensor_dimension_view_frame; [|exact DIMENSIONS].
    eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; right; exact MEMBER.
Qed.

Definition tensor_instruction_backend : MemoryFramedNested.instruction_backend fe ge locals tensor_buffer_view tensor_buffer_capability.
Proof.
  refine {|MemoryFramedNested.lower_instruction:=tensor_lower_instruction pointer logical_array dimension_sources|}.
  intros instruction codes parameters code temps memory source target writes reads COMPILE WORDS RUN VIEW [POINTER DIMENSIONS].
  unfold tensor_lower_instruction in COMPILE.
  destruct(flat_integer_result(instruction_value instruction))eqn:INTEGER; [|discriminate].
  destruct(tensor_lower_access logical_array dimension_sources(instruction_write instruction)codes)as [write_index|]eqn:WRITE_CODE; [|discriminate].
  destruct(tensor_lower_reads logical_array dimension_sources(instruction_reads instruction)codes)as [read_indices|]eqn:READ_CODES; [|discriminate].
  destruct(compile_flat_value codes(map(memory_pointer_lvalue pointer)read_indices)(instruction_value instruction))
    as [value_code|]eqn:VALUE_CODE; [|discriminate].
  inversion COMPILE; subst code; unfold tensor_buffer_view in VIEW; subst source.
  destruct RUN as [WRITES [READS [write [read_locations [WRITE [READ [LOCATIONS ACTION]]]]]]].
  subst writes reads; destruct target as [locations final]; cbn in LOCATIONS,ACTION; subst locations.
  destruct ACTION as [loaded [value [LOAD [COMPUTE STORE]]]]; cbn [memory_reads memory_write memory_compute] in LOAD,COMPUTE,STORE.
  destruct(@tensor_backend_access_evaluation logical_array block base dimension_sources dimensions ge locals temps memory
    (instruction_write instruction)codes parameters write_index write DIMENSIONS WORDS WRITE_CODE WRITE)
    as [offset [BOUND [LOCATION [INDEX_TYPE INDEX_EVAL]]]]; subst write.
  pose proof(@tensor_backend_reads_evaluation pointer logical_array block base dimension_sources dimensions ge locals temps memory
    (instruction_reads instruction)codes parameters read_indices read_locations loaded LAYOUT POINTER DIMENSIONS WORDS READ_CODES READ LOAD)as READ_EVALUATIONS.
  destruct(@compile_flat_value_evaluation(instruction_value instruction)codes(map(memory_pointer_lvalue pointer)read_indices)
    value_code parameters loaded value ge locals temps memory WORDS READ_EVALUATIONS VALUE_CODE COMPUTE)as [VALUE_TYPE VALUE_EVAL].
  destruct(@flat_integer_result_correct(instruction_value instruction)parameters loaded value INTEGER COMPUTE)as [integer ->].
  exists final; split; [reflexivity|].
  eapply exec_Sassign with(loc:=block)(ofs:=Ptrofs.add base(Ptrofs.repr(4*offset)))(bf:=Full)(v:=Vint integer)(v2:=Vint integer).
  - eapply memory_pointer_lvalue_evaluation; [exact POINTER|exact INDEX_TYPE|exact INDEX_EVAL|].
    pose proof(@tensor_index_bounds dimensions(affine_product(snd(instruction_write instruction))parameters)offset BOUND).
    pose proof(@tensor_layout_flag_sound dimensions LAYOUT); unfold signed_range; pose proof Int.min_signed_neg; lia.
  - exact VALUE_EVAL.
  - rewrite VALUE_TYPE; reflexivity.
  - apply assign_loc_value with(chunk:=Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite memory_pointer_buffer_address.
    pose proof(@memory_pointer_store_end memory final block base offset(Vint integer)STORE)as END.
    destruct(zle(memory_pointer_buffer_offset base offset+size_chunk Mint32)Ptrofs.modulus); [exact STORE|lia].
Defined.

Definition compile_tensor_buffer_loop layout bounds live pool loop :=
  if MemoryFramedNested.N.scratch_check pool(layout++tensor_buffer_protected++live)
  then MemoryFramedNested.N.compile_nested_raw(tensor_lower_instruction pointer logical_array dimension_sources)layout bounds pool loop
  else None.
Theorem compile_tensor_buffer_loop_correct layout bounds live pool loop code parameters temps source target memory :
  compile_tensor_buffer_loop layout bounds live pool loop=Some code ->
  MemoryFramedNested.N.A.typed_view layout parameters temps -> MemoryFramedNested.N.A.env_within bounds parameters ->
  GuardMemoryIRs.Loop.loop_semantics loop parameters source target -> tensor_buffer_view source memory -> tensor_buffer_capability temps ->
  exists target_temps target_memory,tensor_buffer_view target target_memory /\ tensor_buffer_capability target_temps /\
    temp_agree(layout++tensor_buffer_protected++live)temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  unfold compile_tensor_buffer_loop; intros COMPILE VIEW WITHIN RUN MEMORY CAPABILITY.
  destruct(MemoryFramedNested.N.scratch_check pool(layout++tensor_buffer_protected++live))eqn:FRESH; [|discriminate].
  destruct(@MemoryFramedNested.compile_nested_correct fe ge locals tensor_buffer_view tensor_buffer_protected
    tensor_buffer_capability tensor_buffer_capability_frame tensor_instruction_backend loop layout bounds pool code parameters temps source target memory
    (tensor_buffer_protected++live)COMPILE(MemoryFramedNested.N.scratch_check_sound pool _ FRESH)WITHIN VIEW RUN MEMORY CAPABILITY
    ltac:(intros identifier MEMBER; apply in_or_app; left; exact MEMBER))as [target_temps [target_memory [TARGET [FRAME EXEC]]]].
  exists target_temps,target_memory; split; [exact TARGET|split; [|split; [exact FRAME|exact EXEC]]].
  eapply tensor_buffer_capability_frame; [|exact CAPABILITY]; eapply temp_agree_weaken; [|exact FRAME].
  intros identifier MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
Qed.
End BACKEND.

Print Assumptions tensor_dimension_view_frame.
Print Assumptions tensor_dimension_view_evaluation.
Print Assumptions tensor_index_words_evaluation.
Print Assumptions tensor_affine_coordinates_evaluation.
Print Assumptions tensor_backend_access_evaluation.
Print Assumptions tensor_backend_reads_evaluation.
Print Assumptions tensor_buffer_capability_frame.
Print Assumptions tensor_instruction_backend.
Print Assumptions compile_tensor_buffer_loop_correct.
