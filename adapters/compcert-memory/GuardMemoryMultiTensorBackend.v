From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightNoWrap CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral
  GuardMemoryArrayBackend GuardMemoryFlatArrayBackend GuardMemoryBufferOffsets GuardMemoryPointerAccess GuardMemoryFramedNested GuardMemoryPointerBackend
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorAccess GuardMemoryDynamicTensorBackend.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Each logical array is named by its actual pointer temporary. Arrays share
    runtime dimensions in this family. The locator retains actual aliasing;
    injectivity or separation is not an assumption of instruction lowering. *)
Definition multi_tensor_locations (initial:temp_env) sizes cell :=
  match initial!(arr_id cell) with
  | Some(Vptr block base)=>tensor_pointer_locations(arr_id cell)block base sizes cell
  | _=>None end.

Lemma multi_tensor_location_at initial sizes array block base coordinates offset :
  initial!array=Some(Vptr block base) -> tensor_index sizes coordinates=Some offset ->
  multi_tensor_locations initial sizes {|arr_id:=array;arr_index:=coordinates|}=
    Some(MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset)).
Proof.
  intros POINTER INDEX; unfold multi_tensor_locations; cbn [arr_id]; rewrite POINTER.
  exact(@tensor_pointer_location_at array block base sizes coordinates offset INDEX).
Qed.

Lemma multi_tensor_location_inverse initial sizes cell location :
  multi_tensor_locations initial sizes cell=Some location ->
  exists block base offset,initial!(arr_id cell)=Some(Vptr block base) /\
    tensor_index sizes(arr_index cell)=Some offset /\
    location=MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset).
Proof.
  unfold multi_tensor_locations; destruct(initial!(arr_id cell))as [value|]eqn:POINTER; [|discriminate].
  destruct value; try discriminate.
  unfold tensor_pointer_locations; rewrite Pos.eqb_refl.
  destruct(tensor_index sizes(arr_index cell))as [offset|]eqn:INDEX; [|discriminate].
  intro RESOLVE; inversion RESOLVE; subst location; exists b,i,offset; auto.
Qed.

Definition multi_tensor_lower_access pointers dimensions access codes :=
  if existsb(Pos.eqb(fst access))pointers then
    match tensor_lower_access(fst access)dimensions access codes with
    | Some index=>Some(memory_pointer_lvalue(fst access)index)
    | None=>None end
  else None.
Fixpoint multi_tensor_lower_reads pointers dimensions accesses codes := match accesses with
| []=>Some []
| access::rest=>match multi_tensor_lower_access pointers dimensions access codes,
    multi_tensor_lower_reads pointers dimensions rest codes with
  | Some code,Some tail=>Some(code::tail)|_,_=>None end end.
Definition multi_tensor_lower_instruction pointers dimensions instruction codes :=
  if flat_integer_result(instruction_value instruction)then
    match multi_tensor_lower_access pointers dimensions(instruction_write instruction)codes,
      multi_tensor_lower_reads pointers dimensions(instruction_reads instruction)codes with
    | Some write,Some reads=>match compile_flat_value codes reads(instruction_value instruction)with
      | Some value=>Some(Sassign write value)|None=>None end
    |_,_=>None end
  else None.

Lemma multi_tensor_backend_access initial sizes pointers dimensions
    ge locals temps memory access codes parameters code location :
  tensor_layout_flag sizes=true -> temp_agree pointers initial temps ->
  tensor_dimension_view dimensions sizes temps ->
  Forall2(MemoryBody.operand_view ge locals temps memory)codes parameters ->
  multi_tensor_lower_access pointers dimensions access codes=Some code ->
  multi_tensor_locations initial sizes(exact_cell access parameters)=Some location ->
  exists block base offset,
    location=MemoryLocation Mint32 block(memory_pointer_buffer_offset base offset) /\
    typeof code=type_int32s /\
    eval_lvalue ge locals temps memory code block(Ptrofs.add base(Ptrofs.repr(4*offset)))Full.
Proof.
  intros LAYOUT FRAME DIMENSIONS WORDS COMPILE RESOLVE.
  destruct access as [array coordinates].
  unfold multi_tensor_lower_access in COMPILE.
  destruct(existsb(Pos.eqb(fst (array,coordinates)))pointers)eqn:MEMBER; [|discriminate].
  apply existsb_exists in MEMBER as [key [MEMBER SAME]]; apply Pos.eqb_eq in SAME; subst key.
  destruct(tensor_lower_access(fst (array,coordinates))dimensions (array,coordinates) codes)as [index|]eqn:INDEX; [|discriminate].
  inversion COMPILE; subst code.
  destruct(@multi_tensor_location_inverse initial sizes(exact_cell (array,coordinates) parameters)location RESOLVE)
    as [block [base [offset [POINTER [BOUND LOCATION]]]]].
  assert(SINGLE:tensor_pointer_locations(fst (array,coordinates))block base sizes(exact_cell (array,coordinates) parameters)=Some location).
  { unfold multi_tensor_locations in RESOLVE; rewrite POINTER in RESOLVE.
    change(tensor_pointer_locations(fst (array,coordinates))block base sizes(exact_cell (array,coordinates) parameters)=Some location)in RESOLVE.
    exact RESOLVE. }
  destruct(@tensor_backend_access_evaluation(fst (array,coordinates))block base dimensions sizes ge locals temps memory
    (array,coordinates) codes parameters index location DIMENSIONS WORDS INDEX SINGLE)
    as [actual [ACTUAL [SAME [TYPE EVAL]]]].
  exists block,base,actual; split; [exact SAME|split; [reflexivity|]].
  eapply memory_pointer_lvalue_evaluation.
  - rewrite FRAME by exact MEMBER; exact POINTER.
  - exact TYPE.
  - exact EVAL.
  - pose proof(@tensor_index_bounds sizes _ actual ACTUAL).
    pose proof(@tensor_layout_flag_sound sizes LAYOUT); unfold signed_range; pose proof Int.min_signed_neg; lia.
Qed.

Lemma multi_tensor_backend_reads initial sizes pointers dimensions ge locals temps memory
    accesses codes parameters read_codes locations loaded :
  tensor_layout_flag sizes=true -> temp_agree pointers initial temps ->
  tensor_dimension_view dimensions sizes temps ->
  Forall2(MemoryBody.operand_view ge locals temps memory)codes parameters ->
  multi_tensor_lower_reads pointers dimensions accesses codes=Some read_codes ->
  resolve_cells(map(fun access=>exact_cell access parameters)accesses)(multi_tensor_locations initial sizes)=Some locations ->
  load_locations locations memory=Some loaded ->
  Forall2(flat_value_view ge locals temps memory)read_codes loaded.
Proof.
  intros LAYOUT FRAME DIMENSIONS WORDS; revert read_codes locations loaded; induction accesses as [|access rest IH];
    intros read_codes locations loaded COMPILE RESOLVE LOAD.
  - cbn in COMPILE,RESOLVE; inversion COMPILE; inversion RESOLVE; subst.
    cbn in LOAD; inversion LOAD; constructor.
  - cbn [multi_tensor_lower_reads]in COMPILE.
    destruct(multi_tensor_lower_access pointers dimensions access codes)as [code|]eqn:CODE; [|discriminate].
    destruct(multi_tensor_lower_reads pointers dimensions rest codes)as [tail|]eqn:TAIL; [|discriminate].
    inversion COMPILE; subst read_codes; cbn [map resolve_cells]in RESOLVE.
    destruct(multi_tensor_locations initial sizes(exact_cell access parameters))as [location|]eqn:LOCATION; [|discriminate].
    destruct(resolve_cells(map(fun a=>exact_cell a parameters)rest)(multi_tensor_locations initial sizes))as [locations'|]eqn:REST; [|discriminate].
    inversion RESOLVE; subst locations; cbn [load_locations]in LOAD.
    destruct(location_load location memory)as [value|]eqn:VALUE; [|discriminate].
    destruct(load_locations locations' memory)as [values|]eqn:VALUES; [|discriminate].
    inversion LOAD; subst loaded; constructor.
    + destruct(@multi_tensor_backend_access initial sizes pointers dimensions ge locals temps memory access codes parameters code location
        LAYOUT FRAME DIMENSIONS WORDS CODE LOCATION)as [block [base [offset [SAME [TYPE LVALUE]]]]].
      subst location; split; [exact TYPE|]; eapply eval_Elvalue; [exact LVALUE|].
      rewrite TYPE; apply deref_loc_value with(chunk:=Mint32); [reflexivity|].
      cbn [Mem.loadv]; rewrite memory_pointer_buffer_address.
      pose proof(@memory_pointer_load_end memory block base offset value VALUE)as END.
      destruct(zle(memory_pointer_buffer_offset base offset+size_chunk Mint32)Ptrofs.modulus); [exact VALUE|lia].
    + eapply IH; eauto.
Qed.

Section BACKEND.
Variable initial:temp_env.
Variable sizes:list Z.
Hypothesis LAYOUT:tensor_layout_flag sizes=true.
Variable dimensions:list tensor_dimension_source.
Variable fe:genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge:genv.
Variable locals:env.
Variable pointers:list ident.
Definition multi_tensor_buffer_view state memory := state=RuntimeState(multi_tensor_locations initial sizes)memory.
Definition multi_tensor_buffer_protected := pointers++tensor_dimension_registers dimensions.
Definition multi_tensor_buffer_capability temps := temp_agree pointers initial temps /\ tensor_dimension_view dimensions sizes temps.
Lemma multi_tensor_buffer_capability_frame before after :
  temp_agree multi_tensor_buffer_protected before after ->
  multi_tensor_buffer_capability before -> multi_tensor_buffer_capability after.
Proof.
  intros FRAME [POINTERS DIMENSIONS]; split.
  - intros id MEMBER; rewrite(FRAME id)by(apply in_or_app; left; exact MEMBER); apply POINTERS; exact MEMBER.
  - eapply tensor_dimension_view_frame; [|exact DIMENSIONS].
    eapply temp_agree_weaken; [|exact FRAME]; intros id MEMBER; apply in_or_app; right; exact MEMBER.
Qed.

Definition multi_tensor_instruction_backend : MemoryFramedNested.instruction_backend fe ge locals
    multi_tensor_buffer_view multi_tensor_buffer_capability.
Proof.
  refine {|MemoryFramedNested.lower_instruction:=multi_tensor_lower_instruction pointers dimensions|}.
  intros instruction codes parameters code temps memory source target writes reads COMPILE WORDS RUN VIEW [POINTERS DIMENSIONS].
  unfold multi_tensor_lower_instruction in COMPILE.
  destruct(flat_integer_result(instruction_value instruction))eqn:INTEGER; [|discriminate].
  destruct(multi_tensor_lower_access pointers dimensions(instruction_write instruction)codes)as [write_code|]eqn:WRITE_CODE; [|discriminate].
  destruct(multi_tensor_lower_reads pointers dimensions(instruction_reads instruction)codes)as [read_codes|]eqn:READ_CODES; [|discriminate].
  destruct(compile_flat_value codes read_codes(instruction_value instruction))as [value_code|]eqn:VALUE_CODE; [|discriminate].
  inversion COMPILE; subst code; unfold multi_tensor_buffer_view in VIEW; subst source.
  destruct RUN as [WRITES [READS [write [read_locations [WRITE [READ [LOCATIONS ACTION]]]]]]].
  subst writes reads; destruct target as [locations final]; cbn in LOCATIONS,ACTION; subst locations.
  destruct ACTION as [loaded [value [LOAD [COMPUTE STORE]]]]; cbn [memory_reads memory_write memory_compute]in LOAD,COMPUTE,STORE.
  destruct(@multi_tensor_backend_access initial sizes pointers dimensions ge locals temps memory(instruction_write instruction)
    codes parameters write_code write LAYOUT POINTERS DIMENSIONS WORDS WRITE_CODE WRITE)
    as [block [base [offset [SAME [WRITE_TYPE LVALUE]]]]]; subst write.
  pose proof(@multi_tensor_backend_reads initial sizes pointers dimensions ge locals temps memory(instruction_reads instruction)
    codes parameters read_codes read_locations loaded LAYOUT POINTERS DIMENSIONS WORDS READ_CODES READ LOAD)as READ_EVALUATIONS.
  destruct(@compile_flat_value_evaluation(instruction_value instruction)codes read_codes value_code parameters loaded value
    ge locals temps memory WORDS READ_EVALUATIONS VALUE_CODE COMPUTE)as [VALUE_TYPE VALUE_EVAL].
  destruct(@flat_integer_result_correct(instruction_value instruction)parameters loaded value INTEGER COMPUTE)as [integer ->].
  exists final; split; [reflexivity|].
  eapply exec_Sassign with(loc:=block)(ofs:=Ptrofs.add base(Ptrofs.repr(4*offset)))(bf:=Full)(v:=Vint integer)(v2:=Vint integer).
  - exact LVALUE.
  - exact VALUE_EVAL.
  - rewrite VALUE_TYPE,WRITE_TYPE; reflexivity.
  - rewrite WRITE_TYPE; apply assign_loc_value with(chunk:=Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite memory_pointer_buffer_address.
    pose proof(@memory_pointer_store_end memory final block base offset(Vint integer)STORE)as END.
    destruct(zle(memory_pointer_buffer_offset base offset+size_chunk Mint32)Ptrofs.modulus); [exact STORE|lia].
Defined.

Definition compile_multi_tensor_buffer_loop layout bounds live pool loop :=
  if MemoryFramedNested.N.scratch_check pool(layout++multi_tensor_buffer_protected++live)then
    MemoryFramedNested.N.compile_nested_raw(multi_tensor_lower_instruction pointers dimensions)layout bounds pool loop
  else None.
Theorem compile_multi_tensor_buffer_loop_correct layout bounds live pool loop code parameters temps source target memory :
  compile_multi_tensor_buffer_loop layout bounds live pool loop=Some code ->
  MemoryFramedNested.N.A.typed_view layout parameters temps -> MemoryFramedNested.N.A.env_within bounds parameters ->
  GuardMemoryIRs.Loop.loop_semantics loop parameters source target ->
  multi_tensor_buffer_view source memory -> multi_tensor_buffer_capability temps ->
  exists target_temps target_memory,multi_tensor_buffer_view target target_memory /\
    multi_tensor_buffer_capability target_temps /\ temp_agree(layout++multi_tensor_buffer_protected++live)temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  unfold compile_multi_tensor_buffer_loop; intros COMPILE VIEW WITHIN RUN MEMORY CAPABILITY.
  destruct(MemoryFramedNested.N.scratch_check pool(layout++multi_tensor_buffer_protected++live))eqn:FRESH; [|discriminate].
  destruct(@MemoryFramedNested.compile_nested_correct fe ge locals multi_tensor_buffer_view multi_tensor_buffer_protected
    multi_tensor_buffer_capability multi_tensor_buffer_capability_frame multi_tensor_instruction_backend loop layout bounds pool code parameters
    temps source target memory(multi_tensor_buffer_protected++live)COMPILE(MemoryFramedNested.N.scratch_check_sound pool _ FRESH)
    WITHIN VIEW RUN MEMORY CAPABILITY ltac:(intros id MEMBER; apply in_or_app; left; exact MEMBER))
    as [target_temps [target_memory [TARGET [FRAME EXEC]]]].
  exists target_temps,target_memory; split; [exact TARGET|split; [|split; [exact FRAME|exact EXEC]]].
  eapply multi_tensor_buffer_capability_frame; [|exact CAPABILITY]; eapply temp_agree_weaken; [|exact FRAME].
  intros id MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
Qed.
End BACKEND.

Print Assumptions multi_tensor_location_at.
Print Assumptions multi_tensor_location_inverse.
Print Assumptions multi_tensor_backend_access.
Print Assumptions multi_tensor_backend_reads.
Print Assumptions multi_tensor_buffer_capability_frame.
Print Assumptions multi_tensor_instruction_backend.
Print Assumptions compile_multi_tensor_buffer_loop_correct.
