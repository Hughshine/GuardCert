From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCountedLoop ClightTempFrame CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryArrayBackend
  GuardMemoryFlatArrayBackend GuardMemoryBufferOffsets GuardMemoryPointerAccess GuardMemoryFramedNested GuardMemoryRectangles.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module MemoryFramedNested := FramedNestedClightFor GuardMemoryInstr GuardMemoryIRs.Loop.

Definition memory_lower_pointer_instruction pointer logical_array instruction codes : option statement :=
  if flat_integer_result (instruction_value instruction) then
    match compile_flat_array_access logical_array (instruction_write instruction) codes,
      compile_flat_array_reads logical_array (instruction_reads instruction) codes with
    | Some write,Some reads => match compile_flat_value codes
        (map (memory_pointer_lvalue pointer) reads) (instruction_value instruction) with
      | Some value => Some (Sassign (memory_pointer_lvalue pointer write) value)
      | None => None end
    | _,_ => None end
  else None.
Lemma memory_pointer_access_evaluation logical_array block base extent ge locals temps memory access codes parameters code location :
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  compile_flat_array_access logical_array access codes = Some code ->
  memory_pointer_buffer_locations logical_array block base extent (exact_cell access parameters) = Some location ->
  exists index, 0 <= index < extent /\
    location = MemoryLocation Mint32 block (memory_pointer_buffer_offset base index) /\ typeof code = type_int32s /\
    eval_expr ge locals temps memory code (Vint (Int.repr index)).
Proof.
  intros OPERANDS COMPILE RESOLVE.
  destruct access as [access_array terms]; destruct terms as [|term [|extra rest]]; try discriminate COMPILE.
  unfold compile_flat_array_access in COMPILE; destruct (Pos.eqb access_array logical_array) eqn:ARRAY; try discriminate.
  apply Pos.eqb_eq in ARRAY; subst access_array; inversion COMPILE; subst code.
  change (memory_pointer_buffer_locations logical_array block base extent
    (point_cell logical_array (dot_product (fst term) parameters+snd term)) = Some location) in RESOLVE.
  destruct (@memory_pointer_buffer_location_inverse logical_array block base extent _ _ RESOLVE) as [BOUND LOCATION].
  exists (dot_product (fst term) parameters+snd term); split; [exact BOUND|].
  split; [exact LOCATION|]; split; [apply flat_affine_type|apply flat_affine_evaluation; exact OPERANDS].
Qed.
Lemma memory_pointer_reads_evaluation extent pointer logical_array block base ge locals temps memory accesses codes parameters indices locations loaded :
  extent <= Int.max_signed+1 -> temps ! pointer = Some (Vptr block base) ->
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  compile_flat_array_reads logical_array accesses codes = Some indices ->
  resolve_cells (map (fun access => exact_cell access parameters) accesses)
    (memory_pointer_buffer_locations logical_array block base extent) = Some locations ->
  load_locations locations memory = Some loaded ->
  Forall2 (flat_value_view ge locals temps memory) (map (memory_pointer_lvalue pointer) indices) loaded.
Proof.
  intros EXTENT POINTER OPERANDS; revert indices locations loaded; induction accesses;
    intros indices locations loaded COMPILE RESOLVE LOAD.
  - cbn in COMPILE,RESOLVE; inversion COMPILE; inversion RESOLVE; subst.
    cbn in LOAD; inversion LOAD; constructor.
  - cbn [compile_flat_array_reads] in COMPILE.
    destruct (compile_flat_array_access logical_array a codes) as [index|] eqn:INDEX; try discriminate.
    destruct (compile_flat_array_reads logical_array accesses codes) as [rest|] eqn:REST; try discriminate.
    inversion COMPILE; subst indices.
    cbn [map resolve_cells] in RESOLVE.
    destruct (memory_pointer_buffer_locations logical_array block base extent (exact_cell a parameters))
      as [location|] eqn:LOCATION; try discriminate.
    destruct (resolve_cells (map (fun access => exact_cell access parameters) accesses)
      (memory_pointer_buffer_locations logical_array block base extent)) as [tail|] eqn:TAIL; try discriminate.
    inversion RESOLVE; subst locations.
    cbn [load_locations] in LOAD.
    destruct (location_load location memory) as [value|] eqn:VALUE; try discriminate.
    destruct (load_locations tail memory) as [values|] eqn:VALUES; try discriminate.
    inversion LOAD; subst loaded; cbn [map]; constructor.
    + destruct (@memory_pointer_access_evaluation logical_array block base extent ge locals temps memory
        a codes parameters index location OPERANDS INDEX LOCATION) as [offset [BOUND [SAME [TYPE EVAL]]]].
      subst location; split; [reflexivity|].
      eapply eval_Elvalue.
      * eapply memory_pointer_lvalue_evaluation; [exact POINTER|exact TYPE|exact EVAL|].
        change (-2147483648 <= offset <= 2147483647).
        change (extent <= 2147483648) in EXTENT; lia.
      * apply deref_loc_value with (chunk := Mint32); [reflexivity|].
        cbn [Mem.loadv]; rewrite memory_pointer_buffer_address.
        pose proof (@memory_pointer_load_end memory block base offset value VALUE) as END.
        destruct (zle (memory_pointer_buffer_offset base offset+size_chunk Mint32) Ptrofs.modulus); [exact VALUE|lia].
    + eapply IHaccesses; eauto.
Qed.

Section BACKEND.
Variable extent : Z.
Hypothesis EXTENT : extent <= Int.max_signed+1.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable pointer logical_array : ident.
Variable block : Values.block.
Variable base : ptrofs.
Definition memory_pointer_buffer_view state memory :=
  state = RuntimeState (memory_pointer_buffer_locations logical_array block base extent) memory.
Definition memory_pointer_capability temps := temps ! pointer = Some (Vptr block base).
Lemma memory_pointer_capability_frame before after : temp_agree [pointer] before after ->
  memory_pointer_capability before -> memory_pointer_capability after.
Proof. intros FRAME POINTER; unfold memory_pointer_capability in *; rewrite FRAME; [exact POINTER|cbn; auto]. Qed.
Definition memory_pointer_instruction_backend : MemoryFramedNested.instruction_backend fe ge locals
  memory_pointer_buffer_view memory_pointer_capability.
Proof.
  refine {| MemoryFramedNested.lower_instruction := memory_lower_pointer_instruction pointer logical_array |}.
  intros instruction codes parameters code temps memory source target writes reads COMPILE OPERANDS RUN VIEW POINTER.
  unfold memory_lower_pointer_instruction in COMPILE.
  destruct (flat_integer_result (instruction_value instruction)) eqn:INTEGER; try discriminate.
  destruct (compile_flat_array_access logical_array (instruction_write instruction) codes) as [write_index|]
    eqn:WRITE_CODE; try discriminate.
  destruct (compile_flat_array_reads logical_array (instruction_reads instruction) codes) as [read_indices|]
    eqn:READ_CODES; try discriminate.
  destruct (compile_flat_value codes (map (memory_pointer_lvalue pointer) read_indices)
    (instruction_value instruction)) as [value_code|] eqn:VALUE_CODE; try discriminate.
  inversion COMPILE; subst code.
  unfold memory_pointer_buffer_view in VIEW; subst source.
  destruct RUN as [WRITES [READS [write [read_locations [WRITE [READ [LOCATIONS ACTION]]]]]]].
  subst writes reads.
  destruct target as [locations final]; cbn in LOCATIONS,ACTION; subst locations.
  destruct ACTION as [loaded [value [LOAD [COMPUTE STORE]]]].
  cbn [memory_reads memory_write memory_compute] in LOAD,COMPUTE,STORE.
  destruct (@memory_pointer_access_evaluation logical_array block base extent ge locals temps memory
    (instruction_write instruction) codes parameters write_index write OPERANDS WRITE_CODE WRITE)
    as [index [BOUND [LOCATION [INDEX_TYPE INDEX_EVAL]]]].
  subst write.
  pose proof (@memory_pointer_reads_evaluation extent pointer logical_array block base ge locals temps memory
    (instruction_reads instruction) codes parameters read_indices read_locations loaded
    EXTENT POINTER OPERANDS READ_CODES READ LOAD) as READ_EVALUATIONS.
  destruct (@compile_flat_value_evaluation (instruction_value instruction) codes
    (map (memory_pointer_lvalue pointer) read_indices) value_code parameters loaded value ge locals temps memory
    OPERANDS READ_EVALUATIONS VALUE_CODE COMPUTE) as [VALUE_TYPE VALUE_EVAL].
  destruct (@flat_integer_result_correct (instruction_value instruction) parameters loaded value INTEGER COMPUTE)
    as [integer ->].
  exists final; split; [reflexivity|].
  eapply exec_Sassign with (loc := block) (ofs := Ptrofs.add base (Ptrofs.repr (4*index))) (bf := Full)
    (v := Vint integer) (v2 := Vint integer).
  - eapply memory_pointer_lvalue_evaluation; [exact POINTER|exact INDEX_TYPE|exact INDEX_EVAL|].
    change (-2147483648 <= index <= 2147483647).
    change (extent <= 2147483648) in EXTENT; lia.
  - exact VALUE_EVAL.
  - rewrite VALUE_TYPE; reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite memory_pointer_buffer_address.
    pose proof (@memory_pointer_store_end memory final block base index (Vint integer) STORE) as END.
    destruct (zle (memory_pointer_buffer_offset base index+size_chunk Mint32) Ptrofs.modulus); [exact STORE|lia].
Defined.
Definition compile_memory_pointer_buffer_loop layout bounds live pool loop :=
  if MemoryFramedNested.N.scratch_check pool (layout++pointer::live)
  then MemoryFramedNested.N.compile_nested_raw (memory_lower_pointer_instruction pointer logical_array) layout bounds pool loop
  else None.
Theorem compile_memory_pointer_buffer_loop_correct layout bounds live pool loop code parameters temps source target memory :
  compile_memory_pointer_buffer_loop layout bounds live pool loop = Some code ->
  MemoryFramedNested.N.A.typed_view layout parameters temps -> MemoryFramedNested.N.A.env_within bounds parameters ->
  GuardMemoryIRs.Loop.loop_semantics loop parameters source target ->
  memory_pointer_buffer_view source memory -> memory_pointer_capability temps ->
  exists target_temps target_memory, memory_pointer_buffer_view target target_memory /\
    memory_pointer_capability target_temps /\ temp_agree (layout++pointer::live) temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  unfold compile_memory_pointer_buffer_loop.
  intros COMPILE VIEW WITHIN RUN MEMORY POINTER.
  destruct (MemoryFramedNested.N.scratch_check pool (layout++pointer::live)) eqn:FRESH; try discriminate.
  destruct (@MemoryFramedNested.compile_nested_correct fe ge locals memory_pointer_buffer_view [pointer]
    memory_pointer_capability memory_pointer_capability_frame memory_pointer_instruction_backend loop
    layout bounds pool code parameters temps source target memory (pointer::live)
    COMPILE (MemoryFramedNested.N.scratch_check_sound pool _ FRESH) WITHIN VIEW RUN MEMORY POINTER
    ltac:(intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[]]; subst; cbn; auto))
    as [target_temps [target_memory [TARGET [FRAME EXEC]]]].
  exists target_temps,target_memory; repeat split; auto.
  eapply memory_pointer_capability_frame; [|exact POINTER].
  eapply temp_agree_weaken; [|exact FRAME].
  intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[]]; subst; apply in_or_app; right; cbn; auto.
Qed.
End BACKEND.
Print Assumptions memory_pointer_instruction_backend.
Print Assumptions compile_memory_pointer_buffer_loop_correct.
