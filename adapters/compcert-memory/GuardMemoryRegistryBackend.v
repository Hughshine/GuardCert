From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightIndexedArray ClightRectangularStore ClightTempFrame
  CompCertMemoryActions CompCertStoreSchedule.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryPolyhedral GuardMemoryArrayBackend GuardMemoryFlatArrayBackend GuardMemoryMultipleArrays.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_array_descriptor := MemoryArrayDescriptor {
  memory_descriptor_id : ident;
  memory_descriptor_variable : ident;
  memory_descriptor_shape : rectangle_shape
}.

Fixpoint memory_find_array descriptors array : option memory_array_descriptor :=
  match descriptors with
  | [] => None
  | descriptor::rest => if Pos.eqb array (memory_descriptor_id descriptor)
      then Some descriptor else memory_find_array rest array
  end.
Definition memory_compile_registry_access descriptors access codes : option expr :=
  match access with
  | (array,[term]) => match memory_find_array descriptors array with
      | Some descriptor => Some (indexed_array_lvalue (memory_descriptor_shape descriptor)
          (memory_descriptor_variable descriptor) (flat_affine_expression codes term))
      | None => None end
  | _ => None end.
Fixpoint memory_compile_registry_reads descriptors accesses codes : option (list expr) :=
  match accesses with
  | [] => Some []
  | access::rest => match memory_compile_registry_access descriptors access codes,
      memory_compile_registry_reads descriptors rest codes with
    | Some code,Some codes => Some (code::codes) | _,_ => None end
  end.
Definition memory_lower_registry_instruction descriptors instruction codes : option statement :=
  if flat_integer_result (instruction_value instruction) then
    match memory_compile_registry_access descriptors (instruction_write instruction) codes,
      memory_compile_registry_reads descriptors (instruction_reads instruction) codes with
    | Some write,Some reads => match compile_flat_value codes reads (instruction_value instruction) with
      | Some value => Some (Sassign write value) | None => None end
    | _,_ => None end
  else None.

Definition memory_descriptor_binding ge locals descriptor entry :=
  memory_array_id entry = memory_descriptor_id descriptor /\
  memory_array_extent entry = rectangle_extent (memory_descriptor_shape descriptor) /\
  rectangle_layout_valid (memory_descriptor_shape descriptor) /\
  rect_array_binding (memory_descriptor_shape descriptor) ge locals
    (memory_descriptor_variable descriptor) (memory_array_block entry).

Lemma memory_registry_access_description ge locals descriptors entries access codes code parameters location :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  memory_compile_registry_access descriptors access codes = Some code ->
  memory_array_registry entries (exact_cell access parameters) = Some location ->
  exists descriptor index,
    code = indexed_array_lvalue (memory_descriptor_shape descriptor)
      (memory_descriptor_variable descriptor) (flat_affine_expression codes (hd ([],0) (snd access))) /\
    rectangle_layout_valid (memory_descriptor_shape descriptor) /\
    rect_array_binding (memory_descriptor_shape descriptor) ge locals
      (memory_descriptor_variable descriptor) (location_block location) /\
    0 <= index < rectangle_extent (memory_descriptor_shape descriptor) /\
    location = MemoryLocation Mint32 (location_block location) (4*index) /\
    index = dot_product (fst (hd ([],0) (snd access))) parameters + snd (hd ([],0) (snd access)).
Proof.
  intros RELATED; destruct access as [array terms]; destruct terms as [|term [|extra tail]];
    try discriminate; cbn [memory_compile_registry_access].
  induction RELATED as [|descriptor entry descriptors entries [ID [EXTENT [VALID BINDING]]] RELATED IH].
  - discriminate.
  - cbn [memory_find_array memory_array_registry exact_cell arr_id].
    rewrite ID.
    destruct (Pos.eqb array (memory_descriptor_id descriptor)) eqn:SAME.
    + intros COMPILE RESOLVE; inversion COMPILE; subst code.
      change (flat_array_locations (memory_descriptor_id descriptor) (memory_array_block entry)
        (memory_array_extent entry) (point_cell array (dot_product (fst term) parameters + snd term)) = Some location) in RESOLVE.
      apply Pos.eqb_eq in SAME; subst array; rewrite <- ID in RESOLVE.
      destruct (@flat_array_location_inverse _ _ _ _ _ RESOLVE) as [BOUND LOCATION].
      rewrite EXTENT in BOUND; subst location.
      exists descriptor,(dot_product (fst term) parameters + snd term).
      split; [reflexivity|]; split; [exact VALID|]; split; [exact BINDING|];
        split; [exact BOUND|]; split; reflexivity.
    + intros COMPILE RESOLVE; apply IH; assumption.
Qed.

Lemma memory_registry_access_evaluation ge locals temps memory descriptors entries access codes code parameters location :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  memory_compile_registry_access descriptors access codes = Some code ->
  memory_array_registry entries (exact_cell access parameters) = Some location ->
  typeof code = type_int32s /\ location_chunk location = Mint32 /\
  0 <= location_offset location <= Ptrofs.max_unsigned /\
  location_offset location + size_chunk Mint32 <= Ptrofs.modulus /\
  eval_lvalue ge locals temps memory code (location_block location)
    (Ptrofs.repr (location_offset location)) Full.
Proof.
  intros ARRAYS OPERANDS COMPILE RESOLVE.
  destruct (@memory_registry_access_description ge locals descriptors entries access codes code parameters location
    ARRAYS COMPILE RESOLVE) as [descriptor [index [CODE [VALID [BINDING [BOUND [LOCATION INDEX]]]]]]].
  rewrite CODE; split; [reflexivity|].
  assert (OFFSET : location_offset location = 4*index) by (rewrite LOCATION; reflexivity).
  assert (CHUNK : location_chunk location = Mint32) by (rewrite LOCATION; reflexivity).
  split; [exact CHUNK|].
  split; [rewrite OFFSET; apply (@rect_small_offset_bound _ VALID); lia|].
  split.
  - rewrite OFFSET; change (size_chunk Mint32) with 4.
    pose proof (@rect_small_offset_bound _ VALID (4*index+4) ltac:(lia));
      unfold Ptrofs.max_unsigned in *; lia.
  - rewrite OFFSET; eapply indexed_array_lvalue_evaluation;
      [exact VALID|apply flat_affine_type|exact BINDING| |exact BOUND].
    rewrite INDEX; apply flat_affine_evaluation; exact OPERANDS.
Qed.

Lemma memory_registry_reads_evaluation ge locals temps memory descriptors entries accesses codes parameters read_codes locations loaded :
  Forall2 (memory_descriptor_binding ge locals) descriptors entries ->
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  memory_compile_registry_reads descriptors accesses codes = Some read_codes ->
  resolve_cells (map (fun access => exact_cell access parameters) accesses)
    (memory_array_registry entries) = Some locations ->
  load_locations locations memory = Some loaded ->
  Forall2 (flat_value_view ge locals temps memory) read_codes loaded.
Proof.
  intros ARRAYS OPERANDS; revert read_codes locations loaded; induction accesses;
    intros read_codes locations loaded COMPILE RESOLVE LOAD.
  - cbn in COMPILE,RESOLVE; inversion COMPILE; inversion RESOLVE; subst.
    cbn in LOAD; inversion LOAD; constructor.
  - cbn [memory_compile_registry_reads] in COMPILE.
    destruct (memory_compile_registry_access descriptors a codes) as [code|] eqn:CODE; try discriminate.
    destruct (memory_compile_registry_reads descriptors accesses codes) as [rest|] eqn:REST; try discriminate.
    inversion COMPILE; subst read_codes; cbn [map resolve_cells] in RESOLVE.
    destruct (memory_array_registry entries (exact_cell a parameters)) as [location|] eqn:LOCATION; try discriminate.
    destruct (resolve_cells (map (fun access => exact_cell access parameters) accesses)
      (memory_array_registry entries)) as [tail|] eqn:TAIL; try discriminate.
    inversion RESOLVE; subst locations; cbn [load_locations] in LOAD.
    destruct (location_load location memory) as [value|] eqn:VALUE; try discriminate.
    destruct (load_locations tail memory) as [values|] eqn:VALUES; try discriminate.
    inversion LOAD; subst loaded; constructor.
    + destruct (@memory_registry_access_evaluation ge locals temps memory descriptors entries a codes code parameters location
        ARRAYS OPERANDS CODE LOCATION) as [TYPE [CHUNK [OFFSET [END EVAL]]]].
      split; [exact TYPE|]; eapply eval_Elvalue; [exact EVAL|].
      rewrite TYPE; apply deref_loc_value with (chunk := Mint32); [reflexivity|].
      unfold location_load in VALUE; rewrite CHUNK in VALUE.
      cbn [Mem.loadv]; rewrite Ptrofs.unsigned_repr by exact OFFSET.
      destruct (zle (location_offset location+size_chunk Mint32) Ptrofs.modulus); [exact VALUE|lia].
    + eapply IHaccesses; eauto.
Qed.

Section BACKEND.
Variable descriptors : list memory_array_descriptor.
Variable entries : list memory_array_entry.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Hypothesis ARRAYS : Forall2 (memory_descriptor_binding ge locals) descriptors entries.
Definition memory_registry_view state memory := state = RuntimeState (memory_array_registry entries) memory.
Definition memory_registry_instruction_backend : MemoryBody.instruction_backend fe ge locals memory_registry_view.
Proof.
  refine {| MemoryBody.lower_instruction := memory_lower_registry_instruction descriptors |}.
  intros instruction codes parameters code temps memory source target writes reads COMPILE OPERANDS RUN VIEW.
  unfold memory_lower_registry_instruction in COMPILE.
  destruct (flat_integer_result (instruction_value instruction)) eqn:INTEGER; try discriminate.
  destruct (memory_compile_registry_access descriptors (instruction_write instruction) codes) as [write_code|]
    eqn:WRITE_CODE; try discriminate.
  destruct (memory_compile_registry_reads descriptors (instruction_reads instruction) codes) as [read_codes|]
    eqn:READ_CODES; try discriminate.
  destruct (compile_flat_value codes read_codes (instruction_value instruction)) as [value_code|]
    eqn:VALUE_CODE; try discriminate.
  inversion COMPILE; subst code; unfold memory_registry_view in VIEW; subst source.
  destruct RUN as [WRITES [READS [write [read_locations [WRITE [READ [LOCATIONS ACTION]]]]]]].
  subst writes reads; destruct target as [locations final]; cbn in LOCATIONS,ACTION; subst locations.
  destruct ACTION as [loaded [value [LOAD [COMPUTE STORE]]]].
  cbn [memory_reads memory_write memory_compute] in LOAD,COMPUTE,STORE.
  destruct (@memory_registry_access_evaluation ge locals temps memory descriptors entries
    (instruction_write instruction) codes write_code parameters write ARRAYS OPERANDS WRITE_CODE WRITE)
    as [WRITE_TYPE [CHUNK [OFFSET [END WRITE_EVAL]]]].
  pose proof (@memory_registry_reads_evaluation ge locals temps memory descriptors entries
    (instruction_reads instruction) codes parameters read_codes read_locations loaded ARRAYS OPERANDS READ_CODES READ LOAD)
    as READ_EVALUATIONS.
  destruct (@compile_flat_value_evaluation (instruction_value instruction) codes read_codes value_code parameters
    loaded value ge locals temps memory OPERANDS READ_EVALUATIONS VALUE_CODE COMPUTE) as [VALUE_TYPE VALUE_EVAL].
  destruct (@flat_integer_result_correct (instruction_value instruction) parameters loaded value INTEGER COMPUTE)
    as [integer ->].
  exists final; split; [reflexivity|].
  eapply exec_Sassign with (loc := location_block write) (ofs := Ptrofs.repr (location_offset write))
    (bf := Full) (v := Vint integer) (v2 := Vint integer).
  - exact WRITE_EVAL.
  - exact VALUE_EVAL.
  - rewrite VALUE_TYPE,WRITE_TYPE; reflexivity.
  - rewrite WRITE_TYPE; apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    unfold location_store in STORE; rewrite CHUNK in STORE.
    cbn [Mem.storev]; rewrite Ptrofs.unsigned_repr by exact OFFSET.
    destruct (zle (location_offset write+size_chunk Mint32) Ptrofs.modulus); [exact STORE|lia].
Defined.
Definition compile_memory_registry_loop layout bounds live pool loop :=
  MemoryNested.checked_compile_nested_raw (memory_lower_registry_instruction descriptors)
    layout bounds live pool loop.
Theorem compile_memory_registry_loop_correct layout bounds live pool loop code parameters temps source target memory :
  compile_memory_registry_loop layout bounds live pool loop = Some code ->
  MemoryNested.A.typed_view layout parameters temps -> MemoryNested.A.env_within bounds parameters ->
  GuardMemoryIRs.Loop.loop_semantics loop parameters source target ->
  memory_registry_view source memory ->
  exists target_temps target_memory, memory_registry_view target target_memory /\
    temp_agree (layout++live) temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  unfold compile_memory_registry_loop,MemoryNested.checked_compile_nested_raw.
  intros COMPILE VIEW WITHIN RUN MEMORY.
  destruct (MemoryNested.scratch_check pool (layout++live)) eqn:FRESH; try discriminate.
  eapply MemoryNested.compile_nested_correct with (backend := memory_registry_instruction_backend); eauto.
  apply MemoryNested.scratch_check_sound; exact FRESH.
Qed.
End BACKEND.
Print Assumptions memory_registry_access_evaluation.
Print Assumptions memory_registry_instruction_backend.
Print Assumptions compile_memory_registry_loop_correct.
