From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCountedLoop ClightTempFrame CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryArrayBackend
  GuardMemoryFlatArrayBackend GuardMemoryBufferOffsets GuardMemoryPointerAccess GuardMemoryFramedNested GuardMemoryRectangles
  GuardMemoryPointerBackend GuardMemoryMultiPointerCells.
From GuardMemory Require Import GuardMemoryMultiPointerBackend.
From GuardMemory Require Import GuardMemoryWindowCells.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The protected identifiers are checked by the lowerer and excluded from its
    scratch pool.  The registry retains their entry bindings.  No entry typing
    assumption is required for an unused pointer. *)
Lemma window_multi_pointer_backend_access initial lower upper pointers access codes parameters ge locals temps memory code location :
  signed_range lower -> signed_range (upper-1) -> temp_agree pointers initial temps ->
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  memory_lower_multi_pointer_access pointers access codes = Some code ->
  window_multi_pointer_locations initial lower upper (exact_cell access parameters) = Some location ->
  exists block base index,
    location = MemoryLocation Mint32 block (memory_pointer_buffer_offset base index) /\
    typeof code = type_int32s /\
    eval_lvalue ge locals temps memory code block (Ptrofs.add base (Ptrofs.repr (4*index))) Full.
Proof.
  intros LOW HIGH FRAME OPERANDS COMPILE RESOLVE.
  unfold memory_lower_multi_pointer_access in COMPILE.
  destruct (existsb (Pos.eqb (fst access)) pointers) eqn:MEMBER; [|discriminate].
  apply existsb_exists in MEMBER as [key [MEMBER SAME]]; apply Pos.eqb_eq in SAME; subst key.
  unfold compile_flat_array_access in COMPILE.
  destruct access as [identifier terms]; destruct terms as [|term [|extra rest]]; try discriminate COMPILE.
  cbn [fst] in COMPILE,MEMBER; rewrite Pos.eqb_refl in COMPILE; inversion COMPILE; subst code.
  change (window_multi_pointer_locations initial lower upper
    (point_cell identifier (dot_product (fst term) parameters+snd term)) = Some location) in RESOLVE.
  destruct (@window_multi_pointer_location_inverse initial lower upper _ _ RESOLVE)
    as [block [base [index [POINTER [CELL [RANGE SAME]]]]]].
  cbn [arr_id arr_index] in POINTER,CELL; inversion CELL; subst index.
  exists block,base,(dot_product (fst term) parameters+snd term); split; [exact SAME|].
  split; [reflexivity|].
  eapply memory_pointer_lvalue_evaluation.
  - rewrite FRAME by exact MEMBER; exact POINTER.
  - apply flat_affine_type.
  - apply flat_affine_evaluation; exact OPERANDS.
  - unfold signed_range in *; lia.
Qed.
Lemma window_multi_pointer_backend_reads initial lower upper pointers ge locals temps memory accesses codes parameters read_codes locations loaded :
  signed_range lower -> signed_range (upper-1) -> temp_agree pointers initial temps ->
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  memory_lower_multi_pointer_reads pointers accesses codes = Some read_codes ->
  resolve_cells (map (fun access => exact_cell access parameters) accesses)
    (window_multi_pointer_locations initial lower upper) = Some locations ->
  load_locations locations memory = Some loaded ->
  Forall2 (flat_value_view ge locals temps memory) read_codes loaded.
Proof.
  intros LOW HIGH FRAME OPERANDS; revert read_codes locations loaded; induction accesses as [|access accesses IH];
    intros read_codes locations loaded COMPILE RESOLVE LOAD.
  - cbn in COMPILE,RESOLVE; inversion COMPILE; inversion RESOLVE; subst.
    cbn in LOAD; inversion LOAD; constructor.
  - cbn [memory_lower_multi_pointer_reads] in COMPILE.
    destruct (memory_lower_multi_pointer_access pointers access codes) as [code|] eqn:CODE; [|discriminate].
    destruct (memory_lower_multi_pointer_reads pointers accesses codes) as [rest|] eqn:REST; [|discriminate].
    inversion COMPILE; subst read_codes.
    cbn [map resolve_cells] in RESOLVE.
    destruct (window_multi_pointer_locations initial lower upper (exact_cell access parameters)) as [location|] eqn:LOCATION; [|discriminate].
    destruct (resolve_cells (map (fun access => exact_cell access parameters) accesses)
      (window_multi_pointer_locations initial lower upper)) as [tail|] eqn:TAIL; [|discriminate].
    inversion RESOLVE; subst locations; cbn [load_locations] in LOAD.
    destruct (location_load location memory) as [value|] eqn:VALUE; [|discriminate].
    destruct (load_locations tail memory) as [values|] eqn:VALUES; [|discriminate].
    inversion LOAD; subst loaded; constructor.
    + destruct (@window_multi_pointer_backend_access initial lower upper pointers access codes parameters ge locals temps memory code location
        LOW HIGH FRAME OPERANDS CODE LOCATION) as [block [base [index [SAME [TYPE LVALUE]]]]].
      subst location; split; [exact TYPE|].
      eapply eval_Elvalue; [exact LVALUE|].
      rewrite TYPE; apply deref_loc_value with (chunk := Mint32); [reflexivity|].
      cbn [Mem.loadv]; rewrite memory_pointer_buffer_address.
      pose proof (@memory_pointer_load_end memory block base index value VALUE) as END.
      destruct (zle (memory_pointer_buffer_offset base index+size_chunk Mint32) Ptrofs.modulus); [exact VALUE|lia].
    + eapply IH; eauto.
Qed.

Section BACKEND.
Variable initial : temp_env.
Variable lower upper : Z.
Hypothesis LOW : signed_range lower.
Hypothesis HIGH : signed_range (upper-1).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable pointers : list ident.
Definition window_multi_pointer_buffer_view state memory :=
  state = RuntimeState (window_multi_pointer_locations initial lower upper) memory.
Definition window_multi_pointer_capability temps := temp_agree pointers initial temps.
Lemma window_multi_pointer_capability_frame before after : temp_agree pointers before after ->
  window_multi_pointer_capability before -> window_multi_pointer_capability after.
Proof. intros FRAME BEFORE identifier MEMBER; rewrite FRAME by exact MEMBER; apply BEFORE; exact MEMBER. Qed.
Definition window_multi_pointer_instruction_backend : MemoryFramedNested.instruction_backend fe ge locals
  window_multi_pointer_buffer_view window_multi_pointer_capability.
Proof.
  refine {| MemoryFramedNested.lower_instruction := memory_lower_multi_pointer_instruction pointers |}.
  intros instruction codes parameters code temps memory source target writes reads COMPILE OPERANDS RUN VIEW FRAME.
  unfold memory_lower_multi_pointer_instruction in COMPILE.
  destruct (flat_integer_result (instruction_value instruction)) eqn:INTEGER; [|discriminate].
  destruct (memory_lower_multi_pointer_access pointers (instruction_write instruction) codes) as [write_code|] eqn:WRITE_CODE; [|discriminate].
  destruct (memory_lower_multi_pointer_reads pointers (instruction_reads instruction) codes) as [read_codes|] eqn:READ_CODES; [|discriminate].
  destruct (compile_flat_value codes read_codes (instruction_value instruction)) as [value_code|] eqn:VALUE_CODE; [|discriminate].
  inversion COMPILE; subst code; unfold window_multi_pointer_buffer_view in VIEW; subst source.
  destruct RUN as [WRITES [READS [write [read_locations [WRITE [READ [LOCATIONS ACTION]]]]]]].
  subst writes reads; destruct target as [locations final]; cbn in LOCATIONS,ACTION; subst locations.
  destruct ACTION as [loaded [value [LOAD [COMPUTE STORE]]]].
  cbn [memory_reads memory_write memory_compute] in LOAD,COMPUTE,STORE.
  destruct (@window_multi_pointer_backend_access initial lower upper pointers (instruction_write instruction) codes parameters ge locals temps memory
    write_code write LOW HIGH FRAME OPERANDS WRITE_CODE WRITE) as [block [base [index [SAME [WRITE_TYPE LVALUE]]]]].
  subst write.
  pose proof (@window_multi_pointer_backend_reads initial lower upper pointers ge locals temps memory
    (instruction_reads instruction) codes parameters read_codes read_locations loaded LOW HIGH FRAME OPERANDS READ_CODES READ LOAD) as READ_EVALUATIONS.
  destruct (@compile_flat_value_evaluation (instruction_value instruction) codes read_codes value_code parameters loaded value ge locals temps memory
    OPERANDS READ_EVALUATIONS VALUE_CODE COMPUTE) as [VALUE_TYPE VALUE_EVAL].
  destruct (@flat_integer_result_correct (instruction_value instruction) parameters loaded value INTEGER COMPUTE) as [integer ->].
  exists final; split; [reflexivity|].
  eapply exec_Sassign with (loc := block) (ofs := Ptrofs.add base (Ptrofs.repr (4*index))) (bf := Full)
    (v := Vint integer) (v2 := Vint integer).
  - exact LVALUE.
  - exact VALUE_EVAL.
  - rewrite VALUE_TYPE,WRITE_TYPE; reflexivity.
  - rewrite WRITE_TYPE; apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite memory_pointer_buffer_address.
    pose proof (@memory_pointer_store_end memory final block base index (Vint integer) STORE) as END.
    destruct (zle (memory_pointer_buffer_offset base index+size_chunk Mint32) Ptrofs.modulus); [exact STORE|lia].
Defined.
Definition compile_window_multi_pointer_buffer_loop layout bounds live pool loop :=
  if MemoryFramedNested.N.scratch_check pool (layout++pointers++live)
  then MemoryFramedNested.N.compile_nested_raw (memory_lower_multi_pointer_instruction pointers) layout bounds pool loop
  else None.
Theorem compile_window_multi_pointer_buffer_loop_correct layout bounds live pool loop code parameters temps source target memory :
  compile_window_multi_pointer_buffer_loop layout bounds live pool loop = Some code ->
  MemoryFramedNested.N.A.typed_view layout parameters temps -> MemoryFramedNested.N.A.env_within bounds parameters ->
  GuardMemoryIRs.Loop.loop_semantics loop parameters source target ->
  window_multi_pointer_buffer_view source memory -> window_multi_pointer_capability temps ->
  exists target_temps target_memory, window_multi_pointer_buffer_view target target_memory /\
    window_multi_pointer_capability target_temps /\ temp_agree (layout++pointers++live) temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  unfold compile_window_multi_pointer_buffer_loop; intros COMPILE VIEW WITHIN RUN MEMORY FRAME.
  destruct (MemoryFramedNested.N.scratch_check pool (layout++pointers++live)) eqn:FRESH; [|discriminate].
  destruct (@MemoryFramedNested.compile_nested_correct fe ge locals window_multi_pointer_buffer_view pointers
    window_multi_pointer_capability window_multi_pointer_capability_frame window_multi_pointer_instruction_backend loop
    layout bounds pool code parameters temps source target memory (pointers++live)
    COMPILE (MemoryFramedNested.N.scratch_check_sound pool _ FRESH) WITHIN VIEW RUN MEMORY FRAME
    ltac:(intros identifier MEMBER; apply in_or_app; left; exact MEMBER))
    as [target_temps [target_memory [TARGET [AGREE EXEC]]]].
  exists target_temps,target_memory; repeat split; auto.
  eapply window_multi_pointer_capability_frame; [|exact FRAME].
  eapply temp_agree_weaken; [|exact AGREE].
  intros identifier MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
Qed.
End BACKEND.
Print Assumptions window_multi_pointer_backend_access.
Print Assumptions window_multi_pointer_backend_reads.
Print Assumptions window_multi_pointer_instruction_backend.
Print Assumptions compile_window_multi_pointer_buffer_loop_correct.
