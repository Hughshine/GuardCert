From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightIndexedArray ClightRectangularStore ClightCondition ClightTempFrame
  CompCertMemoryActions CompCertStoreSchedule.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryPolyhedral GuardMemoryArrayBackend.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The instruction determines its accesses and scalar computation. The backend
    checks array identities and dimensions, then encodes arbitrary affine
    indices and arithmetic over the actual loaded values. *)
Fixpoint flat_linear_expression (codes : list expr) coefficients : expr :=
  match codes,coefficients with
  | code::rest,coefficient::tail => operand_sum (operand_product code coefficient)
      (flat_linear_expression rest tail)
  | _,_ => rect_constant 0
  end.
Definition flat_affine_expression codes term :=
  operand_sum (flat_linear_expression codes (fst term)) (rect_constant (snd term)).
Lemma flat_linear_type codes coefficients : typeof (flat_linear_expression codes coefficients) = type_int32s.
Proof. destruct codes,coefficients; reflexivity. Qed.
Lemma flat_affine_type codes term : typeof (flat_affine_expression codes term) = type_int32s.
Proof. reflexivity. Qed.
Lemma flat_linear_evaluation ge locals temps memory codes parameters coefficients :
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  eval_expr ge locals temps memory (flat_linear_expression codes coefficients)
    (Vint (Int.repr (dot_product coefficients parameters))).
Proof.
  intro OPERANDS; revert coefficients; induction OPERANDS as [|code value codes values OPERAND REST IH];
    intros coefficients; destruct coefficients; cbn [flat_linear_expression dot_product];
    try apply rect_constant_evaluation.
  destruct OPERAND as [TYPE EVAL].
  replace (z*value) with (value*z) by ring.
  apply operand_sum_evaluation; [reflexivity|apply flat_linear_type| |apply IH].
  apply operand_product_evaluation; assumption.
Qed.
Lemma flat_affine_evaluation ge locals temps memory codes parameters term :
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  eval_expr ge locals temps memory (flat_affine_expression codes term)
    (Vint (Int.repr (dot_product (fst term) parameters + snd term))).
Proof.
  intro OPERANDS; unfold flat_affine_expression; apply operand_sum_evaluation;
    [apply flat_linear_type|apply rect_constant_type|apply flat_linear_evaluation; exact OPERANDS|apply rect_constant_evaluation].
Qed.
Definition compile_flat_array_access logical_array access codes : option expr :=
  match access with
  | (array,[term]) => if Pos.eqb array logical_array then Some (flat_affine_expression codes term) else None
  | _ => None end.
Fixpoint compile_flat_array_reads logical_array accesses codes : option (list expr) :=
  match accesses with
  | [] => Some []
  | access::rest => match compile_flat_array_access logical_array access codes,
      compile_flat_array_reads logical_array rest codes with
    | Some index,Some indices => Some (index::indices) | _,_ => None end
  end.
Fixpoint compile_flat_value codes reads value : option expr :=
  match value with
  | ConstantValue z => Some (rect_constant z)
  | ParameterValue index => nth_error codes index
  | LoadedValue index => nth_error reads index
  | AddValue first second | SubValue first second | MulValue first second =>
    match compile_flat_value codes reads first,compile_flat_value codes reads second with
    | Some lhs,Some rhs => Some (Ebinop
        (match value with AddValue _ _ => Oadd | SubValue _ _ => Osub | _ => Omul end)
        lhs rhs type_int32s)
    | _,_ => None end
  end.
Definition flat_integer_result value := match value with LoadedValue _ => false | _ => true end.
Definition lower_flat_array_instruction base array logical_array instruction codes : option statement :=
  if flat_integer_result (instruction_value instruction) then
    match compile_flat_array_access logical_array (instruction_write instruction) codes,
      compile_flat_array_reads logical_array (instruction_reads instruction) codes with
    | Some write,Some reads => match compile_flat_value codes
        (map (indexed_array_lvalue base array) reads) (instruction_value instruction) with
      | Some value => Some (Sassign (indexed_array_lvalue base array write) value)
      | None => None end
    | _,_ => None end
  else None.

Lemma compile_flat_array_access_evaluation base logical_array block ge locals temps memory access codes parameters code location :
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  compile_flat_array_access logical_array access codes = Some code ->
  flat_array_locations logical_array block (rectangle_extent base) (exact_cell access parameters) = Some location ->
  exists index, 0 <= index < rectangle_extent base /\
    location = MemoryLocation Mint32 block (4*index) /\ typeof code = type_int32s /\
    eval_expr ge locals temps memory code (Vint (Int.repr index)).
Proof.
  intros OPERANDS COMPILE RESOLVE.
  destruct access as [access_array terms]; destruct terms as [|term [|extra rest]]; try discriminate COMPILE.
  unfold compile_flat_array_access in COMPILE; destruct (Pos.eqb access_array logical_array) eqn:ARRAY; try discriminate.
  apply Pos.eqb_eq in ARRAY; subst access_array; inversion COMPILE; subst code.
  change (flat_array_locations logical_array block (rectangle_extent base)
    (point_cell logical_array (dot_product (fst term) parameters+snd term)) = Some location) in RESOLVE.
  destruct (@flat_array_location_inverse logical_array block (rectangle_extent base) _ _ RESOLVE) as [BOUND LOCATION].
  exists (dot_product (fst term) parameters+snd term); split; [exact BOUND|].
  split; [exact LOCATION|]; split; [apply flat_affine_type|apply flat_affine_evaluation; exact OPERANDS].
Qed.

Definition flat_value_view ge locals temps memory code value :=
  typeof code = type_int32s /\ eval_expr ge locals temps memory code value.
Lemma flat_forall2_nth {A B} (R : A -> B -> Prop) xs ys : Forall2 R xs ys ->
  forall index x y, nth_error xs index = Some x -> nth_error ys index = Some y -> R x y.
Proof.
  intro RELATED; induction RELATED as [|head other xs ys HEAD RELATED IHRELATED]; intros index x y X Y; destruct index; cbn in X,Y;
    try discriminate; [inversion X; inversion Y; subst; assumption|eapply IHRELATED; eauto].
Qed.
Lemma compile_flat_value_evaluation value : forall codes reads code parameters loaded result ge locals temps memory,
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  Forall2 (flat_value_view ge locals temps memory) reads loaded ->
  compile_flat_value codes reads value = Some code -> evaluate_value parameters loaded value = Some result ->
  flat_value_view ge locals temps memory code result.
Proof.
  induction value; intros codes reads code parameters loaded result ge locals temps memory OPERANDS READS COMPILE VALUE.
  - cbn in COMPILE,VALUE; inversion COMPILE; inversion VALUE; subst.
    split; [apply rect_constant_type|apply rect_constant_evaluation].
  - cbn in COMPILE,VALUE; destruct (nth_error parameters n) as [z|] eqn:PARAMETER; try discriminate.
    inversion VALUE; subst result; exact (@flat_forall2_nth _ _ _ _ _ OPERANDS n code z COMPILE PARAMETER).
  - cbn in COMPILE,VALUE; exact (@flat_forall2_nth _ _ _ _ _ READS n code result COMPILE VALUE).
  - cbn [compile_flat_value] in COMPILE.
    destruct (compile_flat_value codes reads value1) as [first|] eqn:FIRST; try discriminate.
    destruct (compile_flat_value codes reads value2) as [second|] eqn:SECOND; try discriminate.
    inversion COMPILE; subst code.
    cbn [evaluate_value] in VALUE.
    destruct (evaluate_value parameters loaded value1) as [v1|] eqn:V1; try discriminate.
    destruct v1; try discriminate.
    destruct (evaluate_value parameters loaded value2) as [v2|] eqn:V2; try discriminate.
    destruct v2; try discriminate; inversion VALUE; subst result.
    destruct (IHvalue1 _ _ _ _ _ _ _ _ _ _ OPERANDS READS FIRST V1) as [TYPE1 EVAL1].
    destruct (IHvalue2 _ _ _ _ _ _ _ _ _ _ OPERANDS READS SECOND V2) as [TYPE2 EVAL2].
    split; [reflexivity|].
    eapply eval_Ebinop; [exact EVAL1|exact EVAL2|rewrite TYPE1,TYPE2; reflexivity].
  - cbn [compile_flat_value] in COMPILE.
    destruct (compile_flat_value codes reads value1) as [first|] eqn:FIRST; try discriminate.
    destruct (compile_flat_value codes reads value2) as [second|] eqn:SECOND; try discriminate.
    inversion COMPILE; subst code.
    cbn [evaluate_value] in VALUE.
    destruct (evaluate_value parameters loaded value1) as [v1|] eqn:V1; try discriminate.
    destruct v1; try discriminate.
    destruct (evaluate_value parameters loaded value2) as [v2|] eqn:V2; try discriminate.
    destruct v2; try discriminate; inversion VALUE; subst result.
    destruct (IHvalue1 _ _ _ _ _ _ _ _ _ _ OPERANDS READS FIRST V1) as [TYPE1 EVAL1].
    destruct (IHvalue2 _ _ _ _ _ _ _ _ _ _ OPERANDS READS SECOND V2) as [TYPE2 EVAL2].
    split; [reflexivity|].
    eapply eval_Ebinop; [exact EVAL1|exact EVAL2|rewrite TYPE1,TYPE2; reflexivity].
  - cbn [compile_flat_value] in COMPILE.
    destruct (compile_flat_value codes reads value1) as [first|] eqn:FIRST; try discriminate.
    destruct (compile_flat_value codes reads value2) as [second|] eqn:SECOND; try discriminate.
    inversion COMPILE; subst code.
    cbn [evaluate_value] in VALUE.
    destruct (evaluate_value parameters loaded value1) as [v1|] eqn:V1; try discriminate.
    destruct v1; try discriminate.
    destruct (evaluate_value parameters loaded value2) as [v2|] eqn:V2; try discriminate.
    destruct v2; try discriminate; inversion VALUE; subst result.
    destruct (IHvalue1 _ _ _ _ _ _ _ _ _ _ OPERANDS READS FIRST V1) as [TYPE1 EVAL1].
    destruct (IHvalue2 _ _ _ _ _ _ _ _ _ _ OPERANDS READS SECOND V2) as [TYPE2 EVAL2].
    split; [reflexivity|].
    eapply eval_Ebinop; [exact EVAL1|exact EVAL2|rewrite TYPE1,TYPE2; reflexivity].
Qed.
Lemma flat_integer_result_correct expression parameters loaded value :
  flat_integer_result expression = true -> evaluate_value parameters loaded expression = Some value ->
  exists integer, value = Vint integer.
Proof.
  destruct expression; cbn [flat_integer_result evaluate_value]; intros INTEGER VALUE; try discriminate.
  - inversion VALUE; eauto.
  - destruct (nth_error parameters n); try discriminate; inversion VALUE; eauto.
  - destruct (evaluate_value parameters loaded expression1) as [first|]; try discriminate;
    destruct first; try discriminate; destruct (evaluate_value parameters loaded expression2) as [second|];
    try discriminate; destruct second; try discriminate; inversion VALUE; eauto.
  - destruct (evaluate_value parameters loaded expression1) as [first|]; try discriminate;
    destruct first; try discriminate; destruct (evaluate_value parameters loaded expression2) as [second|];
    try discriminate; destruct second; try discriminate; inversion VALUE; eauto.
  - destruct (evaluate_value parameters loaded expression1) as [first|]; try discriminate;
    destruct first; try discriminate; destruct (evaluate_value parameters loaded expression2) as [second|];
    try discriminate; destruct second; try discriminate; inversion VALUE; eauto.
Qed.

Lemma compile_flat_array_reads_evaluation base array logical_array block ge locals temps memory accesses codes parameters indices locations loaded :
  rectangle_layout_valid base -> rect_array_binding base ge locals array block ->
  Forall2 (MemoryBody.operand_view ge locals temps memory) codes parameters ->
  compile_flat_array_reads logical_array accesses codes = Some indices ->
  resolve_cells (map (fun access => exact_cell access parameters) accesses)
    (flat_array_locations logical_array block (rectangle_extent base)) = Some locations ->
  load_locations locations memory = Some loaded ->
  Forall2 (flat_value_view ge locals temps memory)
    (map (indexed_array_lvalue base array) indices) loaded.
Proof.
  intros VALID ARRAY OPERANDS; revert indices locations loaded; induction accesses;
    intros indices locations loaded COMPILE RESOLVE LOAD.
  - cbn in COMPILE,RESOLVE; inversion COMPILE; inversion RESOLVE; subst.
    cbn in LOAD; inversion LOAD; constructor.
  - cbn [compile_flat_array_reads] in COMPILE.
    destruct (compile_flat_array_access logical_array a codes) as [index|] eqn:INDEX; try discriminate.
    destruct (compile_flat_array_reads logical_array accesses codes) as [rest|] eqn:REST; try discriminate.
    inversion COMPILE; subst indices.
    cbn [map resolve_cells] in RESOLVE.
    destruct (flat_array_locations logical_array block (rectangle_extent base) (exact_cell a parameters))
      as [location|] eqn:LOCATION; try discriminate.
    destruct (resolve_cells (map (fun access => exact_cell access parameters) accesses)
      (flat_array_locations logical_array block (rectangle_extent base))) as [tail|] eqn:TAIL; try discriminate.
    inversion RESOLVE; subst locations.
    cbn [load_locations] in LOAD.
    destruct (location_load location memory) as [value|] eqn:VALUE; try discriminate.
    destruct (load_locations tail memory) as [values|] eqn:VALUES; try discriminate.
    inversion LOAD; subst loaded; cbn [map]; constructor.
    + destruct (@compile_flat_array_access_evaluation base logical_array block ge locals temps memory
        a codes parameters index location OPERANDS INDEX LOCATION) as [offset [BOUND [SAME [TYPE EVAL]]]].
      subst location; split; [reflexivity|].
      eapply indexed_array_load_evaluation; [exact VALID|exact TYPE|exact ARRAY|exact EVAL|exact BOUND|exact VALUE].
    + eapply IHaccesses; eauto.
Qed.

Section BACKEND.
Variable base : rectangle_shape.
Hypothesis VALID : rectangle_layout_valid base.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable array logical_array : ident.
Variable block : Values.block.
Hypothesis ARRAY : rect_array_binding base ge locals array block.
Definition flat_array_instruction_backend : MemoryBody.instruction_backend fe ge locals
  (array_memory_view base logical_array block).
Proof.
  refine {| MemoryBody.lower_instruction := lower_flat_array_instruction base array logical_array |}.
  intros instruction codes parameters code temps memory source target writes reads COMPILE OPERANDS RUN VIEW.
  unfold lower_flat_array_instruction in COMPILE.
  destruct (flat_integer_result (instruction_value instruction)) eqn:INTEGER; try discriminate.
  destruct (compile_flat_array_access logical_array (instruction_write instruction) codes) as [write_index|]
    eqn:WRITE_CODE; try discriminate.
  destruct (compile_flat_array_reads logical_array (instruction_reads instruction) codes) as [read_indices|]
    eqn:READ_CODES; try discriminate.
  destruct (compile_flat_value codes (map (indexed_array_lvalue base array) read_indices)
    (instruction_value instruction)) as [value_code|] eqn:VALUE_CODE; try discriminate.
  inversion COMPILE; subst code.
  unfold array_memory_view in VIEW; subst source.
  destruct RUN as [WRITES [READS [write [read_locations [WRITE [READ [LOCATIONS ACTION]]]]]]].
  subst writes reads.
  destruct target as [locations final]; cbn in LOCATIONS,ACTION; subst locations.
  destruct ACTION as [loaded [value [LOAD [COMPUTE STORE]]]].
  cbn [memory_reads memory_write memory_compute] in LOAD,COMPUTE,STORE.
  destruct (@compile_flat_array_access_evaluation base logical_array block ge locals temps memory
    (instruction_write instruction) codes parameters write_index write OPERANDS WRITE_CODE WRITE)
    as [index [BOUND [LOCATION [INDEX_TYPE INDEX_EVAL]]]].
  subst write.
  pose proof (@compile_flat_array_reads_evaluation base array logical_array block ge locals temps memory
    (instruction_reads instruction) codes parameters read_indices read_locations loaded
    VALID ARRAY OPERANDS READ_CODES READ LOAD) as READ_EVALUATIONS.
  destruct (@compile_flat_value_evaluation (instruction_value instruction) codes
    (map (indexed_array_lvalue base array) read_indices) value_code parameters loaded value ge locals temps memory
    OPERANDS READ_EVALUATIONS VALUE_CODE COMPUTE) as [VALUE_TYPE VALUE_EVAL].
  destruct (@flat_integer_result_correct (instruction_value instruction) parameters loaded value INTEGER COMPUTE)
    as [integer ->].
  exists final; split; [reflexivity|].
  eapply exec_Sassign with (loc := block) (ofs := Ptrofs.repr (4*index)) (bf := Full)
    (v := Vint integer) (v2 := Vint integer).
  - eapply indexed_array_lvalue_evaluation; [exact VALID|exact INDEX_TYPE|exact ARRAY|exact INDEX_EVAL|exact BOUND].
  - exact VALUE_EVAL.
  - rewrite VALUE_TYPE; reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite Ptrofs.unsigned_repr by (apply (@rect_small_offset_bound base VALID); lia).
    destruct (zle (4*index+size_chunk Mint32) Ptrofs.modulus); [exact STORE|].
    exfalso; pose proof (@rect_small_offset_bound base VALID (4*index+4) ltac:(lia)) as END.
    unfold Ptrofs.max_unsigned in END; change (size_chunk Mint32) with 4 in *; lia.
Defined.
Definition compile_memory_flat_array_loop layout bounds live pool loop :=
  MemoryNested.checked_compile_nested_raw (lower_flat_array_instruction base array logical_array)
    layout bounds live pool loop.
Theorem compile_memory_flat_array_loop_within_correct layout bounds live pool loop code parameters temps source target memory :
  compile_memory_flat_array_loop layout bounds live pool loop = Some code ->
  MemoryNested.A.typed_view layout parameters temps -> MemoryNested.A.env_within bounds parameters ->
  GuardMemoryIRs.Loop.loop_semantics loop parameters source target ->
  array_memory_view base logical_array block source memory ->
  exists target_temps target_memory, array_memory_view base logical_array block target target_memory /\
    temp_agree (layout++live) temps target_temps /\
    exec_stmt fe ge locals temps memory code E0 target_temps target_memory Out_normal.
Proof.
  unfold compile_memory_flat_array_loop,MemoryNested.checked_compile_nested_raw.
  intros COMPILE VIEW WITHIN RUN MEMORY.
  destruct (MemoryNested.scratch_check pool (layout++live)) eqn:FRESH; try discriminate.
  eapply MemoryNested.compile_nested_correct with (backend := flat_array_instruction_backend); eauto.
  apply MemoryNested.scratch_check_sound; exact FRESH.
Qed.
End BACKEND.
Print Assumptions compile_flat_value_evaluation.
Print Assumptions flat_array_instruction_backend.
Print Assumptions compile_memory_flat_array_loop_within_correct.
