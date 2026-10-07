From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryNaryLift GuardMemoryNaryRanges
  GuardMemoryScalarLoops GuardMemoryScalarLift GuardMemoryRecursiveSource GuardMemoryRecursiveBody
  GuardMemoryRecursiveFramedExecution GuardMemoryRecursiveFirstLeaf GuardMemoryIntervalBox
  GuardMemorySourceParameters GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryTensorSource.
From GuardMemory Require Import GuardMemoryNaryAffineExpressions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint tensor_coordinate_box_check bounds dimensions terms :=
  match dimensions,terms with
  | [],[] => true
  | dimension::rest,term::tail => interval_box_check bounds dimension term && tensor_coordinate_box_check bounds rest tail
  | _,_ => false end.
Theorem tensor_coordinate_box_sound bounds dimensions terms values :
  tensor_coordinate_box_check bounds dimensions terms=true -> interval_ranges bounds values ->
  exists offset,tensor_index dimensions(affine_product terms values)=Some offset.
Proof.
  revert terms; induction dimensions as [|dimension dimensions IH]; intros [|term terms] CHECK RANGES;
    cbn in CHECK; try discriminate.
  - exists 0; reflexivity.
  - apply andb_true_iff in CHECK as [HEAD TAIL].
    pose proof(@interval_box_sound bounds dimension term values HEAD RANGES)as RANGE.
    destruct(IH terms TAIL RANGES)as [offset INDEX].
    exists(memory_nary_index_value term values*tensor_volume dimensions+offset).
    change(tensor_index(dimension::dimensions)(memory_nary_index_value term values::affine_product terms values)=
      Some(memory_nary_index_value term values*tensor_volume dimensions+offset)).
    cbn [tensor_index]; rewrite INDEX.
    assert(LOW:(0 <=? memory_nary_index_value term values)=true)by(apply Z.leb_le; lia).
    assert(HIGH:(memory_nary_index_value term values <? dimension)=true)by(apply Z.ltb_lt; lia).
    rewrite LOW,HIGH; reflexivity.
Qed.
Definition tensor_iteration_box counts scalars :=
  map(fun count=>(0,Z.of_nat count))counts++map(fun value=>(value,value+1))scalars.
Lemma tensor_iteration_box_sound counts coordinates scalars : memory_nary_domain counts [] coordinates ->
  interval_ranges(tensor_iteration_box counts scalars)(coordinates++scalars).
Proof.
  intro DOMAIN; destruct(@memory_nary_domain_suffix counts [] coordinates DOMAIN)as [suffix [VALUES RANGES]];
    cbn in VALUES; subst coordinates; unfold tensor_iteration_box,interval_ranges; apply Forall2_app.
  - clear DOMAIN; induction RANGES; cbn [map]; constructor; assumption.
  - induction scalars; cbn; constructor; [cbn; lia|exact IHscalars].
Qed.
Definition tensor_source_operation_box dimensions layout pointer logical_array source
    (operation:tensor_source_operation dimensions layout pointer logical_array source)counts scalars sizes :=
  forallb(fun access=>tensor_coordinate_box_check(tensor_iteration_box counts scalars)sizes(tensor_source_terms access))
    (tensor_source_write operation::tensor_source_reads operation).
Lemma tensor_source_operation_box_sound dimensions layout pointer logical_array source
    (operation:tensor_source_operation dimensions layout pointer logical_array source)counts scalars sizes coordinates :
  tensor_source_operation_box operation counts scalars sizes=true -> memory_nary_domain counts [] coordinates ->
  Forall(fun access=>tensor_source_access_available access(coordinates++scalars)sizes)
    (tensor_source_write operation::tensor_source_reads operation).
Proof.
  intros CHECK DOMAIN; apply Forall_forall; intros access MEMBER; unfold tensor_source_operation_box in CHECK.
  apply forallb_forall with(x:=access)in CHECK; [|exact MEMBER].
  eapply tensor_coordinate_box_sound; [exact CHECK|apply tensor_iteration_box_sound; exact DOMAIN].
Qed.

(** This decoder consumes an actual original Clight nest, not an assumed Loop
    execution.  Box acceptance is a semantic entry condition; its machine
    realization and source-definedness domain remain separate certificates. *)
Theorem tensor_source_region_decode dimensions nest scalars pointer logical_array
    (operation:tensor_source_operation dimensions(memory_nest_iterators nest++scalars)pointer logical_array(memory_nest_leaf nest))
    fe ge locals counts scalar_values sizes temps memory after final block base :
  memory_nest_shapes nest -> memory_nest_fresh nest -> NoDup(memory_nest_iterators nest++scalars) ->
  (forall identifier,In identifier(memory_nest_iterators nest) ->
    ~In identifier(pointer::tensor_dimension_registers dimensions++scalars)) ->
  length counts=length(memory_nest_iterators nest) -> Forall(fun count=>count<>O /\ signed_range(Z.of_nat count))counts ->
  memory_nest_bindings(memory_nest_bounds nest)(map Z.of_nat counts)temps -> memory_nest_initial nest temps ->
  tensor_layout_flag sizes=true -> tensor_dimension_view dimensions sizes temps ->
  memory_nest_bindings scalars scalar_values temps -> temps!pointer=Some(Vptr block base) ->
  tensor_source_operation_box operation counts scalar_values sizes=true ->
  exec_stmt fe ge locals temps memory(memory_nest_source nest)E0 after final Out_normal ->
  L.loop_semantics(memory_scalar_rectangle 0(length counts)(length scalar_values)[tensor_source_instruction operation])
    (map Z.of_nat counts++scalar_values)(RuntimeState(tensor_pointer_locations logical_array block base sizes)memory)
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)final) /\ after=memory_nest_exit nest counts temps.
Proof.
  intros SHAPES FRESH UNIQUE PROTECTED LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS POINTER BOX SOURCE.
  set(capability:=fun le=>tensor_dimension_view dimensions sizes le /\ memory_nest_bindings scalars scalar_values le /\
    le!pointer=Some(Vptr block base)).
  set(physical:=fun coordinates before target=>memory_scalar_sequence_point[tensor_source_instruction operation]coordinates scalar_values
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)before)
    (RuntimeState(tensor_pointer_locations logical_array block base sizes)target)).
  assert(FRAME:forall first second,temp_agree(pointer::tensor_dimension_registers dimensions++scalars)first second ->
    capability first -> capability second).
  { intros first second AGREE [D [S P]]; split.
    - eapply tensor_dimension_view_frame; [|exact D]; eapply temp_agree_weaken; [|exact AGREE].
      intros identifier MEMBER; cbn; right; apply in_or_app; left; exact MEMBER.
    - split.
      + eapply memory_nest_bindings_frame_from; [|exact AGREE|exact S].
        intros identifier MEMBER; cbn; right; apply in_or_app; right; exact MEMBER.
      + rewrite AGREE by(cbn; auto); exact P. }
  assert(DECODE:forall coordinates le before next target,memory_nary_domain counts [] coordinates ->
    memory_nest_bindings(memory_nest_iterators nest)coordinates le -> capability le ->
    exec_stmt fe ge locals le before(memory_nest_leaf nest)E0 next target Out_normal -> physical coordinates before target /\ next=le).
  { intros coordinates le before next target DOMAIN COORDINATES [D [S P]] RUN.
    assert(ALL:memory_nest_bindings(memory_nest_iterators nest++scalars)(coordinates++scalar_values)le)
      by(apply memory_nest_bindings_append; assumption).
    destruct(memory_nest_bindings_valuation UNIQUE ALL)as [valuation [VALUES WORDS]].
    assert(COVER:Forall(fun access=>tensor_source_access_available access(map valuation(memory_nest_iterators nest++scalars))sizes)
      (tensor_source_write operation::tensor_source_reads operation)).
    { rewrite VALUES; eapply tensor_source_operation_box_sound; eassumption. }
    destruct(@tensor_source_operation_decode dimensions(memory_nest_iterators nest++scalars)pointer logical_array(memory_nest_leaf nest)
      operation fe ge locals le before next target valuation sizes block base LAYOUT D WORDS P COVER RUN)as [POINT EXIT].
    split; [|exact EXIT]; unfold physical,memory_scalar_sequence_point,memory_nary_sequence_point; rewrite <- VALUES.
    econstructor; [exact POINT|constructor]. }
  destruct(@memory_recursive_source_decode_framed fe ge locals nest(pointer::tensor_dimension_registers dimensions++scalars)
    capability FRAME SHAPES FRESH PROTECTED(tensor_source_operation_normal operation)(tensor_source_operation_quiet operation)
    (tensor_source_operation_writes operation)counts physical [] [] temps memory after final LENGTH COUNTS
    ltac:(cbn; tauto)DECODE ltac:(constructor)BOUNDS INITIAL ltac:(repeat split; assumption)SOURCE)as [ITER EXIT].
  split; [|exact EXIT].
  apply(proj1(@memory_scalar_rectangle_lift(tensor_pointer_locations logical_array block base sizes)[tensor_source_instruction operation]
    physical counts scalar_values memory final ltac:(intros; reflexivity))); exact ITER.
Qed.

(** Syntax metadata specifies which RHS parameter is used.  The first actually
    reached source leaf supplies pointer/layout/scalar words before any guard
    or mathematical tensor assumption is used. *)
Theorem tensor_source_region_first_capability dimensions nest scalars pointer logical_array
    (operation:tensor_source_operation dimensions(memory_nest_iterators nest++scalars)pointer logical_array(memory_nest_leaf nest))
    fe ge locals temps memory after final :
  memory_nest_shapes nest -> memory_nest_fresh nest ->
  (forall identifier,In identifier(memory_nest_iterators nest) ->
    ~In identifier(pointer::tensor_dimension_registers(tl dimensions)++scalars)) ->
  (forall identifier,In identifier scalars -> In identifier(tensor_dimension_registers(tl dimensions)) \/
    exists index,nth_error(memory_nest_iterators nest++scalars)index=Some identifier /\
      In index(memory_source_parameter_positions(tensor_source_value operation))) ->
  Forall(fun bound=>0<Int.signed(temp_word bound temps))(memory_nest_bounds nest) -> memory_nest_initial nest temps ->
  exec_stmt fe ge locals temps memory(memory_nest_source nest)E0 after final Out_normal ->
  (exists block base,temps!pointer=Some(Vptr block base)) /\
  (forall identifier,In identifier(tensor_dimension_registers(tl dimensions)++scalars) -> exists word,temps!identifier=Some(Vint word)).
Proof.
  intros SHAPES FRESH PROTECTED USED POSITIVE INITIAL SOURCE.
  destruct(@memory_recursive_first_leaf fe ge locals nest SHAPES FRESH(tensor_source_operation_normal operation)
    (tensor_source_operation_quiet operation)(tensor_source_operation_writes operation)
    (pointer::tensor_dimension_registers(tl dimensions)++scalars)temps memory after final PROTECTED POSITIVE INITIAL SOURCE)
    as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
  destruct(@tensor_source_operation_has_capability dimensions(memory_nest_iterators nest++scalars)pointer logical_array(memory_nest_leaf nest)
    operation fe ge locals leaf_temps memory leaf_after leaf_final LEAF)as [[block [base POINTER]][DIMENSIONS PARAMETERS]].
  split.
  - exists block,base; rewrite <- (FRAME pointer ltac:(cbn; auto)); exact POINTER.
  - intros identifier MEMBER.
    assert(WORD:exists word,leaf_temps!identifier=Some(Vint word)).
    { apply in_app_or in MEMBER as [D|S]; [apply DIMENSIONS; exact D|].
      destruct(USED identifier S)as [D|[index [LOOKUP USE]]]; [apply DIMENSIONS; exact D|eapply PARAMETERS; eassumption]. }
    destruct WORD as [word WORD]; exists word; rewrite <- (FRAME identifier ltac:(cbn; auto)); exact WORD.
Qed.

Print Assumptions tensor_coordinate_box_sound.
Print Assumptions tensor_iteration_box_sound.
Print Assumptions tensor_source_operation_box_sound.
Print Assumptions tensor_source_region_decode.
Print Assumptions tensor_source_region_first_capability.
