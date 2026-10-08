From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightNoWrap ClightFiniteRegion ClightStraightLine.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryNaryLift GuardMemoryNaryRanges
  GuardMemoryScalarLoops GuardMemoryScalarLift GuardMemoryRecursiveSource GuardMemoryRecursiveBody
  GuardMemoryRecursiveFramedExecution GuardMemoryIntervalBox GuardMemoryDynamicTensorLayout
  GuardMemoryDynamicTensorBackend GuardMemoryTensorSource GuardMemoryTensorSourceRegion GuardMemoryMultiTensorBackend
  GuardMemoryMultiTensorSource GuardMemoryMultiTensorSequence GuardMemoryMultiTensorFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition multi_tensor_source_operation_box dimensions layout source
    (operation : multi_tensor_source_operation dimensions layout source) counts scalars sizes :=
  forallb (fun access => tensor_coordinate_box_check (tensor_iteration_box counts scalars) sizes
    (tensor_source_terms (snd access))) (mts_write operation :: mts_reads operation).

Lemma multi_tensor_source_operation_box_sound dimensions layout source
    (operation : multi_tensor_source_operation dimensions layout source) counts scalars sizes coordinates :
  multi_tensor_source_operation_box operation counts scalars sizes = true ->
  memory_nary_domain counts [] coordinates ->
  Forall (fun access => multi_tensor_source_available access (coordinates ++ scalars) sizes)
    (mts_write operation :: mts_reads operation).
Proof.
  intros CHECK DOMAIN; apply Forall_forall; intros access MEMBER.
  unfold multi_tensor_source_operation_box in CHECK; apply forallb_forall with (x := access) in CHECK; [|exact MEMBER].
  eapply tensor_coordinate_box_sound; [exact CHECK|apply tensor_iteration_box_sound; exact DOMAIN].
Qed.

Definition multi_tensor_body_box dimensions layout
    (items : list (multi_tensor_source_statement dimensions layout)) counts scalars sizes :=
  forallb (fun item => multi_tensor_source_operation_box (mt_operation item) counts scalars sizes) items.

Theorem multi_tensor_body_box_sound dimensions layout
    (items : list (multi_tensor_source_statement dimensions layout)) counts scalars sizes coordinates :
  multi_tensor_body_box items counts scalars sizes = true -> memory_nary_domain counts [] coordinates ->
  Forall (fun item => mt_available item (coordinates ++ scalars) sizes) items.
Proof.
  intros CHECK DOMAIN; apply Forall_forall; intros item MEMBER.
  unfold multi_tensor_body_box in CHECK; apply forallb_forall with (x := item) in CHECK; [|exact MEMBER].
  eapply multi_tensor_source_operation_box_sound; eassumption.
Qed.

(** Decode an actual complete, active counted nest, whose leaf is a checked list
    of assignments. Reads use the memory at their own statement, including stores
    earlier at the same point. The mathematical registry is fixed at entry and
    agrees with each point only on the arrays that this source actually uses.

    Box/layout acceptance and scalar/header observations are explicit entry
    premises here. Emitting a source-licensed runtime condition for them is a
    separate frontend obligation; this theorem is not a guarded installation. *)
Theorem multi_tensor_source_region_decode dimensions nest scalars pointers
    (items : list (multi_tensor_source_statement dimensions (memory_nest_iterators nest ++ scalars)))
    fe ge locals counts scalar_values sizes temps memory after final :
  flatten_region (memory_nest_leaf nest) = map mt_statement items ->
  memory_nest_shapes nest -> memory_nest_fresh nest -> NoDup (memory_nest_iterators nest ++ scalars) ->
  (forall identifier, In identifier (memory_nest_iterators nest) ->
    ~ In identifier (pointers ++ tensor_dimension_registers dimensions ++ scalars)) ->
  length counts = length (memory_nest_iterators nest) ->
  Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  memory_nest_bindings (memory_nest_bounds nest) (map Z.of_nat counts) temps -> memory_nest_initial nest temps ->
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes temps ->
  memory_nest_bindings scalars scalar_values temps ->
  multi_tensor_pointer_check pointers (map mt_instruction items) = true ->
  multi_tensor_body_box items counts scalar_values sizes = true ->
  exec_stmt fe ge locals temps memory (memory_nest_source nest) E0 after final Out_normal ->
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length scalar_values) (map mt_instruction items))
    (map Z.of_nat counts ++ scalar_values)
    (RuntimeState (multi_tensor_locations temps sizes) memory) (RuntimeState (multi_tensor_locations temps sizes) final) /\
  after = memory_nest_exit nest counts temps.
Proof.
  intros BODY SHAPES FRESH UNIQUE PROTECTED LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS POINTERS BOX SOURCE.
  set (capability := fun le => tensor_dimension_view dimensions sizes le /\
    memory_nest_bindings scalars scalar_values le /\ temp_agree pointers temps le).
  set (physical := fun coordinates before target => memory_scalar_sequence_point (map mt_instruction items) coordinates scalar_values
    (RuntimeState (multi_tensor_locations temps sizes) before) (RuntimeState (multi_tensor_locations temps sizes) target)).
  assert (FRAME : forall first second, temp_agree (pointers ++ tensor_dimension_registers dimensions ++ scalars) first second ->
    capability first -> capability second).
  { intros first second AGREE [D [S P]]; split.
    - eapply tensor_dimension_view_frame; [|exact D]; eapply temp_agree_weaken; [|exact AGREE].
      intros identifier MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER.
    - split.
      + eapply memory_nest_bindings_frame_from; [|exact AGREE|exact S].
        intros identifier MEMBER; apply in_or_app; right; apply in_or_app; right; exact MEMBER.
      + eapply temp_agree_trans; [exact P|]; eapply temp_agree_weaken; [|exact AGREE].
        intros identifier MEMBER; apply in_or_app; left; exact MEMBER. }
  assert (DECODE : forall coordinates le before next target, memory_nary_domain counts [] coordinates ->
    memory_nest_bindings (memory_nest_iterators nest) coordinates le -> capability le ->
    exec_stmt fe ge locals le before (memory_nest_leaf nest) E0 next target Out_normal ->
    physical coordinates before target /\ next = le).
  { intros coordinates le before next target DOMAIN COORDINATES [D [S P]] RUN.
    assert (ALL : memory_nest_bindings (memory_nest_iterators nest ++ scalars) (coordinates ++ scalar_values) le)
      by (apply memory_nest_bindings_append; assumption).
    destruct (memory_nest_bindings_valuation UNIQUE ALL) as [valuation [VALUES WORDS]].
    assert (COVER : Forall (fun item => mt_available item (map valuation (memory_nest_iterators nest ++ scalars)) sizes) items).
    { rewrite VALUES; eapply multi_tensor_body_box_sound; eassumption. }
    destruct (@multi_tensor_body_source_decode_at_entry dimensions (memory_nest_iterators nest ++ scalars)
      (memory_nest_leaf nest) items pointers temps fe ge locals valuation sizes le before next target
      BODY LAYOUT D WORDS COVER P POINTERS RUN) as [POINT EXIT].
    split; [|exact EXIT]; unfold physical,memory_scalar_sequence_point; rewrite <- VALUES; exact POINT. }
  destruct (@memory_recursive_source_decode_framed fe ge locals nest
    (pointers ++ tensor_dimension_registers dimensions ++ scalars) capability FRAME SHAPES FRESH PROTECTED
    (@multi_tensor_sequence_normal dimensions (memory_nest_iterators nest ++ scalars) items (memory_nest_leaf nest) BODY)
    (@multi_tensor_sequence_quiet dimensions (memory_nest_iterators nest ++ scalars) items (memory_nest_leaf nest) BODY)
    (@multi_tensor_sequence_writes dimensions (memory_nest_iterators nest ++ scalars) items (memory_nest_leaf nest) BODY)
    counts physical [] [] temps memory after final LENGTH COUNTS ltac:(cbn; tauto) DECODE ltac:(constructor)
    BOUNDS INITIAL ltac:(split; [exact DIMENSIONS|split; [exact SCALARS|apply temp_agree_refl]]) SOURCE) as [ITER EXIT].
  split; [|exact EXIT].
  apply (proj1 (@memory_scalar_rectangle_lift (multi_tensor_locations temps sizes) (map mt_instruction items)
    physical counts scalar_values memory final ltac:(intros; reflexivity))); exact ITER.
Qed.

Print Assumptions multi_tensor_source_operation_box_sound.
Print Assumptions multi_tensor_body_box_sound.
Print Assumptions multi_tensor_source_region_decode.
