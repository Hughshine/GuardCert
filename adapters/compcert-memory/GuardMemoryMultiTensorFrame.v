From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightTempFrame ClightFiniteRegion ClightStraightLine.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryRectangles
  GuardMemoryNaryCompute GuardMemoryNaryLoops GuardMemoryNarySequence
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend
  GuardMemoryMultiTensorSource GuardMemoryMultiTensorSequence.
Import ListNotations.
Set Implicit Arguments.

(** Changing the registry outside the cells used by an instruction cannot change
    its concrete memory action. No injectivity or separation premise is needed. *)
Lemma memory_resolve_cells_frame first second cells :
  Forall (fun cell => first cell = second cell) cells ->
  resolve_cells cells first = resolve_cells cells second.
Proof.
  intro AGREE; induction AGREE; cbn [resolve_cells]; [reflexivity|].
  rewrite H,IHAGREE; reflexivity.
Qed.

Definition memory_instruction_locations_agree (first second : cell_locations) instruction parameters :=
  first (exact_cell (instruction_write instruction) parameters) =
    second (exact_cell (instruction_write instruction) parameters) /\
  Forall (fun access => first (exact_cell access parameters) = second (exact_cell access parameters))
    (instruction_reads instruction).

Theorem memory_instruction_locations_frame first second instruction parameters writes reads before after :
  memory_instruction_locations_agree first second instruction parameters ->
  (GuardMemoryInstr.instr_semantics instruction parameters writes reads
    (RuntimeState first before) (RuntimeState first after) <->
   GuardMemoryInstr.instr_semantics instruction parameters writes reads
    (RuntimeState second before) (RuntimeState second after)).
Proof.
  intros [WRITE READS]; unfold GuardMemoryInstr.instr_semantics,footprint_run; cbn.
  assert (RESOLVE : resolve_cells (map (fun access => exact_cell access parameters)
    (instruction_reads instruction)) first = resolve_cells
    (map (fun access => exact_cell access parameters) (instruction_reads instruction)) second).
  { apply memory_resolve_cells_frame,Forall_map; exact READS. }
  split; intros [WRITES [READ_CELLS [write [loaded [LOCATION [LOADS [FRAME ACTION]]]]]]];
    split; [exact WRITES| |exact WRITES|]; split; [exact READ_CELLS| |exact READ_CELLS|];
    subst reads; exists write,loaded; split.
  - rewrite <- WRITE; exact LOCATION.
  - split; [rewrite <- RESOLVE; exact LOADS|split; [reflexivity|exact ACTION]].
  - rewrite WRITE; exact LOCATION.
  - split; [rewrite RESOLVE; exact LOADS|split; [reflexivity|exact ACTION]].
Qed.

Theorem memory_sequence_locations_frame first second instructions parameters before after :
  Forall (fun instruction => memory_instruction_locations_agree first second instruction parameters) instructions ->
  memory_nary_sequence_point instructions parameters (RuntimeState first before) (RuntimeState first after) ->
  memory_nary_sequence_point instructions parameters (RuntimeState second before) (RuntimeState second after).
Proof.
  intro COVER; revert before after; induction COVER as [|instruction instructions HEAD COVER IH];
    intros before after RUN; inversion RUN; subst.
  - constructor.
  - match goal with
    POINT : memory_nary_point _ _ (RuntimeState first before) ?middle |- _ =>
      destruct middle as [locations middle];
      assert (FRAME : locations = first) by (exact (@memory_nary_point_locations _ _ _ _ POINT));
      subst locations
    end.
    match goal with POINT : memory_nary_point _ _ _ (RuntimeState first ?middle) |- _ =>
      eapply Iter.IProgress with (st2 := RuntimeState second middle);
      [ apply (proj1 (@memory_instruction_locations_frame first second instruction parameters
          (memory_write_cells instruction parameters) (memory_read_cells instruction parameters)
          before middle HEAD)); exact POINT
      | apply IH; assumption ]
    end.
Qed.

Lemma multi_tensor_locations_pointer_frame pointers initial current sizes cell :
  temp_agree pointers initial current -> In (arr_id cell) pointers ->
  multi_tensor_locations initial sizes cell = multi_tensor_locations current sizes cell.
Proof.
  intros FRAME MEMBER; unfold multi_tensor_locations; rewrite FRAME by exact MEMBER; reflexivity.
Qed.

(** This is data checked once by the domain frontend. It covers only actual
    write/read arrays, not every pointer binding in the temporary environment. *)
Definition multi_tensor_instruction_pointers pointers instruction :=
  Forall (fun access => In (fst access) pointers)
    (instruction_write instruction :: instruction_reads instruction).
Definition multi_tensor_pointer_check pointers instructions :=
  forallb (fun instruction => forallb (fun access => existsb (Pos.eqb (fst access)) pointers)
    (instruction_write instruction :: instruction_reads instruction)) instructions.

Theorem multi_tensor_pointer_check_sound pointers instructions :
  multi_tensor_pointer_check pointers instructions = true ->
  Forall (multi_tensor_instruction_pointers pointers) instructions.
Proof.
  intro CHECK; apply Forall_forall; intros instruction MEMBER.
  unfold multi_tensor_pointer_check in CHECK; apply forallb_forall with (x := instruction) in CHECK; [|exact MEMBER].
  apply Forall_forall; intros access USED; apply forallb_forall with (x := access) in CHECK; [|exact USED].
  apply existsb_exists in CHECK as [pointer [POINTER_MEMBER SAME]]; apply Pos.eqb_eq in SAME; subst pointer; exact POINTER_MEMBER.
Qed.

Lemma multi_tensor_instruction_pointer_frame pointers initial current sizes instruction parameters :
  temp_agree pointers initial current -> multi_tensor_instruction_pointers pointers instruction ->
  memory_instruction_locations_agree (multi_tensor_locations current sizes)
    (multi_tensor_locations initial sizes) instruction parameters.
Proof.
  intros FRAME POINTERS; inversion POINTERS as [|write reads WRITE READS]; subst.
  split.
  - destruct (instruction_write instruction) as [array coordinates] eqn:ACCESS.
    symmetry; apply multi_tensor_locations_pointer_frame with (pointers := pointers); [exact FRAME|exact WRITE].
  - apply Forall_forall; intros access MEMBER; apply Forall_forall with (x := access) in READS; [|exact MEMBER].
    destruct access as [array coordinates]; symmetry.
    apply multi_tensor_locations_pointer_frame with (pointers := pointers); [exact FRAME|exact READS].
Qed.

Theorem multi_tensor_sequence_at_entry pointers initial current sizes instructions parameters before after :
  temp_agree pointers initial current -> Forall (multi_tensor_instruction_pointers pointers) instructions ->
  memory_nary_sequence_point instructions parameters
    (RuntimeState (multi_tensor_locations current sizes) before) (RuntimeState (multi_tensor_locations current sizes) after) ->
  memory_nary_sequence_point instructions parameters
    (RuntimeState (multi_tensor_locations initial sizes) before) (RuntimeState (multi_tensor_locations initial sizes) after).
Proof.
  intros FRAME POINTERS; apply memory_sequence_locations_frame.
  eapply Forall_impl; [|exact POINTERS]; intros instruction USED.
  eapply multi_tensor_instruction_pointer_frame; eassumption.
Qed.

Theorem multi_tensor_body_source_decode_at_entry dimensions layout body
    (items : list (multi_tensor_source_statement dimensions layout)) pointers initial
    fe ge locals valuation sizes temps memory after final :
  flatten_region body = map mt_statement items ->
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes temps ->
  (forall id, In id layout -> temps!id = Some (Vint (Int.repr (valuation id)))) ->
  Forall (fun item => mt_available item (map valuation layout) sizes) items ->
  temp_agree pointers initial temps -> multi_tensor_pointer_check pointers (map mt_instruction items) = true ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
  memory_nary_sequence_point (map mt_instruction items) (map valuation layout)
    (RuntimeState (multi_tensor_locations initial sizes) memory) (RuntimeState (multi_tensor_locations initial sizes) final) /\
  after = temps.
Proof.
  intros BODY LAYOUT DIMENSIONS WORDS AVAILABLE FRAME POINTERS SOURCE.
  destruct (@multi_tensor_body_source_decode dimensions layout body items fe ge locals valuation sizes
    temps memory after final BODY LAYOUT DIMENSIONS WORDS AVAILABLE SOURCE) as [RUN EXIT].
  split; [|exact EXIT].
  eapply multi_tensor_sequence_at_entry; [exact FRAME|apply multi_tensor_pointer_check_sound; exact POINTERS|exact RUN].
Qed.

Print Assumptions memory_resolve_cells_frame.
Print Assumptions memory_instruction_locations_frame.
Print Assumptions memory_sequence_locations_frame.
Print Assumptions multi_tensor_locations_pointer_frame.
Print Assumptions multi_tensor_pointer_check_sound.
Print Assumptions multi_tensor_instruction_pointer_frame.
Print Assumptions multi_tensor_sequence_at_entry.
Print Assumptions multi_tensor_body_source_decode_at_entry.
