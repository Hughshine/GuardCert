From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import CompCertMemoryActions CompCertStoreSchedule RectangularSchedule
  ClightRectangularStore ClightRectangularRegion.
From Guard Require Import RectangularMemorySchedule RectangularRowSchedule
  ClightRectangularUpdate ClightRectangularRowUpdate.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_write_cells instruction parameters := [exact_cell (instruction_write instruction) parameters].
Definition memory_read_cells instruction parameters := map (fun access => exact_cell access parameters) (instruction_reads instruction).
Lemma resolved_instruction_execution instruction parameters locations write reads before after :
  locations (exact_cell (instruction_write instruction) parameters) = Some write ->
  resolve_cells (memory_read_cells instruction parameters) locations = Some reads ->
  (GuardMemoryInstr.instr_semantics instruction parameters (memory_write_cells instruction parameters)
    (memory_read_cells instruction parameters) (RuntimeState locations before) (RuntimeState locations after) <->
   memory_action_run (MemoryAction reads write (fun values => evaluate_value parameters values (instruction_value instruction))) before after).
Proof.
  intros WRITE READ; split.
  - intros [_ [_ [actual_write [actual_reads [ACTUAL_WRITE [ACTUAL_READ [_ RUN]]]]]]].
    cbn [runtime_locations runtime_memory] in ACTUAL_WRITE, ACTUAL_READ, RUN.
    rewrite WRITE in ACTUAL_WRITE; inversion ACTUAL_WRITE; subst actual_write.
    rewrite READ in ACTUAL_READ; inversion ACTUAL_READ; subst actual_reads; exact RUN.
  - intro RUN; split; [reflexivity|]; split; [reflexivity|].
    exists write,reads; repeat split; assumption || reflexivity.
Qed.
Definition point_cell array index := {| arr_id := array; arr_index := [index] |}.
Lemma flat_array_location_at array block extent index : 0 <= index < extent ->
  flat_array_locations array block extent (point_cell array index) = Some (MemoryLocation Mint32 block (4 * index)).
Proof.
  intro BOUND; unfold flat_array_locations, point_cell; cbn [arr_id arr_index]; rewrite Pos.eqb_refl.
  assert (ACCEPT : (0 <=? index) && (index <? extent) = true) by
    (apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  rewrite ACCEPT; reflexivity.
Qed.
Definition rect_write_access d array : AccessFunction := (array,[([rectangle_stride d;1],0)]).
Lemma rect_write_cell d array i j : exact_cell (rect_write_access d array) [i;j] =
  point_cell array (i * rectangle_stride d + j).
Proof.
  change (point_cell array (rectangle_stride d * i + (1*j + 0) + 0) = point_cell array (i * rectangle_stride d + j)).
  f_equal; ring.
Qed.
Definition rect_payload_expression d := AddValue
  (AddValue (MulValue (ParameterValue 0) (ConstantValue (rectangle_coefficient d))) (ParameterValue 1))
  (ConstantValue (rectangle_bias d)).
Lemma rect_payload_expression_value d i j loaded :
  evaluate_value [i;j] loaded (rect_payload_expression d) = Some (rect_payload d i j).
Proof.
  change (Some (Vint (Int.add (Int.add (Int.mul (Int.repr i) (Int.repr (rectangle_coefficient d)))
    (Int.repr j)) (Int.repr (rectangle_bias d)))) = Some (rect_payload d i j)).
  rewrite rect_integer_multiply, !rect_integer_add; reflexivity.
Qed.
Definition rect_memory_write d array := MemoryInstruction (rect_write_access d array) [] (rect_payload_expression d).
Lemma rect_memory_write_execution d array block i j before after :
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  (GuardMemoryInstr.instr_semantics (rect_memory_write d array) [i;j]
    (memory_write_cells (rect_memory_write d array) [i;j]) []
    (RuntimeState (flat_array_locations array block (rectangle_extent d)) before)
    (RuntimeState (flat_array_locations array block (rectangle_extent d)) after) <->
   store_action_run (rectangle_action block (rectangle_stride d) (rect_payload d) (i,j)) before after).
Proof.
  intro BOUND.
  rewrite (@resolved_instruction_execution (rect_memory_write d array) [i;j]
    (flat_array_locations array block (rectangle_extent d))
    (MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j))) [] before after).
  - split.
    + intros [inputs [value [LOAD [COMPUTE STORE]]]].
      cbn [load_locations memory_reads] in LOAD; inversion LOAD; subst inputs.
      change (evaluate_value [i;j] [] (rect_payload_expression d) = Some value) in COMPUTE.
      rewrite rect_payload_expression_value in COMPUTE; inversion COMPUTE; subst value; exact STORE.
    + intro STORE; exists [],(rect_payload d i j); split; [reflexivity|]; split;
        [apply rect_payload_expression_value|exact STORE].
  - change (flat_array_locations array block (rectangle_extent d) (exact_cell (rect_write_access d array) [i;j]) =
      Some (MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j)))).
    rewrite rect_write_cell; apply flat_array_location_at; exact BOUND.
  - reflexivity.
Qed.

Lemma rect_memory_write_clight_decode d (VALID : rectangle_layout_valid d) fe ge locals le before
  array row column i j after_temps after :
  le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) ->
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  exec_stmt fe ge locals le before (rect_store d array row column) E0 after_temps after Out_normal ->
  exists block, rect_array_binding d ge locals array block /\ after_temps = le /\
    GuardMemoryInstr.NonAlias (RuntimeState (flat_array_locations array block (rectangle_extent d)) before) /\
    GuardMemoryInstr.instr_semantics (rect_memory_write d array) [i;j]
      (memory_write_cells (rect_memory_write d array) [i;j]) []
      (RuntimeState (flat_array_locations array block (rectangle_extent d)) before)
      (RuntimeState (flat_array_locations array block (rectangle_extent d)) after).
Proof.
  intros ROW COLUMN BOUND EXEC.
  destruct (@rect_store_inverse d VALID fe ge locals le before array row column i j E0 after_temps after Out_normal
    ROW COLUMN BOUND EXEC) as [block [BIND [_ [TEMPS [_ STORE]]]]].
  exists block; split; [exact BIND|]; split; [exact TEMPS|]; split.
  - apply flat_array_locations_nonalias.
  - apply rect_memory_write_execution; [exact BOUND|exact STORE].
Qed.
Print Assumptions rect_memory_write_execution.
Print Assumptions rect_memory_write_clight_decode.

Definition rect_read_payload_expression d := AddValue (LoadedValue 0) (rect_payload_expression d).
Lemma rect_read_payload_expression_value d i j old :
  evaluate_value [i;j] [old] (rect_read_payload_expression d) = rect_update_compute d i j [old].
Proof.
  unfold rect_read_payload_expression; cbn [evaluate_value].
  rewrite rect_payload_expression_value; destruct old; reflexivity.
Qed.
Definition rect_memory_update d array :=
  MemoryInstruction (rect_write_access d array) [rect_write_access d array] (rect_read_payload_expression d).
Definition rect_row_access d array : AccessFunction := (array,[([rectangle_stride d;0],0)]).
Lemma rect_row_cell d array i j : exact_cell (rect_row_access d array) [i;j] =
  point_cell array (i * rectangle_stride d).
Proof.
  change (point_cell array (rectangle_stride d * i + (0*j + 0) + 0) = point_cell array (i * rectangle_stride d)).
  f_equal; ring.
Qed.
Definition rect_memory_row_update d array :=
  MemoryInstruction (rect_write_access d array) [rect_row_access d array] (rect_read_payload_expression d).

Lemma singleton_load_inputs location memory inputs :
  load_locations [location] memory = Some inputs -> exists old, inputs = [old].
Proof.
  cbn [load_locations]; destruct (location_load location memory); try discriminate.
  intro EQ; inversion EQ; eauto.
Qed.

Lemma rect_memory_update_execution d array block i j before after :
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  (GuardMemoryInstr.instr_semantics (rect_memory_update d array) [i;j]
    (memory_write_cells (rect_memory_update d array) [i;j])
    (memory_read_cells (rect_memory_update d array) [i;j])
    (RuntimeState (flat_array_locations array block (rectangle_extent d)) before)
    (RuntimeState (flat_array_locations array block (rectangle_extent d)) after) <->
   memory_action_run (rect_update_action d block i j) before after).
Proof.
  intro BOUND.
  rewrite (@resolved_instruction_execution (rect_memory_update d array) [i;j]
    (flat_array_locations array block (rectangle_extent d))
    (MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j)))
    [MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j))] before after).
  - unfold rect_update_action, rectangle_memory_action, rectangle_location.
    cbn [fst snd memory_reads memory_write memory_compute].
    change (memory_action_run (MemoryAction
      [MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j))]
      (MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j)))
      (fun inputs => evaluate_value [i;j] inputs (rect_read_payload_expression d))) before after <->
      memory_action_run (MemoryAction [MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j))]
      (MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j)))
      (rect_update_compute d i j)) before after).
    split; intros [inputs [value [LOAD [COMPUTE STORE]]]].
    + destruct (@singleton_load_inputs _ _ _ LOAD) as [old EQ]; subst inputs.
      exists [old],value; split; [exact LOAD|]; split; [|exact STORE].
      cbn [memory_compute] in COMPUTE; rewrite rect_read_payload_expression_value in COMPUTE; exact COMPUTE.
    + destruct (@singleton_load_inputs _ _ _ LOAD) as [old EQ]; subst inputs.
      exists [old],value; split; [exact LOAD|]; split; [|exact STORE].
      cbn [memory_compute]; rewrite rect_read_payload_expression_value; exact COMPUTE.
  - change (flat_array_locations array block (rectangle_extent d) (exact_cell (rect_write_access d array) [i;j]) = Some (MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j)))).
    rewrite rect_write_cell; apply flat_array_location_at; exact BOUND.
  - unfold memory_read_cells, rect_memory_update; cbn [instruction_reads map resolve_cells].
    rewrite rect_write_cell, flat_array_location_at by exact BOUND; reflexivity.
Qed.

Lemma rect_memory_row_update_execution d array block i j before after :
  0 <= i * rectangle_stride d + j < rectangle_extent d ->
  0 <= i * rectangle_stride d < rectangle_extent d ->
  (GuardMemoryInstr.instr_semantics (rect_memory_row_update d array) [i;j]
    (memory_write_cells (rect_memory_row_update d array) [i;j])
    (memory_read_cells (rect_memory_row_update d array) [i;j])
    (RuntimeState (flat_array_locations array block (rectangle_extent d)) before)
    (RuntimeState (flat_array_locations array block (rectangle_extent d)) after) <->
   memory_action_run (rect_row_update_action d block i j) before after).
Proof.
  intros WRITE_BOUND READ_BOUND.
  rewrite (@resolved_instruction_execution (rect_memory_row_update d array) [i;j]
    (flat_array_locations array block (rectangle_extent d))
    (MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j)))
    [MemoryLocation Mint32 block (4 * (i * rectangle_stride d))] before after).
  - unfold rect_row_update_action, rectangle_row_action, rectangle_location.
    cbn [fst snd memory_reads memory_write memory_compute]; rewrite Z.add_0_r.
    change (memory_action_run (MemoryAction [MemoryLocation Mint32 block (4 * (i * rectangle_stride d))]
      (MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j)))
      (fun inputs => evaluate_value [i;j] inputs (rect_read_payload_expression d))) before after <->
      memory_action_run (MemoryAction [MemoryLocation Mint32 block (4 * (i * rectangle_stride d))]
      (MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j)))
      (rect_update_compute d i j)) before after).
    split; intros [inputs [value [LOAD [COMPUTE STORE]]]].
    + destruct (@singleton_load_inputs _ _ _ LOAD) as [old EQ]; subst inputs.
      exists [old],value; split; [exact LOAD|]; split; [|exact STORE].
      cbn [memory_compute] in COMPUTE; rewrite rect_read_payload_expression_value in COMPUTE; exact COMPUTE.
    + destruct (@singleton_load_inputs _ _ _ LOAD) as [old EQ]; subst inputs.
      exists [old],value; split; [exact LOAD|]; split; [|exact STORE].
      cbn [memory_compute]; rewrite rect_read_payload_expression_value; exact COMPUTE.
  - change (flat_array_locations array block (rectangle_extent d) (exact_cell (rect_write_access d array) [i;j]) = Some (MemoryLocation Mint32 block (4 * (i * rectangle_stride d + j)))).
    rewrite rect_write_cell; apply flat_array_location_at; exact WRITE_BOUND.
  - unfold memory_read_cells, rect_memory_row_update; cbn [instruction_reads map resolve_cells].
    rewrite rect_row_cell, flat_array_location_at by exact READ_BOUND; reflexivity.
Qed.
Print Assumptions rect_memory_update_execution.
Print Assumptions rect_memory_row_update_execution.
