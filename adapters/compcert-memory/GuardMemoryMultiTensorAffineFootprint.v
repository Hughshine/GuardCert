From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryLoopTrace GuardMemoryRegistryGuard GuardMemoryFootprintRestriction GuardMemoryFiniteFootprint
  GuardMemoryRuntimeReceipts GuardMemoryFiniteAliasCondition GuardMemoryRectangularFootprint
  GuardMemoryScalarLoops GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend
  GuardMemoryMultiTensorBackend GuardMemoryMultiTensorAddressReceipts
  GuardMemoryBooleanPairRectangle GuardMemoryMultiTensorPairSeparation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition multi_tensor_instruction_accesses instruction :=
  instruction_write instruction :: instruction_reads instruction.
Definition multi_tensor_instruction_templates instructions :=
  flat_map multi_tensor_instruction_accesses instructions.
Definition multi_tensor_affine_source_footprint counts values instructions :=
  memory_events_footprint (memory_loop_trace
    (memory_scalar_rectangle 0 (length counts) (length values) instructions) (counts ++ values)).

Lemma multi_tensor_point_template_footprint instructions values :
  memory_point_footprint instructions values =
  map (fun access => exact_cell access values) (multi_tensor_instruction_templates instructions).
Proof.
  unfold memory_point_footprint,multi_tensor_instruction_templates; rewrite memory_map_flat_map.
  apply flat_map_ext; intro instruction; reflexivity.
Qed.
Lemma multi_tensor_affine_source_footprint_exact counts values instructions :
  multi_tensor_affine_source_footprint counts values instructions =
  flat_map (fun point => map (fun access => exact_cell access (point++values))
    (multi_tensor_instruction_templates instructions)) (memory_rectangular_points counts []).
Proof.
  unfold multi_tensor_affine_source_footprint.
  pose proof (@memory_scalar_rectangle_footprint counts instructions values [] [] eq_refl) as EXACT.
  cbn [rev app length] in EXACT; rewrite EXACT.
  apply flat_map_ext; intro point; apply multi_tensor_point_template_footprint.
Qed.
Theorem multi_tensor_affine_source_footprint_member counts values instructions cell :
  In cell (multi_tensor_affine_source_footprint counts values instructions) <->
  exists point access,
    Forall2 (fun coordinate count => 0 <= coordinate < count) point counts /\
    In access (multi_tensor_instruction_templates instructions) /\ cell = exact_cell access (point++values).
Proof.
  rewrite multi_tensor_affine_source_footprint_exact; split.
  - intro MEMBER; apply in_flat_map in MEMBER as [point [POINT MEMBER]].
    apply memory_rectangular_points_origin in POINT.
    apply in_map_iff in MEMBER as [access [SAME MEMBER]]; exists point,access; auto.
  - intros [point [access [POINT [MEMBER SAME]]]]; subst cell.
    apply in_flat_map; exists point; split; [apply memory_rectangular_points_origin; exact POINT|].
    apply in_map_iff; exists access; auto.
Qed.

(** Permission receipts follow the actual source trace, including reads made
    defined by earlier stores. This theorem moves permissions, not values. *)
Theorem multi_tensor_affine_source_point_receipts counts values instructions locations memory final :
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) instructions)
    (counts++values) (RuntimeState locations memory) (RuntimeState locations final) ->
  forall point access,
    Forall2 (fun coordinate count => 0 <= coordinate < count) point counts ->
    In access (multi_tensor_instruction_templates instructions) ->
    memory_cell_access locations memory (exact_cell access (point++values)) Readable.
Proof.
  intros SOURCE point access POINT MEMBER.
  pose proof (@memory_loop_entry_footprint_readable _ _ _ _ SOURCE) as RECEIPTS.
  change (Forall (fun cell => memory_cell_access locations memory cell Readable)
    (multi_tensor_affine_source_footprint counts values instructions)) in RECEIPTS.
  rewrite Forall_forall in RECEIPTS; apply RECEIPTS.
  apply multi_tensor_affine_source_footprint_member; exists point,access; auto.
Qed.

Definition multi_tensor_affine_access_check locations (first second : AccessFunction) a b :=
  if Pos.eqb (fst first) (fst second) then true
  else memory_cell_pair_address_check locations (exact_cell first a) (exact_cell second b).
Definition multi_tensor_affine_point_check locations accesses values first second :=
  forallb (fun left => forallb (fun right =>
    multi_tensor_affine_access_check locations left right (first++values) (second++values)) accesses) accesses.
Definition multi_tensor_affine_scan_check locations accesses values counts :=
  memory_boolean_pair_rectangle_result (multi_tensor_affine_point_check locations accesses values) counts.

Lemma multi_tensor_affine_scan_check_member locations accesses values counts :
  Forall (fun count => 0 <= count) counts ->
  multi_tensor_affine_scan_check locations accesses values counts = true <->
  forall a b first second,
    Forall2 (fun coordinate count => 0 <= coordinate < count) a counts ->
    Forall2 (fun coordinate count => 0 <= coordinate < count) b counts ->
    In first accesses -> In second accesses ->
    multi_tensor_affine_access_check locations first second (a++values) (b++values) = true.
Proof.
  intro COUNTS; unfold multi_tensor_affine_scan_check; rewrite memory_boolean_pair_rectangle_member by exact COUNTS.
  split.
  - intros ALL a b first second A B FIRST SECOND.
    specialize (ALL a b A B); unfold multi_tensor_affine_point_check in ALL.
    apply forallb_forall with (x:=first) in ALL; [|exact FIRST].
    apply forallb_forall with (x:=second) in ALL; assumption.
  - intros ALL a b A B; unfold multi_tensor_affine_point_check.
    apply forallb_forall; intros first FIRST; apply forallb_forall; intros second SECOND.
    apply ALL; assumption.
Qed.

Theorem multi_tensor_affine_scan_footprint_separation dimensions sizes original memory final counts values instructions
    (ge : genv) (locals : env) :
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes original ->
  Forall (fun count => 0 <= count) counts ->
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) instructions)
    (counts++values) (RuntimeState (multi_tensor_locations original sizes) memory)
    (RuntimeState (multi_tensor_locations original sizes) final) ->
  multi_tensor_affine_scan_check (multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates instructions) values counts = true ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed
    (multi_tensor_affine_source_footprint counts values instructions)) (multi_tensor_locations original sizes)).
Proof.
  intros LAYOUT DIMENSIONS COUNTS SOURCE CHECK.
  assert (SPAN : 4 * tensor_volume sizes <= Ptrofs.modulus).
  { pose proof (@tensor_layout_flag_sound sizes LAYOUT); tauto. }
  pose proof ((proj1 (@multi_tensor_affine_scan_check_member (multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates instructions) values counts COUNTS)) CHECK) as ALL.
  apply memory_restricted_locations_nonalias.
  intros cell1 cell2 loc1 loc2 ALLOWED1 ALLOWED2 RESOLVE1 RESOLVE2 DIFFERENT.
  apply memory_footprint_allowed_exact in ALLOWED1,ALLOWED2.
  apply multi_tensor_affine_source_footprint_member in ALLOWED1 as [a [first [A [FIRST SAME1]]]].
  apply multi_tensor_affine_source_footprint_member in ALLOWED2 as [b [second [B [SECOND SAME2]]]].
  subst cell1 cell2.
  specialize (ALL a b first second A B FIRST SECOND).
  unfold multi_tensor_affine_access_check in ALL.
  destruct (Pos.eqb (fst first) (fst second)) eqn:IDS.
  - apply Pos.eqb_eq in IDS; eapply multi_tensor_same_array_separation;
      [exact SPAN| |exact RESOLVE1|exact RESOLVE2|exact DIFFERENT].
    destruct first,second; exact IDS.
  - eapply memory_cell_pair_address_separated with
      (code := multi_tensor_cell_address dimensions) (s := Entry ge locals original memory);
      [| |exact RESOLVE1|exact RESOLVE2|exact DIFFERENT|exact ALL].
    + eapply multi_tensor_cell_address_receipt; [exact LAYOUT|exact DIMENSIONS|].
      eapply multi_tensor_affine_source_point_receipts; [exact SOURCE|exact A|exact FIRST].
    + eapply multi_tensor_cell_address_receipt; [exact LAYOUT|exact DIMENSIONS|].
      eapply multi_tensor_affine_source_point_receipts; [exact SOURCE|exact B|exact SECOND].
Qed.

Print Assumptions multi_tensor_point_template_footprint.
Print Assumptions multi_tensor_affine_source_footprint_exact.
Print Assumptions multi_tensor_affine_source_footprint_member.
Print Assumptions multi_tensor_affine_source_point_receipts.
Print Assumptions multi_tensor_affine_scan_check_member.
Print Assumptions multi_tensor_affine_scan_footprint_separation.
