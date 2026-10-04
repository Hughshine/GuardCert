From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryFiniteFootprint GuardMemoryScalarLoops GuardMemoryNaryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardMemory Require Import GuardMemoryRectangularFootprint GuardMemoryBooleanRectangle GuardMemoryBooleanScan.
From GuardMemory Require Import GuardMemoryScalarContextTail GuardMemoryStartedScalarLoop GuardMemoryStartedBooleanRectangle.
Lemma memory_scalar_sequence_footprint_tail instructions prefix counts values tail :
  length prefix = length counts ->
  memory_events_footprint (memory_loop_list_trace
    (memory_scalar_instruction_sequence (length prefix) (length values) instructions)
    (rev prefix++counts++(values++tail))) = memory_point_footprint instructions (prefix++values).
Proof.
  intro LENGTH; induction instructions; [reflexivity|].
  cbn [memory_scalar_instruction_sequence memory_loop_list_trace memory_loop_trace].
  unfold memory_events_footprint at 1; rewrite flat_map_app.
  cbn [flat_map event_instruction event_arguments].
  rewrite memory_scalar_arguments_value_tail by exact LENGTH.
  rewrite app_nil_r.
  change (memory_instruction_footprint a (prefix++values)++
    memory_events_footprint (memory_loop_list_trace
      (memory_scalar_instruction_sequence (length prefix) (length values) instructions)
      (rev prefix++counts++(values++tail))) = memory_point_footprint (a::instructions) (prefix++values)).
  rewrite IHinstructions; reflexivity.
Qed.
Theorem memory_scalar_rectangle_footprint_tail counts instructions values tail : forall prefix previous,
  length prefix = length previous ->
  memory_events_footprint (memory_loop_trace
    (memory_scalar_rectangle (length prefix) (length counts) (length values) instructions)
    (rev prefix++(previous++counts)++(values++tail))) =
  flat_map (fun coordinates => memory_point_footprint instructions (coordinates++values))
    (memory_rectangular_points (counts) prefix).
Proof.
  induction counts as [|count counts IH]; intros prefix previous LENGTH.
  - cbn [length memory_scalar_rectangle memory_loop_trace map memory_rectangular_points flat_map].
    rewrite app_nil_r,app_nil_r; apply memory_scalar_sequence_footprint_tail; exact LENGTH.
  - cbn [length memory_scalar_rectangle memory_loop_trace L.eval_expr memory_rectangular_points].
    rewrite memory_scalar_bound_z_value by exact LENGTH.
    unfold memory_events_footprint at 1; rewrite memory_flat_map_associative.
    rewrite memory_flat_map_associative.
    apply flat_map_ext; intro coordinate.
    change (memory_events_footprint (memory_loop_trace
      (memory_scalar_rectangle (S (length prefix)) (length counts) (length values) instructions)
      (coordinate::rev prefix++(previous++count::counts)++(values++tail))) =
      flat_map (fun coordinates => memory_point_footprint instructions (coordinates++values))
        (memory_rectangular_points (counts) (prefix++[coordinate]))).
    replace (S (length prefix)) with (length (prefix++[coordinate])) by (rewrite length_app; cbn; lia).
    replace (coordinate::rev prefix++(previous++count::counts)++(values++tail)) with
      (rev (prefix++[coordinate])++((previous++[count])++counts)++(values++tail)) by
      (rewrite rev_app_distr; cbn; repeat rewrite <- app_assoc; reflexivity).
    apply IH; rewrite !length_app; cbn; lia.
Qed.

Definition memory_started_rectangular_points upper counts start :=
  flat_map (fun x => memory_rectangular_points counts [x]) (Zrange start upper).
Lemma memory_started_rectangular_points_member upper counts start coordinates :
  In coordinates (memory_started_rectangular_points upper counts start) <->
  memory_started_axis_coordinates start (upper::counts) coordinates.
Proof.
  unfold memory_started_rectangular_points; rewrite in_flat_map; split.
  - intros [x [RANGE POINT]].
    apply Zrange_in in RANGE; apply memory_rectangular_points_member in POINT as [suffix [-> REST]].
    exact (conj RANGE REST).
  - destruct coordinates as [|x suffix]; [contradiction|].
    cbn [memory_started_axis_coordinates]; intros [RANGE REST].
    exists x; split; [apply Zrange_in; exact RANGE|].
    apply memory_rectangular_points_member; exists suffix; auto.
Qed.
Theorem memory_started_scalar_loop_footprint upper counts instructions values start :
  memory_events_footprint (memory_loop_trace
    (memory_started_scalar_loop (S (length counts)) (length values) instructions)
    ((upper::counts)++values++[start])) =
  flat_map (fun coordinates => memory_point_footprint instructions (coordinates++values))
    (memory_started_rectangular_points upper counts start).
Proof.
  assert (LOWER : nth (S (length counts)+length values)%nat ((upper::counts)++values++[start]) 0 = start).
  { replace (S (length counts)+length values)%nat with (length ((upper::counts)++values))
      by (rewrite length_app; cbn; lia).
    rewrite app_assoc; apply nth_middle. }
  unfold memory_started_scalar_loop; cbn [Nat.pred memory_loop_trace L.eval_expr].
  rewrite LOWER.
  unfold memory_events_footprint at 1; rewrite memory_flat_map_associative.
  unfold memory_started_rectangular_points; rewrite memory_flat_map_associative.
  apply flat_map_ext; intro x.
  pose proof (@memory_scalar_rectangle_footprint_tail counts instructions values [start] [x] [upper] eq_refl) as FOOTPRINT.
  cbn [length rev app] in FOOTPRINT; exact FOOTPRINT.
Qed.
Print Assumptions memory_started_scalar_loop_footprint.
Print Assumptions memory_started_rectangular_points_member.

Lemma memory_boolean_started_rectangle_member test upper counts start :
  start <= upper -> Forall (fun count => 0 <= count) counts ->
  memory_boolean_started_rectangle_result test upper counts start = true <->
  forall coordinates, memory_started_axis_coordinates start (upper::counts) coordinates -> test coordinates = true.
Proof.
  intros ORDER NONNEG; unfold memory_boolean_started_rectangle_result.
  rewrite memory_boolean_scan_member; rewrite Z2Nat.id by lia.
  split.
  - intros CHECK [|x coordinates] DOMAIN; [contradiction|].
    destruct DOMAIN as [RANGE TAIL].
    specialize (CHECK x ltac:(lia)); rewrite (@memory_boolean_rectangle_member test counts NONNEG [x]) in CHECK.
    specialize (CHECK coordinates TAIL); exact CHECK.
  - intros CHECK x RANGE; apply (proj2 (@memory_boolean_rectangle_member test counts NONNEG [x])).
    intros coordinates TAIL; apply CHECK; cbn [memory_started_axis_coordinates]; split; [lia|exact TAIL].
Qed.
Print Assumptions memory_boolean_started_rectangle_member.
