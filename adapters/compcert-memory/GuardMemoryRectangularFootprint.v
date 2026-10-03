From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryFiniteFootprint GuardMemoryScalarLoops GuardMemoryNaryLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_rectangular_points counts prefix : list (list Z) :=
  match counts with
  | [] => [prefix]
  | count::rest => flat_map (fun coordinate => memory_rectangular_points rest (prefix++[coordinate])) (Zrange 0 count)
  end.
Definition memory_instruction_footprint instruction values :=
  exact_cell (instruction_write instruction) values::
    map (fun access => exact_cell access values) (instruction_reads instruction).
Definition memory_point_footprint instructions values :=
  flat_map (fun instruction => memory_instruction_footprint instruction values) instructions.

Lemma memory_flat_map_associative {A B C} (f : B -> list C) (g : A -> list B) xs :
  flat_map f (flat_map g xs) = flat_map (fun x => flat_map f (g x)) xs.
Proof. induction xs; cbn; [reflexivity|rewrite flat_map_app,IHxs; reflexivity]. Qed.
Lemma memory_scalar_sequence_footprint instructions prefix counts values :
  length prefix = length counts ->
  memory_events_footprint (memory_loop_list_trace
    (memory_scalar_instruction_sequence (length prefix) (length values) instructions)
    (rev prefix++counts++values)) = memory_point_footprint instructions (prefix++values).
Proof.
  intro LENGTH; induction instructions; [reflexivity|].
  cbn [memory_scalar_instruction_sequence memory_loop_list_trace memory_loop_trace].
  unfold memory_events_footprint at 1; rewrite flat_map_app.
  cbn [flat_map event_instruction event_arguments].
  rewrite memory_scalar_arguments_value by exact LENGTH.
  rewrite app_nil_r.
  change (memory_instruction_footprint a (prefix++values)++
    memory_events_footprint (memory_loop_list_trace
      (memory_scalar_instruction_sequence (length prefix) (length values) instructions)
      (rev prefix++counts++values)) = memory_point_footprint (a::instructions) (prefix++values)).
  rewrite IHinstructions; reflexivity.
Qed.
Lemma memory_scalar_bound_z_value prefix previous count counts values :
  length prefix = length previous ->
  nth (2*length prefix)%nat (rev prefix++(previous++count::counts)++values) 0 = count.
Proof.
  intro LENGTH; rewrite !app_assoc.
  replace (2*length prefix)%nat with (length (rev prefix++previous)) by
    (rewrite length_app,length_rev; lia).
  rewrite <- app_assoc; apply nth_middle.
Qed.
Theorem memory_scalar_rectangle_footprint counts instructions values : forall prefix previous,
  length prefix = length previous ->
  memory_events_footprint (memory_loop_trace
    (memory_scalar_rectangle (length prefix) (length counts) (length values) instructions)
    (rev prefix++(previous++counts)++values)) =
  flat_map (fun coordinates => memory_point_footprint instructions (coordinates++values))
    (memory_rectangular_points (counts) prefix).
Proof.
  induction counts as [|count counts IH]; intros prefix previous LENGTH.
  - cbn [length memory_scalar_rectangle memory_loop_trace map memory_rectangular_points flat_map].
    rewrite app_nil_r,app_nil_r; apply memory_scalar_sequence_footprint; exact LENGTH.
  - cbn [length memory_scalar_rectangle memory_loop_trace L.eval_expr memory_rectangular_points].
    rewrite memory_scalar_bound_z_value by exact LENGTH.
    unfold memory_events_footprint at 1; rewrite memory_flat_map_associative.
    rewrite memory_flat_map_associative.
    apply flat_map_ext; intro coordinate.
    change (memory_events_footprint (memory_loop_trace
      (memory_scalar_rectangle (S (length prefix)) (length counts) (length values) instructions)
      (coordinate::rev prefix++(previous++count::counts)++values)) =
      flat_map (fun coordinates => memory_point_footprint instructions (coordinates++values))
        (memory_rectangular_points (counts) (prefix++[coordinate]))).
    replace (S (length prefix)) with (length (prefix++[coordinate])) by (rewrite length_app; cbn; lia).
    replace (coordinate::rev prefix++(previous++count::counts)++values) with
      (rev (prefix++[coordinate])++((previous++[count])++counts)++values) by
      (rewrite rev_app_distr; cbn; repeat rewrite <- app_assoc; reflexivity).
    apply IH; rewrite !length_app; cbn; lia.
Qed.

Lemma memory_rectangular_points_member counts : forall prefix coordinates,
  In coordinates (memory_rectangular_points counts prefix) <->
  exists suffix, coordinates = prefix++suffix /\ Forall2 (fun coordinate count => 0 <= coordinate < count) suffix counts.
Proof.
  induction counts as [|count counts IH]; intros prefix coordinates; cbn; split.
  - intros [SAME|[]]; exists []; split; [subst; rewrite app_nil_r; reflexivity|constructor].
  - intros [suffix [SAME RANGE]]; inversion RANGE; subst; left; rewrite app_nil_r; reflexivity.
  - intro MEMBER; apply in_flat_map in MEMBER as [coordinate [MEMBER POINT]].
    apply Zrange_in in MEMBER; apply IH in POINT as [suffix [SAME RANGE]].
    exists (coordinate::suffix); split; [rewrite SAME,<-app_assoc; reflexivity|constructor; assumption].
  - intros [suffix [SAME RANGE]]; inversion RANGE; subst.
    apply in_flat_map; eexists; split; [apply Zrange_in; eassumption|].
    apply IH; eexists; split; [rewrite <-app_assoc; reflexivity|eassumption].
Qed.
Lemma memory_rectangular_points_origin counts coordinates :
  In coordinates (memory_rectangular_points counts []) <-> Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts.
Proof. rewrite memory_rectangular_points_member; cbn; split;
  [intros [suffix [-> RANGE]]; exact RANGE|intro RANGE; exists coordinates; auto]. Qed.
Print Assumptions memory_scalar_rectangle_footprint.
Print Assumptions memory_rectangular_points_member.
