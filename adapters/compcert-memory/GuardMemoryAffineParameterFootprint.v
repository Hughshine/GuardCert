From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From polcert.src Require Import PolyBase.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryLoopTrace GuardMemoryFiniteFootprint GuardMemoryRectangularFootprint
  GuardMemoryAffineParameterLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Enumerate the actual ragged domain, rather than its rectangular envelope.
    The entry context contains the outer bound and all stable parameters. *)
Definition memory_affine_parameter_points expression context :=
  flat_map (fun i => map (fun j => [i;j])
    (Zrange 0 (L.eval_expr (i::context) expression))) (Zrange 0 (L.eval_expr context (L.Var 0))).

Lemma memory_affine_parameter_point_member expression context coordinates :
  In coordinates (memory_affine_parameter_points expression context) <->
  exists i j, coordinates = [i;j] /\
    0 <= i < L.eval_expr context (L.Var 0) /\
    0 <= j < L.eval_expr (i::context) expression.
Proof.
  unfold memory_affine_parameter_points; rewrite in_flat_map; split.
  - intros [i [I POINT]]; apply Zrange_in in I.
    apply in_map_iff in POINT as [j [SAME J]]; apply Zrange_in in J; exists i,j; auto.
  - intros [i [j [-> [I J]]]]; exists i; split; [apply Zrange_in; exact I|].
    apply in_map_iff; exists j; split; [reflexivity|apply Zrange_in; exact J].
Qed.

Lemma memory_affine_parameter_instruction_footprint instructions i j context :
  memory_events_footprint (memory_loop_list_trace
    (memory_affine_parameter_instructions (length context) instructions) (j::i::context)) =
  memory_point_footprint instructions ([i;j]++context).
Proof.
  induction instructions as [|instruction instructions IH]; [reflexivity|].
  cbn [memory_affine_parameter_instructions memory_loop_list_trace memory_loop_trace].
  unfold memory_events_footprint at 1; rewrite flat_map_app.
  cbn [flat_map event_instruction event_arguments].
  rewrite memory_affine_parameter_arguments_value,app_nil_r.
  change (memory_instruction_footprint instruction ([i;j]++context) ++
    memory_events_footprint (memory_loop_list_trace
      (memory_affine_parameter_instructions (length context) instructions) (j::i::context)) =
    memory_point_footprint (instruction::instructions) ([i;j]++context)).
  rewrite IH; reflexivity.
Qed.

Lemma memory_affine_parameter_row_footprint expression instructions context i :
  memory_events_footprint (memory_loop_trace
    (L.Loop (L.Constant 0) expression
      (L.Seq (memory_affine_parameter_instructions (length context) instructions))) (i::context)) =
  flat_map (fun j => memory_point_footprint instructions ([i;j]++context))
    (Zrange 0 (L.eval_expr (i::context) expression)).
Proof.
  cbn [memory_loop_trace L.eval_expr].
  unfold memory_events_footprint at 1; rewrite memory_flat_map_associative.
  apply flat_map_ext; intro j; apply memory_affine_parameter_instruction_footprint.
Qed.

Lemma memory_loop_footprint_loop lower upper body context :
  memory_events_footprint (memory_loop_trace (L.Loop lower upper body) context) =
  flat_map (fun i => memory_events_footprint (memory_loop_trace body (i::context)))
    (Zrange (L.eval_expr context lower) (L.eval_expr context upper)).
Proof.
  cbn [memory_loop_trace]; unfold memory_events_footprint;
    apply memory_flat_map_associative.
Qed.

Theorem memory_affine_parameter_sequence_footprint expression instructions context :
  memory_events_footprint (memory_loop_trace
    (memory_affine_parameter_sequence (length context) expression instructions) context) =
  flat_map (fun coordinates => memory_point_footprint instructions (coordinates++context))
    (memory_affine_parameter_points expression context).
Proof.
  unfold memory_affine_parameter_sequence,memory_affine_parameter_points.
  rewrite memory_loop_footprint_loop; cbn [L.eval_expr].
  rewrite memory_flat_map_associative.
  apply flat_map_ext; intro i.
  rewrite memory_affine_parameter_row_footprint.
  rewrite !flat_map_concat_map,map_map; reflexivity.
Qed.

(** The box is used only to derive a sufficient condition. It does not license
    guard loads at points absent from the actual source domain. *)
Theorem memory_affine_parameter_points_box expression context column_cap :
  (forall i, 0 <= i < L.eval_expr context (L.Var 0) ->
    L.eval_expr (i::context) expression <= column_cap) ->
  forall coordinates, In coordinates (memory_affine_parameter_points expression context) ->
    Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates
      [L.eval_expr context (L.Var 0);column_cap].
Proof.
  intros BOUND coordinates POINT.
  apply memory_affine_parameter_point_member in POINT as [i [j [-> [I J]]]].
  constructor; [exact I|constructor; [specialize (BOUND i I); lia|constructor]].
Qed.

Print Assumptions memory_affine_parameter_sequence_footprint.
Print Assumptions memory_affine_parameter_point_member.
Print Assumptions memory_affine_parameter_points_box.
