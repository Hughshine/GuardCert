From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineMappedExtractor GuardMemoryAffineReindex GuardMemoryNamedOperations
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceEndpoints GuardMemoryParametricLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_source_bounds_test_from index bounds :=
  match bounds with
  | [] => L.LE (L.Constant 0) (L.Constant 0)
  | interval::rest => L.And
      (L.And (L.LE (L.Constant (MemoryNested.A.lower interval)) (L.Var index))
        (L.LE (L.Var index) (L.Constant (MemoryNested.A.upper interval))))
      (memory_source_bounds_test_from (S index) rest) end.
Lemma memory_source_bounds_test_from_true bounds index parameters :
  (forall offset interval, nth_error bounds offset = Some interval ->
    MemoryNested.A.contains interval (nth (index+offset) parameters 0)) ->
  L.eval_test parameters (memory_source_bounds_test_from index bounds) = true.
Proof.
  revert index; induction bounds as [|interval rest IH]; intros index WITHIN.
  - reflexivity.
  - cbn [memory_source_bounds_test_from L.eval_test L.eval_expr].
    apply andb_true_iff; split.
    + specialize (WITHIN O interval eq_refl); rewrite Nat.add_0_r in WITHIN.
      unfold MemoryNested.A.contains in WITHIN; apply andb_true_iff; split; apply Z.leb_le; tauto.
    + apply IH; intros offset item POSITION.
      specialize (WITHIN (S offset) item POSITION).
      replace (index+S offset)%nat with (S index+offset)%nat in WITHIN by lia; exact WITHIN.
Qed.
Lemma memory_source_bounds_test_true bounds parameters :
  MemoryNested.A.env_within bounds parameters ->
  L.eval_test parameters (memory_source_bounds_test_from O bounds) = true.
Proof.
  intro WITHIN; apply memory_source_bounds_test_from_true; exact WITHIN.
Qed.
Definition memory_source_width_model stride row context expression parameters :=
  match memory_source_endpoints row context expression with
  | Some (first,last) => L.eval_test parameters (memory_source_endpoint_test stride first last)
  | None => false end.
Definition memory_parametric_assumed_loop base row context bounds expression loop :=
  L.Guard (memory_source_bounds_test_from O bounds)
    (match memory_source_endpoints row context expression with
    | Some (first,last) => L.Guard (memory_source_endpoint_test (rectangle_stride base) first last) loop
    | None => L.Guard (L.LE (L.Constant 1) (L.Constant 0)) loop end).
Lemma memory_parametric_assumed_execution base row context bounds expression parameters before after loop :
  MemoryNested.A.env_within bounds parameters ->
  memory_source_width_model (rectangle_stride base) row context expression parameters = true ->
  (L.loop_semantics (memory_parametric_assumed_loop base row context bounds expression loop) parameters before after <->
    L.loop_semantics loop parameters before after).
Proof.
  intros WITHIN WIDTH; pose proof (memory_source_bounds_test_true WITHIN) as RANGES.
  unfold memory_parametric_assumed_loop,memory_source_width_model in *.
  destruct (memory_source_endpoints row context expression) as [[first last]|]; [|discriminate].
  split; intro RUN.
  - inversion RUN; subst; [|congruence].
    match goal with INNER : L.loop_semantics (L.Guard _ _) _ _ _ |- _ =>
      inversion INNER; subst; [assumption|congruence] end.
  - apply L.LGuardTrue; [apply L.LGuardTrue; assumption|exact RANGES].
Qed.
Definition memory_parametric_candidate_certificate base operations row context bounds expression encoded candidate :=
  forall parameters initial final,
    length parameters = length context -> MemoryNested.A.env_within bounds parameters ->
    memory_source_width_model (rectangle_stride base) row context expression parameters = true ->
    GuardMemoryInstr.NonAlias initial ->
    L.loop_semantics (memory_parametric_sequence encoded (map named_operation_instruction operations)) parameters initial final ->
    L.loop_semantics candidate parameters initial final.
Definition checked_named_parametric_candidate base operations row context bounds expression encoded candidate steps :=
  let vars := map (fun array => (array,tt)) (context++flat_map named_operation_arrays operations) in
  checked_memory_affine_mapped_domain_loops
    (memory_parametric_assumed_loop base row context bounds expression
      (memory_parametric_sequence encoded (map named_operation_instruction operations)),context,vars)
    (memory_parametric_assumed_loop base row context bounds expression candidate,context,vars) steps.
Theorem checked_named_parametric_candidate_correct base operations row context bounds expression encoded candidate steps :
  mayReturn (checked_named_parametric_candidate base operations row context bounds expression encoded candidate steps) true ->
  memory_parametric_candidate_certificate base operations row context bounds expression encoded candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN WIDTH NONALIAS SOURCE.
  unfold checked_named_parametric_candidate in CHECK.
  apply memory_parametric_assumed_execution with (base := base) (row := row) (context := context)
    (bounds := bounds) (expression := expression); [exact WITHIN|exact WIDTH|].
  pose proof (@validated_memory_affine_mapped_domain_loops_at
    (memory_parametric_assumed_loop base row context bounds expression
      (memory_parametric_sequence encoded (map named_operation_instruction operations)))
    (memory_parametric_assumed_loop base row context bounds expression candidate) context
    (map (fun array => (array,tt)) (context++flat_map named_operation_arrays operations))
    steps (rev parameters) before after ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply (proj1 VALID).
  apply memory_parametric_assumed_execution; assumption.
Qed.
Print Assumptions checked_named_parametric_candidate_correct.
