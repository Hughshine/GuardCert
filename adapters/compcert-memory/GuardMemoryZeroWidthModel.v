From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineMappedExtractor GuardMemoryExtractedTiling GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceEndpoints GuardMemoryParametricChecker.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Domain-library assumption: every child width is nonnegative and bounded.
    This assumption permits empty children. Body-input licensing is a separate
    source/language obligation; this model predicate cannot license a read. *)
Definition memory_source_zero_width_test cap first last :=
  L.And (L.LE (L.Constant 0) first)
    (L.And (L.LE first (L.Constant cap))
      (L.And (L.LE (L.Constant 0) last) (L.LE last (L.Constant cap)))).
Definition memory_source_zero_width_model cap row context expression parameters :=
  match memory_source_endpoints row context expression with
  | Some (first,last) => L.eval_test parameters (memory_source_zero_width_test cap first last)
  | None => false end.

Theorem memory_source_zero_endpoints_exact expression row bound parameters valuation cap first last :
  0 < valuation bound ->
  memory_source_endpoints row (bound::parameters) expression = Some (first,last) ->
  (L.eval_test (map valuation (bound::parameters))
     (memory_source_zero_width_test cap first last) = true <->
   forall i, 0 <= i < valuation bound ->
     0 <= memory_source_affine_math (memory_source_set_valuation valuation row i) expression <= cap).
Proof.
  intros POSITIVE ENDS; unfold memory_source_endpoints in ENDS.
  destruct (memory_source_endpoint_expression row (bound::parameters) (L.Constant 0) expression)
    as [a|] eqn:FIRST; [|discriminate].
  destruct (memory_source_endpoint_expression row (bound::parameters)
    (L.Sum (L.Var O) (L.Constant (-1))) expression) as [b|] eqn:LAST; [|discriminate].
  injection ENDS as A B; subst a b.
  pose proof (@memory_source_endpoint_value expression row (bound::parameters)
    (L.Constant 0) first valuation FIRST) as F.
  pose proof (@memory_source_endpoint_value expression row (bound::parameters)
    (L.Sum (L.Var O) (L.Constant (-1))) last valuation LAST) as E.
  cbn [L.eval_expr map nth] in F,E.
  replace (valuation bound + -1) with (valuation bound-1) in E by ring.
  unfold memory_source_zero_width_test; cbn [L.eval_test map].
  rewrite F,E; repeat rewrite andb_true_iff; repeat rewrite Z.leb_le.
  split.
  - intros ENDPOINTS i I; apply memory_source_affine_row_extrema with (last:=valuation bound-1); tauto || lia.
  - intro ALL; pose proof (ALL 0 ltac:(lia)); pose proof (ALL (valuation bound-1) ltac:(lia)); tauto.
Qed.

Theorem memory_source_zero_width_model_exact expression row bound parameters valuation cap first last :
  0 < valuation bound ->
  memory_source_endpoints row (bound::parameters) expression = Some (first,last) ->
  (memory_source_zero_width_model cap row (bound::parameters) expression
     (map valuation (bound::parameters)) = true <->
   forall i, 0 <= i < valuation bound ->
     0 <= memory_source_affine_math (memory_source_set_valuation valuation row i) expression <= cap).
Proof.
  intros POSITIVE ENDS; unfold memory_source_zero_width_model; rewrite ENDS.
  eapply memory_source_zero_endpoints_exact; eassumption.
Qed.

Definition memory_zero_width_assumed_loop cap row context bounds expression loop :=
  L.Guard (memory_source_bounds_test_from O bounds)
    (match memory_source_endpoints row context expression with
     | Some (first,last) => L.Guard (memory_source_zero_width_test cap first last) loop
     | None => L.Guard (L.LE (L.Constant 1) (L.Constant 0)) loop end).

Lemma memory_zero_width_assumed_execution cap row context bounds expression parameters before after loop :
  MemoryNested.A.env_within bounds parameters ->
  memory_source_zero_width_model cap row context expression parameters = true ->
  (L.loop_semantics (memory_zero_width_assumed_loop cap row context bounds expression loop)
      parameters before after <-> L.loop_semantics loop parameters before after).
Proof.
  intros WITHIN WIDTH; pose proof (memory_source_bounds_test_true WITHIN) as RANGES.
  unfold memory_zero_width_assumed_loop,memory_source_zero_width_model in *.
  destruct (memory_source_endpoints row context expression) as [[first last]|]; [|discriminate].
  split; intro RUN.
  - inversion RUN; subst; [|congruence].
    match goal with INNER : L.loop_semantics (L.Guard _ _) _ _ _ |- _ =>
      inversion INNER; subst; [assumption|congruence] end.
  - apply L.LGuardTrue; [apply L.LGuardTrue; assumption|exact RANGES].
Qed.

(** C_opt must be obtained for this assumed source and this assumed candidate.
    A certificate checked under the old first-positive assumption is insufficient. *)
Definition memory_zero_width_candidate_certificate cap source row context bounds expression candidate :=
  forall parameters initial final,
    length parameters = length context -> MemoryNested.A.env_within bounds parameters ->
    memory_source_zero_width_model cap row context expression parameters = true ->
    GuardMemoryInstr.NonAlias initial -> L.loop_semantics source parameters initial final ->
    L.loop_semantics candidate parameters initial final.
Definition checked_zero_width_model_candidate cap source arrays row context bounds expression candidate steps :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_affine_mapped_domain_loops
    (memory_zero_width_assumed_loop cap row context bounds expression source,context,vars)
    (memory_zero_width_assumed_loop cap row context bounds expression candidate,context,vars) steps.

Theorem checked_zero_width_model_candidate_correct cap source arrays row context bounds expression candidate steps :
  mayReturn (checked_zero_width_model_candidate cap source arrays row context bounds expression candidate steps) true ->
  memory_zero_width_candidate_certificate cap source row context bounds expression candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN WIDTH NONALIAS SOURCE.
  apply memory_zero_width_assumed_execution with (cap:=cap) (row:=row) (context:=context)
    (bounds:=bounds) (expression:=expression); [exact WITHIN|exact WIDTH|].
  pose proof (@validated_memory_affine_mapped_domain_loops_at
    (memory_zero_width_assumed_loop cap row context bounds expression source)
    (memory_zero_width_assumed_loop cap row context bounds expression candidate) context
    (map (fun array => (array,tt)) (context++arrays)) steps (rev parameters) before after
    ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply (proj1 VALID); apply memory_zero_width_assumed_execution; assumption.
Qed.

Definition checked_zero_width_model_tiling cap source arrays row context bounds expression candidate witnesses :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_extracted_tiling_loops
    (memory_zero_width_assumed_loop cap row context bounds expression source,context,vars)
    (memory_zero_width_assumed_loop cap row context bounds expression candidate,context,vars) witnesses.
Theorem checked_zero_width_model_tiling_correct cap source arrays row context bounds expression candidate witnesses :
  mayReturn (checked_zero_width_model_tiling cap source arrays row context bounds expression candidate witnesses) true ->
  memory_zero_width_candidate_certificate cap source row context bounds expression candidate.
Proof.
  intros CHECK parameters before after LENGTH WITHIN WIDTH NONALIAS SOURCE.
  apply memory_zero_width_assumed_execution with (cap:=cap) (row:=row) (context:=context)
    (bounds:=bounds) (expression:=expression); [exact WITHIN|exact WIDTH|].
  pose proof (@validated_memory_extracted_tiling_loops_at
    (memory_zero_width_assumed_loop cap row context bounds expression source)
    (memory_zero_width_assumed_loop cap row context bounds expression candidate) context
    (map (fun array => (array,tt)) (context++arrays)) witnesses (rev parameters) before after
    ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply VALID; apply memory_zero_width_assumed_execution; assumption.
Qed.

Print Assumptions memory_source_zero_endpoints_exact.
Print Assumptions memory_source_zero_width_model_exact.
Print Assumptions memory_zero_width_assumed_execution.
Print Assumptions checked_zero_width_model_candidate_correct.
Print Assumptions checked_zero_width_model_tiling_correct.
