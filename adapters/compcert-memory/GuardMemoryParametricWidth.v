From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From Guard Require Import ClightCondition ClightPureExpr.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceLoop GuardMemoryAffineSourceEndpoints.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition compile_memory_source_width stride row context bounds expression :=
  match memory_source_endpoints row context expression with
  | Some (first,last) => MemoryNested.A.lower_test context bounds (memory_source_endpoint_test stride first last)
  | None => None end.
Theorem compile_memory_source_width_pure stride row context bounds expression tree :
  compile_memory_source_width stride row context bounds expression = Some tree -> pure_tree tree.
Proof.
  unfold compile_memory_source_width.
  destruct (memory_source_endpoints row context expression) as [[first last]|] eqn:ENDPOINTS; [|discriminate].
  apply MemoryNested.A.lower_test_pure.
Qed.
Theorem compile_memory_source_width_sound stride row bound parameters bounds expression tree valuation ge locals temps memory :
  0 < valuation bound ->
  compile_memory_source_width stride row (bound::parameters) bounds expression = Some tree ->
  MemoryNested.A.typed_view (bound::parameters) (map valuation (bound::parameters)) temps ->
  MemoryNested.A.env_within bounds (map valuation (bound::parameters)) ->
  decision_run (Entry ge locals temps memory) tree true ->
  0 < memory_source_affine_math (memory_source_set_valuation valuation row 0) expression /\
  forall value, 0 <= value < valuation bound ->
    0 <= memory_source_affine_math (memory_source_set_valuation valuation row value) expression <= stride.
Proof.
  intros POSITIVE COMPILE VIEW RANGE RUN; unfold compile_memory_source_width in COMPILE.
  destruct (memory_source_endpoints row (bound::parameters) expression) as [[first last]|] eqn:ENDPOINTS; [|discriminate].
  pose proof (proj1 (@MemoryNested.A.lower_test_exact (memory_source_endpoint_test stride first last)
    (bound::parameters) bounds tree (map valuation (bound::parameters)) temps ge locals memory true COMPILE RANGE VIEW) RUN) as FLAG.
  eapply (@memory_source_endpoints_sound expression row bound parameters valuation stride first last);
    [exact POSITIVE|exact ENDPOINTS|symmetry; exact FLAG].
Qed.
Theorem compile_memory_source_width_exact stride row context bounds expression tree parameters ge locals temps memory :
  compile_memory_source_width stride row context bounds expression = Some tree ->
  MemoryNested.A.typed_view context parameters temps -> MemoryNested.A.env_within bounds parameters ->
  exists first last, memory_source_endpoints row context expression = Some (first,last) /\
    forall flag, decision_run (Entry ge locals temps memory) tree flag <->
      flag = L.eval_test parameters (memory_source_endpoint_test stride first last).
Proof.
  intros COMPILE VIEW RANGE; unfold compile_memory_source_width in COMPILE.
  destruct (memory_source_endpoints row context expression) as [[first last]|] eqn:ENDPOINTS; [|discriminate].
  exists first,last; split; [reflexivity|].
  intro flag; eapply MemoryNested.A.lower_test_exact; eassumption.
Qed.
Print Assumptions compile_memory_source_width_sound.
Print Assumptions compile_memory_source_width_exact.
