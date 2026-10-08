From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceEndpoints.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Header-only affine endpoint evidence. It neither observes body parameters
    nor requires a positive leaf. The checked machine lowering is reused. *)
Definition affine_empty_width_test first last :=
  L.And(L.LE(L.Constant 1)(L.Var O))
    (L.And(L.And(L.LE(L.Constant Int.min_signed)first)(L.LE first(L.Constant 0)))
      (L.And(L.LE(L.Constant Int.min_signed)last)(L.LE last(L.Constant 0)))).
Definition affine_empty_width_fact expression valuation row bound :=
  0<valuation bound /\ forall i,0<=i<valuation bound ->
    Int.min_signed<=memory_source_affine_math(memory_source_set_valuation valuation row i)expression<=0.
Definition compile_affine_empty_width row context bounds expression :=
  match memory_source_endpoints row context expression with
  | Some(first,last)=>MemoryNested.A.lower_test context bounds(affine_empty_width_test first last)
  | None=>None end.

Lemma affine_empty_width_math_sound expression valuation row bound first last :
  first=memory_source_affine_math(memory_source_set_valuation valuation row 0)expression ->
  last=memory_source_affine_math(memory_source_set_valuation valuation row(valuation bound-1))expression ->
  1<=valuation bound -> Int.min_signed<=first<=0 -> Int.min_signed<=last<=0 ->
  affine_empty_width_fact expression valuation row bound.
Proof.
  intros FIRST LAST COUNT LOW HIGH; subst first last; split; [lia|].
  intros i I; apply memory_source_affine_row_extrema with(last:=valuation bound-1); try assumption; lia.
Qed.

Theorem compile_affine_empty_width_sound row bound parameters bounds expression tree valuation
    ge locals temps memory :
  compile_affine_empty_width row(bound::parameters)bounds expression=Some tree ->
  MemoryNested.A.typed_view(bound::parameters)(map valuation(bound::parameters))temps ->
  MemoryNested.A.env_within bounds(map valuation(bound::parameters)) ->
  decision_run(Entry ge locals temps memory)tree true ->
  affine_empty_width_fact expression valuation row bound.
Proof.
  intros COMPILE VIEW RANGE RUN; unfold compile_affine_empty_width in COMPILE.
  destruct(memory_source_endpoints row(bound::parameters)expression)as [[first last]|]eqn:ENDS;
    [|discriminate].
  pose proof(proj1(@MemoryNested.A.lower_test_exact(affine_empty_width_test first last)
    (bound::parameters)bounds tree(map valuation(bound::parameters))temps ge locals memory true
    COMPILE RANGE VIEW)RUN)as FLAG.
  assert(TEST:L.eval_test(map valuation(bound::parameters))(affine_empty_width_test first last)=true)by congruence.
  unfold memory_source_endpoints in ENDS.
  destruct(memory_source_endpoint_expression row(bound::parameters)(L.Constant 0)expression)
    as [a|]eqn:FIRST; [|discriminate].
  destruct(memory_source_endpoint_expression row(bound::parameters)(L.Sum(L.Var O)(L.Constant(-1)))expression)
    as [b|]eqn:LAST; [|discriminate].
  injection ENDS as A B; subst a b.
  pose proof(@memory_source_endpoint_value expression row(bound::parameters)(L.Constant 0)first valuation FIRST)as F.
  pose proof(@memory_source_endpoint_value expression row(bound::parameters)(L.Sum(L.Var O)(L.Constant(-1)))
    last valuation LAST)as LST.
  cbn [L.eval_expr map nth]in F,LST.
  replace(valuation bound+ -1)with(valuation bound-1)in LST by ring.
  eapply(@affine_empty_width_math_sound expression valuation row bound
    (L.eval_expr(map valuation(bound::parameters))first)(L.eval_expr(map valuation(bound::parameters))last));
    [exact F|exact LST| | |].
  all: unfold affine_empty_width_test in TEST; cbn [L.eval_test L.eval_expr map nth]in TEST;
    repeat rewrite andb_true_iff in TEST; repeat rewrite Z.leb_le in TEST; tauto.
Qed.

Theorem affine_empty_width_word_facts expression valuation row bound :
  affine_empty_width_fact expression valuation row bound -> forall i,0<=i<valuation bound ->
    Int.lt Int.zero(Int.repr(memory_source_affine_math(memory_source_set_valuation valuation row i)expression))=false.
Proof.
  intros [COUNT WIDTH]i I; specialize(WIDTH i I); unfold Int.lt.
  rewrite Int.signed_zero,Int.signed_repr by(unfold signed_range; change Int.max_signed with 2147483647; lia).
  destruct(zlt 0(memory_source_affine_math(memory_source_set_valuation valuation row i)expression));
    [lia|reflexivity].
Qed.

Theorem compile_affine_empty_width_exact row context bounds expression tree parameters ge locals temps memory :
  compile_affine_empty_width row context bounds expression=Some tree ->
  MemoryNested.A.typed_view context parameters temps -> MemoryNested.A.env_within bounds parameters ->
  exists first last,memory_source_endpoints row context expression=Some(first,last) /\
    forall flag,decision_run(Entry ge locals temps memory)tree flag <->
      flag=L.eval_test parameters(affine_empty_width_test first last).
Proof.
  intros COMPILE VIEW RANGE; unfold compile_affine_empty_width in COMPILE.
  destruct(memory_source_endpoints row context expression)as [[first last]|]eqn:ENDS; [|discriminate].
  exists first,last; split; [reflexivity|].
  intro flag; eapply MemoryNested.A.lower_test_exact; eassumption.
Qed.

Print Assumptions affine_empty_width_math_sound.
Print Assumptions compile_affine_empty_width_sound.
Print Assumptions affine_empty_width_word_facts.
Print Assumptions compile_affine_empty_width_exact.
