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

(** A domain service: constant-many affine endpoint tests establish which
    child first reaches a body. Language lowering remains the existing checked
    machine-arithmetic compiler. This is not a universal assumption extractor. *)
Definition first_reached_width_test low high skip first last previous selected :=
  L.And(L.LE(L.Constant(Z.of_nat skip+1))(L.Var O))
    (L.And(L.And(L.LE(L.Constant low)first)(L.LE first(L.Constant high)))
      (L.And(L.And(L.LE(L.Constant low)last)(L.LE last(L.Constant high)))
        (L.And(L.LE(L.Constant 1)selected)
          (match skip with O=>L.LE(L.Constant 0)(L.Constant 0)
           | S _=>L.LE previous(L.Constant 0)end)))).

Definition first_reached_width_fact expression valuation row bound low high skip :=
  0<=Z.of_nat skip<valuation bound /\
  (forall i,0<=i<valuation bound -> low<=memory_source_affine_math
    (memory_source_set_valuation valuation row i)expression<=high) /\
  (forall i,0<=i<Z.of_nat skip -> memory_source_affine_math
    (memory_source_set_valuation valuation row i)expression<=0) /\
  0<memory_source_affine_math(memory_source_set_valuation valuation row(Z.of_nat skip))expression.

Definition compile_first_reached_width low high skip row context bounds expression :=
  match memory_source_endpoints row context expression,
    memory_source_endpoint_expression row context(L.Constant(Z.of_nat skip-1))expression,
    memory_source_endpoint_expression row context(L.Constant(Z.of_nat skip))expression with
  | Some(first,last),Some previous,Some selected=>
    MemoryNested.A.lower_test context bounds(first_reached_width_test low high skip first last previous selected)
  | _,_,_=>None end.

Lemma first_reached_width_math_sound expression valuation row bound low high skip first last previous selected :
  first=memory_source_affine_math(memory_source_set_valuation valuation row 0)expression ->
  last=memory_source_affine_math(memory_source_set_valuation valuation row(valuation bound-1))expression ->
  previous=memory_source_affine_math(memory_source_set_valuation valuation row(Z.of_nat skip-1))expression ->
  selected=memory_source_affine_math(memory_source_set_valuation valuation row(Z.of_nat skip))expression ->
  Z.of_nat skip+1<=valuation bound -> low<=first<=high -> low<=last<=high -> 1<=selected ->
  (match skip with O=>True|S _=>previous<=0 end) ->
  first_reached_width_fact expression valuation row bound low high skip.
Proof.
  intros FIRST LAST PREVIOUS SELECTED COUNT LOW HIGH POSITIVE EMPTY.
  subst first last previous selected.
  assert(RANGE:0<=Z.of_nat skip<valuation bound)by lia.
  unfold first_reached_width_fact; split; [exact RANGE|split].
  - intros i I; apply memory_source_affine_row_extrema with(last:=valuation bound-1); try assumption; lia.
  - split.
    + intros i I; destruct skip as [|skip]; [cbn in I; lia|].
      change(memory_source_affine_math(memory_source_set_valuation valuation row(Z.of_nat(S skip)-1))expression<=0)in EMPTY.
      rewrite memory_source_affine_row_linear in EMPTY,POSITIVE|-*.
      rewrite Nat2Z.inj_succ in EMPTY,POSITIVE,I.
      assert(SLOPE:0<memory_source_row_coefficient row expression)by nia.
      nia.
    + lia.
Qed.

Theorem compile_first_reached_width_sound low high skip row bound parameters bounds expression tree valuation
    ge locals temps memory :
  compile_first_reached_width low high skip row(bound::parameters)bounds expression=Some tree ->
  MemoryNested.A.typed_view(bound::parameters)(map valuation(bound::parameters))temps ->
  MemoryNested.A.env_within bounds(map valuation(bound::parameters)) ->
  decision_run(Entry ge locals temps memory)tree true ->
  first_reached_width_fact expression valuation row bound low high skip.
Proof.
  intros COMPILE VIEW RANGE RUN; unfold compile_first_reached_width in COMPILE.
  destruct(memory_source_endpoints row(bound::parameters)expression)as [[first last]|]eqn:ENDS; [|discriminate].
  destruct(memory_source_endpoint_expression row(bound::parameters)(L.Constant(Z.of_nat skip-1))expression)
    as [previous|]eqn:PREVIOUS; [|discriminate].
  destruct(memory_source_endpoint_expression row(bound::parameters)(L.Constant(Z.of_nat skip))expression)
    as [selected|]eqn:SELECTED; [|discriminate].
  pose proof(proj1(@MemoryNested.A.lower_test_exact
    (first_reached_width_test low high skip first last previous selected)(bound::parameters)bounds tree
    (map valuation(bound::parameters))temps ge locals memory true COMPILE RANGE VIEW)RUN)as FLAG.
  assert(TEST:L.eval_test(map valuation(bound::parameters))
    (first_reached_width_test low high skip first last previous selected)=true)by congruence.
  unfold memory_source_endpoints in ENDS.
  destruct(memory_source_endpoint_expression row(bound::parameters)(L.Constant 0)expression)as [a|]eqn:FIRST;
    [|discriminate].
  destruct(memory_source_endpoint_expression row(bound::parameters)(L.Sum(L.Var O)(L.Constant(-1)))expression)
    as [b|]eqn:LAST; [|discriminate].
  injection ENDS as A B; subst a b.
  pose proof(@memory_source_endpoint_value expression row(bound::parameters)(L.Constant 0)first valuation FIRST)as F.
  pose proof(@memory_source_endpoint_value expression row(bound::parameters)(L.Sum(L.Var O)(L.Constant(-1)))
    last valuation LAST)as LST.
  pose proof(@memory_source_endpoint_value expression row(bound::parameters)(L.Constant(Z.of_nat skip-1))
    previous valuation PREVIOUS)as P.
  pose proof(@memory_source_endpoint_value expression row(bound::parameters)(L.Constant(Z.of_nat skip))
    selected valuation SELECTED)as S.
  cbn [L.eval_expr map nth]in F,LST,P,S.
  replace(valuation bound+ -1)with(valuation bound-1)in LST by ring.
  eapply(@first_reached_width_math_sound expression valuation row bound low high skip
    (L.eval_expr(map valuation(bound::parameters))first)(L.eval_expr(map valuation(bound::parameters))last)
    (L.eval_expr(map valuation(bound::parameters))previous)(L.eval_expr(map valuation(bound::parameters))selected));
    [exact F|exact LST|exact P|exact S| | | | |].
  all: unfold first_reached_width_test in TEST; cbn [L.eval_test L.eval_expr map nth]in TEST;
    repeat rewrite andb_true_iff in TEST; repeat rewrite Z.leb_le in TEST; try tauto.
  destruct skip; cbn [L.eval_test L.eval_expr]in TEST|-*;
    repeat rewrite andb_true_iff in TEST; repeat rewrite Z.leb_le in TEST; tauto.
Qed.

Theorem first_reached_width_word_facts expression valuation row bound low high skip :
  Int.min_signed<=low -> high<=Int.max_signed ->
  first_reached_width_fact expression valuation row bound low high skip ->
  (forall i,0<=i<Z.of_nat skip ->
    Int.lt Int.zero(Int.repr(memory_source_affine_math(memory_source_set_valuation valuation row i)expression))=false) /\
  Int.lt Int.zero(Int.repr(memory_source_affine_math
    (memory_source_set_valuation valuation row(Z.of_nat skip))expression))=true.
Proof.
  intros LOW HIGH [RANGE [WIDTH [EMPTY ACTIVE]]].
  assert(SAFE:forall i,0<=i<valuation bound ->
    signed_range(memory_source_affine_math(memory_source_set_valuation valuation row i)expression)).
  { intros i I; specialize(WIDTH i I); unfold signed_range; lia. }
  split.
  - intros i I; specialize(EMPTY i I); unfold Int.lt.
    rewrite Int.signed_zero,Int.signed_repr by(apply SAFE; lia).
    destruct(zlt 0(memory_source_affine_math(memory_source_set_valuation valuation row i)expression));
      [lia|reflexivity].
  - unfold Int.lt; rewrite Int.signed_zero,Int.signed_repr by(apply SAFE; lia).
    destruct(zlt 0(memory_source_affine_math(memory_source_set_valuation valuation row(Z.of_nat skip))expression));
      [reflexivity|lia].
Qed.

Theorem compile_first_reached_width_exact low high skip row context bounds expression tree parameters
    ge locals temps memory :
  compile_first_reached_width low high skip row context bounds expression=Some tree ->
  MemoryNested.A.typed_view context parameters temps -> MemoryNested.A.env_within bounds parameters ->
  exists first last previous selected,
    memory_source_endpoints row context expression=Some(first,last) /\
    memory_source_endpoint_expression row context(L.Constant(Z.of_nat skip-1))expression=Some previous /\
    memory_source_endpoint_expression row context(L.Constant(Z.of_nat skip))expression=Some selected /\
    forall flag,decision_run(Entry ge locals temps memory)tree flag <->
      flag=L.eval_test parameters(first_reached_width_test low high skip first last previous selected).
Proof.
  intros COMPILE VIEW RANGE; unfold compile_first_reached_width in COMPILE.
  destruct(memory_source_endpoints row context expression)as [[first last]|]eqn:ENDS; [|discriminate].
  destruct(memory_source_endpoint_expression row context(L.Constant(Z.of_nat skip-1))expression)
    as [previous|]eqn:PREVIOUS; [|discriminate].
  destruct(memory_source_endpoint_expression row context(L.Constant(Z.of_nat skip))expression)
    as [selected|]eqn:SELECTED; [|discriminate].
  exists first,last,previous,selected; split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
  intro flag; eapply MemoryNested.A.lower_test_exact; eassumption.
Qed.

Print Assumptions first_reached_width_math_sound.
Print Assumptions compile_first_reached_width_sound.
Print Assumptions first_reached_width_word_facts.
Print Assumptions compile_first_reached_width_exact.
