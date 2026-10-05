From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightSameAddress
  ClightCountedLoop ClightCountedProtocol ClightLoopExecution ClightStraightLine ClightTempFrame ClightLoopSyntax ClightRegionProgress.
From GuardInterface Require Import ClightStrictLoopProgress ClightStrictIteration ClightIndexedLoadBody
  ClightIndexedBoundSyntax ClightQuietDeterminacy ClightStableLoadBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma indexed_bound_body_writes out iterator body :
  flatten_region body = [indexed_bound_body out iterator] -> writes_only [] body.
Proof. intro FLAT; apply flatten_writes_certificate; rewrite FLAT; repeat constructor. Qed.
Lemma indexed_bound_body_normal out iterator body :
  flatten_region body = [indexed_bound_body out iterator] -> normal_statement body = true.
Proof. intro FLAT; apply flatten_normal_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. Qed.
Lemma indexed_bound_body_quiet out iterator body :
  flatten_region body = [indexed_bound_body out iterator] -> quiet_statement body = true.
Proof. intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. Qed.

(** This step is extracted from the actual source execution. No stability
    premise is used to obtain its store permission or its remaining execution. *)
Theorem indexed_bound_source_step fe ge locals iterator bound out body le memory after final point upper q qofs :
  flatten_region body = [indexed_bound_body out iterator] ->
  0 <= point < Int.signed upper ->
  le ! iterator = Some (Vint (Int.repr point)) -> le ! bound = Some (Vptr q qofs) ->
  Mem.loadv Mint32 memory (Vptr q qofs) = Some (Vint upper) ->
  exec_stmt fe ge locals le memory (indexed_bound_loop iterator bound body) E0 after final Out_normal ->
  exists block base value next_memory,
    le ! out = Some (Vptr block base) /\
    Mem.storev Mint32 memory (Vptr block (indexed_word_offset base (Int.repr point))) value = Some next_memory /\
    exec_stmt fe ge locals (PTree.set iterator (Vint (Int.repr (point+1))) le) next_memory
      (indexed_bound_loop iterator bound body) E0 after final Out_normal.
Proof.
  intros FLAT RANGE ITER BOUND READ SOURCE.
  assert (POINT_RANGE : signed_range point) by
    (pose proof (Int.signed_range upper); unfold signed_range; change Int.min_signed with (-2147483648); lia).
  assert (LT : Int.lt (Int.repr point) upper = true).
  { unfold Int.lt; rewrite Int.signed_repr by exact POINT_RANGE;
      destruct (zlt point (Int.signed upper)); [reflexivity|lia]. }
  assert (ACTIVE : expression_test (indexed_bound_test iterator bound) (Entry ge locals le memory) true).
  { rewrite <- LT; eapply indexed_bound_test_eval; eassumption. }
  destruct (@strict_active_iteration fe ge locals iterator (indexed_bound_test iterator bound) body
    le memory after final (@indexed_bound_body_normal out iterator body FLAT)
    (@indexed_bound_body_quiet out iterator body FLAT) ACTIVE SOURCE)
    as [body_temps [next_memory [next_temps [increment_memory [BODY [INC TAIL]]]]]].
  pose proof (memory_body_temporaries_exact (@indexed_bound_body_writes out iterator body FLAT) BODY) as TEMPS;
    subst body_temps.
  destruct (@strict_increment_execution_exact fe ge locals iterator le next_memory E0 next_temps increment_memory Out_normal
    (@indexed_bound_test_strict ge locals le memory iterator bound ACTIVE) INC)
    as [_ [NEXT [MEMORY _]]]; subst next_temps increment_memory.
  apply (flattened_singleton_execution FLAT) in BODY.
  destruct (indexed_bound_body_store ITER BODY) as [block [base [value [OUT STORE]]]].
  exists block, base, value, next_memory; split; [exact OUT|split; [exact STORE|]].
  unfold increment_temps in TAIL; rewrite ITER in TAIL.
  rewrite Int.add_signed, Int.signed_repr in TAIL by exact POINT_RANGE.
  change (Int.signed Int.one) with 1 in TAIL; exact TAIL.
Qed.
Print Assumptions indexed_bound_source_step.
