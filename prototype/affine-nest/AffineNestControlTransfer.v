From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightLoopSyntax
  ClightFramedLoop ClightTempFrame ClightNoWrap ClightZeroTrip.
From GuardAffineNest Require Import AffineNestLoopTrace.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section TRANSFER.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable iterator bound : ident.
Variable body shadow_body : statement.
Hypothesis DISTINCT : iterator<>bound.
Hypothesis NORMAL : normal_statement body=true.
Hypothesis FRAME : forall before memory trace after final_memory,
  exec_stmt fe ge locals before memory body trace after final_memory Out_normal ->
  temp_agree [iterator;bound] before after.
Hypothesis SHADOW : forall before memory after final_memory,
  exec_stmt fe ge locals before memory body E0 after final_memory Out_normal ->
  forall shadow_memory,
  exec_stmt fe ge locals before shadow_memory shadow_body E0 after shadow_memory Out_normal.

Lemma affine_trace_shadow_execution count x temps memory after final_memory :
  affine_frontend_trace fe ge locals iterator body count x temps memory after final_memory ->
  forall upper, signed_range upper -> upper=x+Z.of_nat count -> signed_range x ->
  temps!iterator=Some(Vint(Int.repr x)) -> temps!bound=Some(Vint(Int.repr upper)) ->
  forall shadow_memory,
  exec_stmt fe ge locals temps shadow_memory (frontend_counted_loop iterator bound shadow_body)
    E0 after shadow_memory Out_normal.
Proof.
  intro TRACE; induction TRACE; intros upper UPPER SPAN RANGE ITERATOR BOUND shadow_memory.
  - cbn in SPAN; assert (SAME:upper=x) by lia; clear SPAN; subst upper.
    apply frontend_zero_trip_encode.
    pose proof (@counter_condition_at ge locals temps shadow_memory iterator bound x x
      DISTINCT ITERATOR BOUND RANGE UPPER) as TEST.
    rewrite Z.ltb_irrefl in TEST; exact TEST.
  - assert (ACTIVE:x<upper) by (rewrite Nat2Z.inj_succ in SPAN; lia).
    pose proof (@counter_condition_at ge locals temps shadow_memory iterator bound x upper
      DISTINCT ITERATOR BOUND RANGE UPPER) as TEST.
    assert (TRUE:(x <? upper)=true) by (apply Z.ltb_lt; exact ACTIVE); rewrite TRUE in TEST.
    pose proof (@FRAME _ _ _ _ _ H) as PRESERVED.
    assert (MID_ITERATOR:middle!iterator=Some(Vint(Int.repr x))).
    { rewrite (PRESERVED iterator (or_introl eq_refl)); exact ITERATOR. }
    assert (MID_BOUND:middle!bound=Some(Vint(Int.repr upper))).
    { rewrite (PRESERVED bound (or_intror (or_introl eq_refl))); exact BOUND. }
    eapply frontend_iteration_encode; [exact TEST| |eapply SHADOW; exact H|].
    + exists (Int.repr x),(Int.repr upper); repeat split; try assumption.
      rewrite !Int.signed_repr by assumption; exact ACTIVE.
    + rewrite (@counter_increment_small iterator middle x MID_ITERATOR).
      eapply IHTRACE; [exact UPPER|rewrite Nat2Z.inj_succ in SPAN; lia|unfold signed_range in *; lia|apply PTree.gss|].
      rewrite PTree.gso by congruence; exact MID_BOUND.
Qed.

Theorem affine_frontend_control_transfer temps memory after final_memory :
  exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body)
    E0 after final_memory Out_normal ->
  forall shadow_memory,
  exec_stmt fe ge locals temps shadow_memory (frontend_counted_loop iterator bound shadow_body)
    E0 after shadow_memory Out_normal.
Proof.
  intros SOURCE shadow_memory.
  destruct (frontend_entry_test SOURCE) as [flag TEST].
  destruct (counter_test_domain TEST) as [word [upper_word [ITERATOR BOUND]]].
  cbn [entry_temps] in ITERATOR,BOUND.
  set (x:=Int.signed word); set (upper:=Int.signed upper_word).
  assert (X:signed_range x) by (unfold x,signed_range; pose proof(Int.signed_range word); lia).
  assert (U:signed_range upper) by (unfold upper,signed_range; pose proof(Int.signed_range upper_word); lia).
  assert (I:temps!iterator=Some(Vint(Int.repr x))) by (unfold x; rewrite Int.repr_signed; exact ITERATOR).
  assert (B:temps!bound=Some(Vint(Int.repr upper))) by (unfold upper; rewrite Int.repr_signed; exact BOUND).
  destruct (Z_lt_ge_dec x upper) as [ACTIVE|EMPTY].
  - set (count:=Z.to_nat(upper-x)).
    assert (SPAN:upper=x+Z.of_nat count) by (unfold count; rewrite Z2Nat.id by lia; lia).
    pose proof (@affine_frontend_trace_decode fe ge locals iterator bound body DISTINCT NORMAL FRAME
      upper U count x temps memory after final_memory SPAN X I B SOURCE) as TRACE.
    eapply affine_trace_shadow_execution; eassumption.
  - pose proof (@counter_condition_at ge locals temps memory iterator bound x upper DISTINCT I B X U) as TEST_SOURCE.
    pose proof (@counter_condition_at ge locals temps shadow_memory iterator bound x upper DISTINCT I B X U) as TEST_SHADOW.
    assert (FALSE:(x <? upper)=false) by (apply Z.ltb_ge; lia).
    rewrite FALSE in TEST_SOURCE,TEST_SHADOW.
    destruct (frontend_zero_trip_result SOURCE TEST_SOURCE) as [TEMPS MEMORY]; subst.
    apply frontend_zero_trip_encode; exact TEST_SHADOW.
Qed.
End TRANSFER.
Print Assumptions affine_trace_shadow_execution.
Print Assumptions affine_frontend_control_transfer.
