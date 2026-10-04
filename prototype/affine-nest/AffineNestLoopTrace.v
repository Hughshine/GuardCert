From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightLoopSyntax ClightFramedLoop
  ClightTempFrame ClightZeroTrip.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Unlike a constant rectangular exit assignment, a child may recompute
    bounds from its parent's current coordinate. Keep the actual temporary
    states through each iteration until their public exit is reconstructed. *)
Section TRACE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable iterator bound : ident.
Variable body : statement.

Inductive affine_frontend_trace : nat -> Z -> temp_env -> mem -> temp_env -> mem -> Prop :=
| affine_trace_zero : forall x temps memory,
    affine_frontend_trace O x temps memory temps memory
| affine_trace_step : forall count x temps memory middle next_memory after final_memory,
    exec_stmt fe ge locals temps memory body E0 middle next_memory Out_normal ->
    affine_frontend_trace count (x+1)
      (PTree.set iterator (Vint (Int.repr (x+1))) middle) next_memory after final_memory ->
    affine_frontend_trace (S count) x temps memory after final_memory.

Hypothesis DISTINCT : iterator <> bound.
Hypothesis NORMAL : normal_statement body=true.
Hypothesis FRAME : forall before memory trace after final_memory,
  exec_stmt fe ge locals before memory body trace after final_memory Out_normal ->
  temp_agree [iterator;bound] before after.

Lemma affine_trace_body_frame before memory trace after final_memory :
  exec_stmt fe ge locals before memory body trace after final_memory Out_normal ->
  trace=E0 -> temp_agree [iterator;bound] before after.
Proof. intros RUN EMPTY; subst; eapply FRAME; exact RUN. Qed.

Theorem affine_frontend_trace_decode upper : signed_range upper ->
  forall count x temps memory after final_memory,
  upper=x+Z.of_nat count -> signed_range x ->
  temps!iterator=Some(Vint(Int.repr x)) -> temps!bound=Some(Vint(Int.repr upper)) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body)
    E0 after final_memory Out_normal ->
  affine_frontend_trace count x temps memory after final_memory.
Proof.
  intro UPPER; induction count as [|count IH];
    intros x temps memory after final_memory SPAN RANGE ITERATOR BOUND RUN.
  - cbn in SPAN; assert (SAME:upper=x) by lia; clear SPAN; subst upper.
    pose proof (@counter_condition_at ge locals temps memory iterator bound x x
      DISTINCT ITERATOR BOUND RANGE UPPER) as TEST.
    rewrite Z.ltb_irrefl in TEST.
    destruct (frontend_zero_trip_result RUN TEST) as [TEMPS MEMORY]; subst; constructor.
  - assert (ACTIVE:x<upper) by (rewrite Nat2Z.inj_succ in SPAN; lia).
    pose proof (@counter_condition_at ge locals temps memory iterator bound x upper
      DISTINCT ITERATOR BOUND RANGE UPPER) as TEST.
    assert (TRUE:(x <? upper)=true) by (apply Z.ltb_lt; exact ACTIVE); rewrite TRUE in TEST.
    destruct (frontend_iteration_decode TEST
      (@normal_statement_execution fe ge locals body NORMAL)
      FRAME RUN) as [middle [next_memory [BODY REST]]].
    pose proof (@FRAME _ _ _ _ _ BODY) as PRESERVED.
    assert (MID_ITERATOR:middle!iterator=Some(Vint(Int.repr x))).
    { rewrite (PRESERVED iterator (or_introl eq_refl)); exact ITERATOR. }
    rewrite (@counter_increment_small iterator middle x MID_ITERATOR) in REST.
    econstructor; [exact BODY|].
    eapply IH; [rewrite Nat2Z.inj_succ in SPAN; lia|unfold signed_range in *; lia|apply PTree.gss| |exact REST].
    rewrite PTree.gso by congruence.
    rewrite (PRESERVED bound (or_intror (or_introl eq_refl))); exact BOUND.
Qed.

Theorem affine_frontend_trace_encode upper : signed_range upper ->
  forall count x temps memory after final_memory,
  affine_frontend_trace count x temps memory after final_memory ->
  upper=x+Z.of_nat count -> signed_range x ->
  temps!iterator=Some(Vint(Int.repr x)) -> temps!bound=Some(Vint(Int.repr upper)) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body)
    E0 after final_memory Out_normal.
Proof.
  intros UPPER count x temps memory after final_memory TRACE; induction TRACE;
    intros SPAN RANGE ITERATOR BOUND.
  - cbn in SPAN; assert (SAME:upper=x) by lia; clear SPAN; subst upper.
    apply frontend_zero_trip_encode.
    pose proof (@counter_condition_at ge locals temps memory iterator bound x x
      DISTINCT ITERATOR BOUND RANGE UPPER) as TEST.
    rewrite Z.ltb_irrefl in TEST; exact TEST.
  - assert (ACTIVE:x<upper) by (rewrite Nat2Z.inj_succ in SPAN; lia).
    pose proof (@counter_condition_at ge locals temps memory iterator bound x upper
      DISTINCT ITERATOR BOUND RANGE UPPER) as TEST.
    assert (TRUE:(x <? upper)=true) by (apply Z.ltb_lt; exact ACTIVE); rewrite TRUE in TEST.
    pose proof (@FRAME _ _ _ _ _ H) as PRESERVED.
    assert (MID_ITERATOR:middle!iterator=Some(Vint(Int.repr x))).
    { rewrite (PRESERVED iterator (or_introl eq_refl)); exact ITERATOR. }
    assert (MID_BOUND:middle!bound=Some(Vint(Int.repr upper))).
    { rewrite (PRESERVED bound (or_intror (or_introl eq_refl))); exact BOUND. }
    eapply frontend_iteration_encode; [exact TEST| |exact H|].
    + exists (Int.repr x),(Int.repr upper); repeat split; try assumption.
      rewrite !Int.signed_repr by assumption; exact ACTIVE.
    + rewrite (@counter_increment_small iterator middle x MID_ITERATOR).
      apply IHTRACE; [rewrite Nat2Z.inj_succ in SPAN; lia|unfold signed_range in *; lia|apply PTree.gss|].
      rewrite PTree.gso by congruence; exact MID_BOUND.
Qed.

Theorem affine_frontend_trace_last count x temps memory after final_memory upper :
  affine_frontend_trace (S count) x temps memory after final_memory ->
  upper=x+Z.of_nat(S count) ->
  temps!iterator=Some(Vint(Int.repr x)) -> temps!bound=Some(Vint(Int.repr upper)) ->
  exists last_temps last_memory last_after,
    last_temps!iterator=Some(Vint(Int.repr(upper-1))) /\
    last_temps!bound=Some(Vint(Int.repr upper)) /\
    exec_stmt fe ge locals last_temps last_memory body E0 last_after final_memory Out_normal /\
    after=PTree.set iterator (Vint(Int.repr upper)) last_after.
Proof.
  revert x temps memory after final_memory upper.
  induction count as [|count IH]; intros x temps memory after final_memory upper TRACE SPAN ITERATOR BOUND.
  - revert SPAN; inversion TRACE; subst.
    match goal with TAIL:affine_frontend_trace O _ _ _ _ _ |- _ => inversion TAIL; subst end.
    intro SPAN.
    assert (UPPER:upper=x+1) by (cbn in SPAN; lia).
    exists temps,memory,middle; repeat split; try assumption.
    + replace (upper-1) with x by lia; exact ITERATOR.
    + rewrite UPPER; reflexivity.
  - revert SPAN; inversion TRACE; subst; intro SPAN.
    match goal with BODY:exec_stmt _ _ _ _ _ body _ ?middle _ Out_normal |- _ =>
      pose proof (@FRAME _ _ _ _ _ BODY) as PRESERVED end.
    eapply IH; [eassumption|rewrite Nat2Z.inj_succ in SPAN; lia|apply PTree.gss|].
    rewrite PTree.gso by congruence.
    rewrite (PRESERVED bound (or_intror (or_introl eq_refl))); exact BOUND.
Qed.
End TRACE.
Print Assumptions affine_frontend_trace_decode.
Print Assumptions affine_frontend_trace_encode.
Print Assumptions affine_frontend_trace_last.
