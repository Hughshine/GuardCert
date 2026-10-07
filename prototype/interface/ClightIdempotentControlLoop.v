From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightLoopExecution ClightTempFrame ClightFramedLoop ClightNoWrap.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Pure control bodies can settle private/public temporaries on every
    iteration. These laws justify one settlement at the final counter; they
    are not a license to omit memory effects of an arbitrary loop body. *)
Definition filled_control_exit iterator upper (settle:temp_env->temp_env) count temps :=
  match count with
  | O=>temps
  | S _=>PTree.set iterator(Vint(Int.repr upper))(settle temps) end.

Section LOOP.
Variable fe : genv->function->list val->mem->env->temp_env->mem->Prop.
Variable ge : genv.
Variable locals : env.
Variables iterator bound : ident.
Variable body : statement.
Variable settle : temp_env->temp_env.
Variable invariant : temp_env->Prop.
Hypothesis DISTINCT : iterator<>bound.
Hypothesis BODY : forall temps memory,invariant temps ->
  exec_stmt fe ge locals temps memory body E0(settle temps) memory Out_normal.
Hypothesis FRAME : forall temps,(settle temps)!iterator=temps!iterator /\ (settle temps)!bound=temps!bound.
Hypothesis IDEMPOTENT : forall temps,settle(settle temps)=settle temps.
Hypothesis COMMUTE : forall temps word,settle(PTree.set iterator(Vint word)temps)=
  PTree.set iterator(Vint word)(settle temps).
Hypothesis SETTLED : forall temps,invariant temps -> invariant(settle temps).
Hypothesis INCREMENT : forall temps word,invariant temps -> invariant(PTree.set iterator(Vint word)temps).

Theorem frontend_idempotent_control_execution count x upper temps memory :
  upper=x+Z.of_nat count -> signed_range x -> signed_range upper -> invariant temps ->
  temps!iterator=Some(Vint(Int.repr x)) -> temps!bound=Some(Vint(Int.repr upper)) ->
  exec_stmt fe ge locals temps memory(frontend_counted_loop iterator bound body)
    E0(filled_control_exit iterator upper settle count temps) memory Out_normal.
Proof.
  revert x upper temps memory; induction count as [|count IH];
    intros x upper temps memory LENGTH RANGE UPPER INV ITER BOUND.
  - cbn in LENGTH; assert(SAME:upper=x) by lia; clear LENGTH; subst upper.
    cbn [filled_control_exit]; apply frontend_zero_trip_encode.
    pose proof(@counter_condition_at ge locals temps memory iterator bound x x DISTINCT ITER BOUND RANGE UPPER) as TEST.
    rewrite Z.ltb_irrefl in TEST; exact TEST.
  - assert(ACTIVE:x<upper) by(rewrite Nat2Z.inj_succ in LENGTH; lia).
    pose proof(@counter_condition_at ge locals temps memory iterator bound x upper DISTINCT ITER BOUND RANGE UPPER) as TEST.
    assert(TRUE:(x<?upper)=true) by(apply Z.ltb_lt; exact ACTIVE); rewrite TRUE in TEST.
    destruct(FRAME temps) as [KEEP_ITER KEEP_BOUND].
    set(next:=PTree.set iterator(Vint(Int.repr(x+1)))(settle temps)).
    assert(REST:exec_stmt fe ge locals next memory(frontend_counted_loop iterator bound body)
      E0(filled_control_exit iterator upper settle count next) memory Out_normal).
    { apply IH with(x:=x+1).
      - rewrite Nat2Z.inj_succ in LENGTH; lia.
      - unfold signed_range in *; lia.
      - exact UPPER.
      - apply INCREMENT,SETTLED; exact INV.
      - apply PTree.gss.
      - unfold next; rewrite PTree.gso by congruence; rewrite KEEP_BOUND; exact BOUND. }
    assert(EXIT:filled_control_exit iterator upper settle count next=
      filled_control_exit iterator upper settle(S count)temps).
    { destruct count as [|count].
      - cbn [filled_control_exit]; unfold next.
        replace upper with(x+1) by(cbn in LENGTH; lia); reflexivity.
      - cbn [filled_control_exit]; unfold next; rewrite COMMUTE,IDEMPOTENT,PTree.set2; reflexivity. }
    rewrite EXIT in REST.
    eapply frontend_iteration_encode; [exact TEST| |exact(@BODY temps memory INV)|].
    + exists(Int.repr x),(Int.repr upper); split; [rewrite KEEP_ITER; exact ITER|].
      split; [rewrite KEEP_BOUND; exact BOUND|].
      rewrite !Int.signed_repr by assumption; exact ACTIVE.
    + rewrite(@counter_increment_small iterator(settle temps)x ltac:(rewrite KEEP_ITER; exact ITER)).
      exact REST.
Qed.
End LOOP.

Print Assumptions frontend_idempotent_control_execution.
