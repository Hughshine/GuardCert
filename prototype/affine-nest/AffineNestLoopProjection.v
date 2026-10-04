From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightLoopSyntax
  ClightFrontendLoopProtocol ClightFrontendRegion ClightZeroTrip ClightNoWrap ClightFramedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops.
From GuardAffineNest Require Import AffineNestMemoryProjection.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma affine_counted_memory_map locations (physical : Z -> mem -> mem -> Prop)
  (logical : Z -> runtime_state -> runtime_state -> Prop) :
  (forall value before after, physical value before after ->
    logical value (RuntimeState locations before) (RuntimeState locations after)) ->
  forall count start before after, counted_iterations physical count start before after ->
    counted_iterations logical count start (RuntimeState locations before) (RuntimeState locations after).
Proof.
  intros POINT count start before after RUN; induction RUN; [constructor|].
  econstructor; [apply POINT; exact H|exact IHRUN].
Qed.

Lemma affine_counted_memory_map_bounded locations (physical : Z -> mem -> mem -> Prop)
  (logical : Z -> runtime_state -> runtime_state -> Prop) floor upper :
  (forall value before after, floor<=value<upper -> physical value before after ->
    logical value (RuntimeState locations before) (RuntimeState locations after)) ->
  forall count start before after, floor<=start -> upper=start+Z.of_nat count ->
    counted_iterations physical count start before after ->
    counted_iterations logical count start (RuntimeState locations before) (RuntimeState locations after).
Proof.
  intros POINT count; induction count; intros start before after FLOOR SPAN RUN;
    revert SPAN; inversion RUN; subst; intro SPAN; [constructor|].
  rewrite Nat2Z.inj_succ in SPAN; econstructor.
  - apply POINT; [lia|eassumption].
  - eapply IHcount; [lia|lia|eassumption].
Qed.

(** A structural combinator for the real source execution. The point premise
    refers to actual body executions with their actual temporary inputs. It
    will be discharged recursively, rather than assumed by the compiler. *)
Theorem affine_frontend_loop_projection fe ge locals iterator bound body protected written original
  locations code environment lower upper start finish temps memory after final :
  iterator<>bound -> normal_statement body=true -> writes_only written body ->
  ~In iterator written -> ~In bound written -> ~In iterator protected ->
  (forall identifier, In identifier protected -> ~In identifier written) ->
  signed_range start -> signed_range finish ->
  L.eval_expr environment lower=start -> L.eval_expr environment upper=finish ->
  temps!iterator=Some(Vint(Int.repr start)) -> temps!bound=Some(Vint(Int.repr finish)) ->
  temp_agree protected original temps ->
  (forall value first last,
    start<=value<finish ->
    affine_actual_body_point fe ge locals iterator body protected original value first last ->
    L.loop_semantics code (value::environment) (RuntimeState locations first) (RuntimeState locations last)) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop iterator bound body)
    E0 after final Out_normal ->
  L.loop_semantics (L.Loop lower upper code) environment
    (RuntimeState locations memory) (RuntimeState locations final).
Proof.
  intros DISTINCT NORMAL WRITES ITERATOR_FRESH BOUND_FRESH PRIVATE PROTECTED
    START FINISH LOWER UPPER ITERATOR BOUND VIEW POINT SOURCE.
  destruct (Z_lt_ge_dec start finish) as [ACTIVE|EMPTY].
  - assert (SPAN:finish=start+Z.of_nat(Z.to_nat(finish-start))).
    { rewrite Z2Nat.id by lia; lia. }
    pose proof (@affine_frontend_memory_projection fe ge locals iterator bound body protected written
      original WRITES PROTECTED PRIVATE DISTINCT NORMAL ITERATOR_FRESH BOUND_FRESH
      finish (Z.to_nat(finish-start)) start temps memory after final FINISH SPAN START
      ITERATOR BOUND VIEW SOURCE) as RUN.
    apply L.LLoop; rewrite LOWER,UPPER.
    apply(proj2(@memory_range_iterations (Z.to_nat(finish-start)) _ start finish _ _ SPAN)).
    eapply affine_counted_memory_map_bounded; [exact POINT|lia|exact SPAN|exact RUN].
  - pose proof (@counter_condition_at ge locals temps memory iterator bound start finish
      DISTINCT ITERATOR BOUND START FINISH) as TEST.
    assert (FALSE:(start <? finish)=false) by (apply Z.ltb_ge; lia).
    rewrite FALSE in TEST.
    destruct (frontend_zero_trip_result SOURCE TEST) as [TEMPS MEMORY]; subst final.
    apply L.LLoop; rewrite LOWER,UPPER,Zrange_empty by lia; constructor.
Qed.
Print Assumptions affine_counted_memory_map.
Print Assumptions affine_frontend_loop_projection.
