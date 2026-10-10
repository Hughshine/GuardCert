From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightPureExpr ClightLoopSyntax
  ClightRegionProgress ClightFragmentProgress ClightSequenceProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl
  GuardMemoryLongLoopControl GuardMemoryLongLoopSettle GuardMemoryLongHeaderLicense
  GuardMemoryLongRawLoadedProgress GuardMemoryObservationDeterminism.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The interval uses actual signed source values, including nonzero starts
    and empty intervals. Expression evaluation and no-wrap/model obligations
    remain separate: this interface does not replace an I64 result by an
    unchecked mathematical affine expression. *)
Definition memory_long_range_count lower upper := Z.to_nat (upper-lower).
Lemma memory_long_range_end lower upper :
  lower+Z.of_nat (memory_long_range_count lower upper)=Z.max lower upper.
Proof.
  unfold memory_long_range_count; destruct (Z_le_dec lower upper).
  - rewrite Z2Nat.id by lia; rewrite Z.max_r by lia; lia.
  - rewrite Z.max_l by lia; destruct (upper-lower) eqn:DIFFERENCE; cbn; lia.
Qed.
Lemma memory_long_range_test lower upper value :
  lower<=value<=Z.max lower upper ->
  (value <? Z.max lower upper)=(value <? upper).
Proof.
  intro RANGE; destruct (Z_le_dec lower upper).
  - rewrite Z.max_r by lia; reflexivity.
  - rewrite Z.max_l in * by lia.
    assert (SAME : value=lower) by lia; subst value.
    rewrite Z.ltb_irrefl,(proj2 (Z.ltb_ge lower upper) ltac:(lia)); reflexivity.
Qed.

Definition memory_long_from_loop iterator initial condition body :=
  Ssequence (Sset iterator initial) (memory_long_frontend_loop iterator condition body).
Definition long_raw_from_loop iterator initial bound body :=
  Ssequence (Ssequence Sskip (Sset iterator initial)) (long_raw_loaded_loop iterator bound body).

Lemma memory_long_from_loop_decode fe ge locals temps memory iterator initial condition body
  lower after final :
  eval_expr ge locals temps memory initial (Vlong (Int64.repr lower)) ->
  exec_stmt fe ge locals temps memory (memory_long_from_loop iterator initial condition body)
    E0 after final Out_normal ->
  exec_stmt fe ge locals (PTree.set iterator (Vlong (Int64.repr lower)) temps) memory
    (memory_long_frontend_loop iterator condition body) E0 after final Out_normal.
Proof.
  intros EXPECTED RUN; unfold memory_long_from_loop in RUN.
  destruct (sequence_normal_decode RUN) as [middle [mem [INIT LOOP]]].
  inversion INIT; subst.
  match goal with EVAL : eval_expr _ _ _ _ initial ?actual |- _ =>
    pose proof (memory_expression_unique EVAL EXPECTED) as SAME; subst actual
  end.
  exact LOOP.
Qed.

Section RANGE_SOURCE.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable iterator : ident.
Variables initial condition : expr.
Variable body : statement.
Variables lower upper : Z.
Variable invariant : temp_env -> mem -> Prop.
Variable physical : Z -> mem -> mem -> Prop.
Variable settle : Z -> temp_env -> temp_env.
Hypothesis INITIAL : forall temps memory, invariant temps memory ->
  eval_expr ge locals temps memory initial (Vlong (Int64.repr lower)).
Hypothesis HEADER : forall temps memory value, invariant temps memory ->
  lower<=value<=Z.max lower upper -> temps ! iterator=Some (Vlong (Int64.repr value)) ->
  expression_test condition (Entry ge locals temps memory) (value <? upper).
Hypothesis NORMAL : forall le m tr le' m' out,
  exec_stmt fe ge locals le m body tr le' m' out -> out=Out_normal.
Hypothesis FRAME : forall le m tr le' m',
  exec_stmt fe ge locals le m body tr le' m' Out_normal -> le' ! iterator=le ! iterator.
Hypothesis BRIDGE : forall value temps memory after final,
  lower<=value<upper -> invariant temps memory -> temps ! iterator=Some (Vlong (Int64.repr value)) ->
  (exec_stmt fe ge locals temps memory body E0 after final Out_normal <->
   physical value memory final /\ after=settle value temps).
Hypothesis BODY_INV : forall value temps memory after final,
  lower<=value<upper -> invariant temps memory -> temps ! iterator=Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal -> invariant after final.
Hypothesis SET_INV : forall temps memory value, invariant temps memory ->
  invariant (PTree.set iterator (Vlong (Int64.repr value)) temps) memory.

Lemma memory_long_range_header temps memory value :
  invariant temps memory -> lower<=value<=Z.max lower upper ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  expression_test condition (Entry ge locals temps memory) (value <? Z.max lower upper).
Proof. intros INV RANGE VALUE; rewrite memory_long_range_test by exact RANGE; apply HEADER; assumption. Qed.
Lemma memory_long_range_active value : lower<=value<Z.max lower upper -> lower<=value<upper.
Proof. destruct (Z_le_dec lower upper); rewrite ?Z.max_r,?Z.max_l by lia; lia. Qed.

Theorem memory_long_from_range_equivalence temps memory after final :
  invariant temps memory ->
  (exec_stmt fe ge locals temps memory (memory_long_from_loop iterator initial condition body)
     E0 after final Out_normal <->
   counted_iterations physical (memory_long_range_count lower upper) lower memory final /\
   after=memory_long_settled_exit iterator settle (memory_long_range_count lower upper) lower
     (PTree.set iterator (Vlong (Int64.repr lower)) temps)).
Proof.
  intro INV.
  assert (ACTIVE_BRIDGE : forall value temps memory after final,
    lower<=value<Z.max lower upper -> invariant temps memory ->
    temps ! iterator=Some (Vlong (Int64.repr value)) ->
    (exec_stmt fe ge locals temps memory body E0 after final Out_normal <->
     physical value memory final /\ after=settle value temps)).
  { intros; apply BRIDGE; [apply memory_long_range_active; assumption|assumption|assumption]. }
  assert (ACTIVE_INV : forall value temps memory after final,
    lower<=value<Z.max lower upper -> invariant temps memory ->
    temps ! iterator=Some (Vlong (Int64.repr value)) ->
    exec_stmt fe ge locals temps memory body E0 after final Out_normal -> invariant after final).
  { intros; eapply BODY_INV; [apply memory_long_range_active; eassumption|eassumption|eassumption|eassumption]. }
  split.
  - intro RUN; apply memory_long_from_loop_decode with (lower:=lower) in RUN; [|apply INITIAL; exact INV].
    eapply (@memory_long_settled_decode fe ge locals iterator condition body (Z.max lower upper) lower
      invariant physical settle memory_long_range_header NORMAL FRAME ACTIVE_BRIDGE ACTIVE_INV SET_INV).
    + symmetry; apply memory_long_range_end.
    + lia.
    + apply SET_INV; exact INV.
    + apply PTree.gss.
    + exact RUN.
  - intros [ITER EXIT]; subst after; unfold memory_long_from_loop.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [apply exec_Sset; apply INITIAL; exact INV|].
    eapply (@memory_long_settled_encode fe ge locals iterator condition body (Z.max lower upper) lower
      invariant physical settle memory_long_range_header FRAME ACTIVE_BRIDGE ACTIVE_INV SET_INV).
    + symmetry; apply memory_long_range_end.
    + lia.
    + apply SET_INV; exact INV.
    + apply PTree.gss.
    + exact ITER.
Qed.
End RANGE_SOURCE.

(** Strict source control cannot wrap after a true comparison. Reuse the
    existing progress protocol for any initializer, independently of a guard
    accepting or an affine interpretation of the bound. *)
Definition long_raw_from_framed_progress iterator initial bound
  (BOUND_TYPE : typeof bound=memory_long_type) protected
  (FRESH : ~ In iterator protected) body (F : framed_progress body (iterator::protected)) :
  framed_progress (long_raw_from_loop iterator initial bound body) protected.
Proof.
  apply sequence_framed_progress.
  - apply finite_framed_progress; cbn [frame_statement].
    destruct (in_dec peq iterator protected); [contradiction|reflexivity].
  - apply long_raw_loaded_framed_progress; assumption.
Defined.
Definition long_raw_from_region_progress iterator initial bound
  (BOUND_TYPE : typeof bound=memory_long_type) protected
  (FRESH : ~ In iterator protected) body (F : framed_progress body (iterator::protected)) :
  region_progress (long_raw_from_loop iterator initial bound body).
Proof.
  apply sequence_region_progress with (protected:=protected).
  - apply finite_framed_progress; cbn [frame_statement].
    destruct (in_dec peq iterator protected); [contradiction|reflexivity].
  - apply long_raw_loaded_framed_progress; assumption.
Defined.

Print Assumptions memory_long_range_end.
Print Assumptions memory_long_range_test.
Print Assumptions memory_long_from_loop_decode.
Print Assumptions memory_long_from_range_equivalence.
Print Assumptions long_raw_from_framed_progress.
Print Assumptions long_raw_from_region_progress.
