From Stdlib Require Import Bool List.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightRegionProgress.
From GuardInterface Require Import GuardInterface ClightReadonlyRewrite.
Set Implicit Arguments.

Lemma deref_location_determinate ty memory block offset field first second :
  deref_loc ty memory block offset field first ->
  deref_loc ty memory block offset field second -> first = second.
Proof.
  intros FIRST SECOND; inversion FIRST; inversion SECOND; subst; try congruence.
  match goal with SAME : Bits _ _ _ _ = Bits _ _ _ _ |- _ => inversion SAME; subst end.
  match goal with A : load_bitfield _ _ _ _ _ _ _ _, B : load_bitfield _ _ _ _ _ _ _ _ |- _ =>
    inversion A; inversion B; subst end; congruence.
Qed.

Ltac eliminate_impossible_lvalue :=
  repeat match goal with
  | H : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion H
  | H : eval_lvalue _ _ _ _ (Econst_float _ _) _ _ _ |- _ => inversion H
  | H : eval_lvalue _ _ _ _ (Econst_single _ _) _ _ _ |- _ => inversion H
  | H : eval_lvalue _ _ _ _ (Econst_long _ _) _ _ _ |- _ => inversion H
  | H : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H
  | H : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion H
  | H : eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _ |- _ => inversion H
  | H : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H
  | H : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion H
  | H : eval_lvalue _ _ _ _ (Esizeof _ _) _ _ _ |- _ => inversion H
  | H : eval_lvalue _ _ _ _ (Ealignof _ _) _ _ _ |- _ => inversion H
  end.

Ltac align_expression_values :=
  repeat match goal with
  | IH : forall v, eval_expr ?ge ?e ?le ?m ?a v -> _,
    RUN : eval_expr ?ge ?e ?le ?m ?a ?other |- _ =>
      let SAME := fresh "VALUE" in pose proof (IH _ RUN) as SAME; clear IH; inversion SAME; subst
  | IH : forall b ofs bf, eval_lvalue ?ge ?e ?le ?m ?a b ofs bf -> _,
    RUN : eval_lvalue ?ge ?e ?le ?m ?a ?other_b ?other_ofs ?other_bf |- _ =>
      let SAME := fresh "ADDRESS" in pose proof (IH _ _ _ RUN) as SAME; clear IH;
      destruct SAME as [? [? ?]]; subst
  end.

Theorem expressions_determinate ge e le memory :
  (forall a value, eval_expr ge e le memory a value -> forall other,
    eval_expr ge e le memory a other -> value = other) /\
  (forall a block offset field, eval_lvalue ge e le memory a block offset field ->
    forall other_block other_offset other_field,
    eval_lvalue ge e le memory a other_block other_offset other_field ->
    block = other_block /\ offset = other_offset /\ field = other_field).
Proof.
  apply eval_expr_lvalue_ind; intros.
  all: match goal with
  | |- _ = ?other => match goal with RUN : eval_expr _ _ _ _ _ other |- _ => inversion RUN; subst end
  | |- _ = ?other_b /\ _ = ?other_ofs /\ _ = ?other_bf =>
      match goal with RUN : eval_lvalue _ _ _ _ _ other_b other_ofs other_bf |- _ => inversion RUN; subst end
  end.
  all: eliminate_impossible_lvalue; align_expression_values; try congruence; try (repeat split; congruence).
  - eapply deref_location_determinate; eassumption.
Qed.

Lemma assign_location_determinate ce ty memory block offset field value first second :
  assign_loc ce ty memory block offset field value first ->
  assign_loc ce ty memory block offset field value second -> first = second.
Proof.
  intros FIRST SECOND; inversion FIRST; inversion SECOND; subst; try congruence.
  match goal with SAME : Bits _ _ _ _ = Bits _ _ _ _ |- _ => inversion SAME; subst end.
  match goal with A : store_bitfield _ _ _ _ _ _ _ _ _ _, B : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ =>
    inversion A; inversion B; subst end; congruence.
Qed.

Ltac align_evaluations :=
  repeat match goal with
  | FIRST : eval_expr ?ge ?e ?le ?m ?a ?value,
    SECOND : eval_expr ?ge ?e ?le ?m ?a ?other |- _ =>
      let SAME := fresh "VALUE" in
      pose proof ((proj1 (expressions_determinate ge e le m)) _ _ FIRST _ SECOND) as SAME;
      clear SECOND; inversion SAME; subst
  | FIRST : eval_lvalue ?ge ?e ?le ?m ?a ?b ?ofs ?bf,
    SECOND : eval_lvalue ?ge ?e ?le ?m ?a ?other_b ?other_ofs ?other_bf |- _ =>
      let SAME := fresh "ADDRESS" in
      pose proof ((proj2 (expressions_determinate ge e le m)) _ _ _ _ FIRST _ _ _ SECOND) as SAME;
      clear SECOND; destruct SAME as [? [? ?]]; subst
  end.

Ltac align_statement_runs :=
  repeat match goal with
  | IH : quiet_statement ?body = true -> forall tr le' m' out,
      exec_stmt ?fe ?ge ?e ?le ?m ?body tr le' m' out -> _,
    RUN : exec_stmt ?fe ?ge ?e ?le ?m ?body ?tr ?le' ?m' ?out |- _ =>
      let SAFE := fresh "QUIET" in
      assert (SAFE : quiet_statement body = true) by
        (first [assumption|cbn [quiet_statement]; apply andb_true_iff; split; assumption]);
      let SAME := fresh "EXIT" in pose proof (IH SAFE _ _ _ _ RUN) as SAME;
      lazymatch type of SAME with
      | ?t1 = ?t2 /\ ?l1 = ?l2 /\ ?m1 = ?m2 /\ ?o1 = ?o2 =>
          tryif (constr_eq t1 t2; constr_eq l1 l2; constr_eq m1 m2; constr_eq o1 o2)
          then fail 1 else idtac
      end;
      clear IH SAFE; destruct SAME as [? [? [? ?]]]; subst
  end.

Lemma break_outcome_determinate before first second :
  out_break_or_return before first -> out_break_or_return before second -> first = second.
Proof. intros FIRST SECOND; inversion FIRST; inversion SECOND; subst; congruence. Qed.

Theorem quiet_execution_determinate fe ge e le memory body trace le' memory' out :
  exec_stmt fe ge e le memory body trace le' memory' out -> quiet_statement body = true ->
  forall other_trace other_temps other_memory other_out,
  exec_stmt fe ge e le memory body other_trace other_temps other_memory other_out ->
  trace = other_trace /\ le' = other_temps /\ memory' = other_memory /\ out = other_out.
Proof.
  intro RUN; induction RUN; intros QUIET other_trace other_temps other_memory other_out OTHER;
    cbn [quiet_statement] in QUIET; try discriminate;
    try (apply andb_true_iff in QUIET as [LEFT RIGHT]); inversion OTHER; subst.
  all: align_evaluations.
  all: repeat match goal with
  | FIRST : sem_cast ?v ?from ?to ?m = Some ?value,
    SECOND : sem_cast ?v ?from ?to ?m = Some ?other |- _ =>
      assert (value = other) by congruence; clear SECOND; subst
  | FIRST : bool_val ?v ?ty ?m = Some ?b, SECOND : bool_val ?v ?ty ?m = Some ?other |- _ =>
      assert (b = other) by congruence; clear SECOND; subst
  end.
  all: try match goal with IH : quiet_statement (if ?choice then _ else _) = true -> _ |- _ =>
    destruct choice; cbn in * end.
  all: align_statement_runs; try contradiction;
    try (repeat split; congruence).
  all: try match goal with
  | NORMAL : out_normal_or_continue ?out, STOP : out_break_or_return ?out _ |- _ =>
      inversion NORMAL; inversion STOP; subst; congruence
  end.
  all: try match goal with STOP : out_break_or_return Out_normal _ |- _ => inversion STOP end.
  all: try (match goal with FIRST : assign_loc _ _ _ _ _ _ _ ?m1, SECOND : assign_loc _ _ _ _ _ _ _ ?m2 |- _ =>
      pose proof (assign_location_determinate FIRST SECOND); subst end; repeat split; reflexivity).
  all: try (match goal with FIRST : out_break_or_return ?out ?result,
    SECOND : out_break_or_return ?out ?other |- _ =>
      pose proof (break_outcome_determinate FIRST SECOND); subst end;
    repeat split; reflexivity).
Qed.

Theorem quiet_fragment_determinate fe body entry first second :
  quiet_statement body = true -> clight_fragment_run fe body entry first ->
  clight_fragment_run fe body entry second -> first = second.
Proof.
  destruct first as [trace temps memory out], second as [other_trace other_temps other_memory other_out].
  intros QUIET FIRST SECOND.
  destruct (@quiet_execution_determinate fe (ClightCondition.entry_ge entry)
    (ClightCondition.entry_env entry) (ClightCondition.entry_temps entry) (ClightCondition.entry_memory entry)
    body trace temps memory out FIRST QUIET other_trace other_temps other_memory other_out SECOND)
    as [TRACE [TEMPS [MEMORY EXIT]]]; subst; reflexivity.
Qed.

Theorem quiet_execution_silent fe ge e le memory body trace le' memory' out :
  exec_stmt fe ge e le memory body trace le' memory' out -> quiet_statement body = true -> trace = E0.
Proof.
  intro RUN; induction RUN; intros QUIET; cbn [quiet_statement] in QUIET; try discriminate;
    try (apply andb_true_iff in QUIET as [LEFT RIGHT]); try (destruct b; cbn in *).
  all: repeat match goal with IH : quiet_statement ?code = true -> ?tr = E0 |- _ =>
    let SAFE := fresh "SAFE" in assert (SAFE : quiet_statement code = true) by
      (first [assumption|cbn [quiet_statement]; apply andb_true_iff; split; assumption]);
    specialize (IH SAFE); rewrite IH
  end; reflexivity.
Qed.

Theorem quiet_exact_host_determinate fe body entry first second :
  quiet_statement body = true ->
  runs (readonly_clight_host fe (@eq ClightCondition.fragment_observation)) body entry first ->
  runs (readonly_clight_host fe (@eq ClightCondition.fragment_observation)) body entry second -> first = second.
Proof.
  intros QUIET [raw [FIRST SAME1]] [other_raw [SECOND SAME2]]; subst raw other_raw.
  eapply quiet_fragment_determinate; eassumption.
Qed.

Print Assumptions deref_location_determinate.
Print Assumptions expressions_determinate.
Print Assumptions assign_location_determinate.
Print Assumptions quiet_execution_determinate.
Print Assumptions quiet_fragment_determinate.
Print Assumptions quiet_exact_host_determinate.
Print Assumptions quiet_execution_silent.
