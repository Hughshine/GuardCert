From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightRedundantSet ClightNoWrap ClightTempFrame ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryIntervalGuard GuardMemoryWindowParameterGuard.
From GuardAffineNest Require Import AffineNestProbe AffineNestNumericGuard.
Import ListNotations.
Set Implicit Arguments.

Definition affine_numeric_guard_statement ranges parameters iterator floor cap result :=
  tree_statement(affine_numeric_guard_tree ranges parameters iterator floor cap)
    (affine_probe_store result true)(affine_probe_store result false).

Theorem affine_numeric_guard_execution ranges parameters iterator floor cap result fe ge locals temps memory :
  Forall(fun identifier => register_domain identifier(Entry ge locals temps memory)) parameters ->
  register_domain iterator(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory(affine_numeric_guard_statement ranges parameters iterator floor cap result) E0
    (PTree.set result(Vint(if affine_numeric_guard_flag ranges parameters iterator floor cap(Entry ge locals temps memory)
      then Int.one else Int.zero)) temps) memory Out_normal.
Proof.
  intros PARAMETERS ITERATOR; unfold affine_numeric_guard_statement.
  pose proof(proj2(@affine_numeric_guard_encoding ranges parameters iterator floor cap(Entry ge locals temps memory)
    PARAMETERS ITERATOR _ ) eq_refl) as RUN.
  eapply decision_fragment_run; [exact RUN|].
  destruct(affine_numeric_guard_flag ranges parameters iterator floor cap(Entry ge locals temps memory)); constructor; constructor.
Qed.

Lemma affine_interval_flag_frame identifier lower upper ge locals before after memory :
  after!identifier=before!identifier ->
  signed_interval_flag identifier lower upper(Entry ge locals after memory)=
  signed_interval_flag identifier lower upper(Entry ge locals before memory).
Proof.
  intro SAME; unfold signed_interval_flag,signed_interval_lower_flag,register_at_most,temp_word;
    cbn [entry_temps]; rewrite SAME; reflexivity.
Qed.
Lemma affine_parameter_flag_frame ranges parameters ge locals before after memory :
  temp_agree parameters before after ->
  window_parameters_accept ranges parameters(Entry ge locals after memory)=
  window_parameters_accept ranges parameters(Entry ge locals before memory).
Proof.
  revert parameters; induction ranges as [|[lower upper] rest IH]; intros [|identifier parameters] FRAME; cbn; try reflexivity.
  rewrite (@affine_interval_flag_frame identifier lower upper ge locals before after memory
    ltac:(apply FRAME; cbn; auto)).
  rewrite IH; [reflexivity|intros key MEMBER; apply FRAME; cbn; auto].
Qed.

Theorem affine_numeric_guard_flag_frame ranges parameters iterator floor cap ge locals before after memory :
  temp_agree(parameters++[iterator]) before after ->
  affine_numeric_guard_flag ranges parameters iterator floor cap(Entry ge locals after memory)=
  affine_numeric_guard_flag ranges parameters iterator floor cap(Entry ge locals before memory).
Proof.
  intro FRAME; unfold affine_numeric_guard_flag.
  rewrite (@affine_parameter_flag_frame ranges parameters ge locals before after memory
    ltac:(intros identifier MEMBER; apply FRAME,in_or_app; auto)).
  rewrite (@affine_interval_flag_frame iterator floor cap ge locals before after memory
    ltac:(apply FRAME,in_or_app; right; cbn; auto)); reflexivity.
Qed.
Print Assumptions affine_numeric_guard_execution.
Print Assumptions affine_numeric_guard_flag_frame.
