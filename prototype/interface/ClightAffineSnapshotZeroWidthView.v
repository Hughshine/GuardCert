From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightNoWrap.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext
  GuardMemoryAffineSourceEndpoints GuardMemoryParametricGuard GuardMemoryParametricSourceDomain
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerRegionSource
  GuardMemoryZeroWidthModel GuardMemoryZeroWidthPointerSource.
From GuardInterface Require Import ClightAffineSnapshotSyntax ClightAffineSnapshotSourceInputs
  ClightAffinePreparedState ClightFirstReachedWidth ClightAffineSnapshotReachedCondition.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section INPUTS.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Let row:=affine_inner_pointer_row shape.
Let cache:=affine_inner_pointer_bound shape.
Let expression:=affine_inner_pointer_expression package.
Let context:=memory_affine_inner_pointer_region_context package.
Let cap:=affine_inner_pointer_column_limit package.
Variable skip : nat.
Variable bounds : list MemoryNested.A.interval.
Variable tree : decision_tree.
Hypothesis COMPILE : compile_first_reached_width 0 cap skip row
  (memory_affine_inner_pointer_header shape expression) bounds expression=Some tree.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.

(** C_derive input producer. The full body view is a conclusion of accepted
    actual checks and original-source licensing, not a source-user premise. *)
Theorem snapshot_zero_width_condition_facts entry :
  snapshot_first_reached_domain site bounds fe entry -> decision_run entry tree true ->
  snapshot_first_reached_facts site 0 cap skip entry.
Proof.
  intros DOMAIN RUN.
  eapply snapshot_first_reached_condition_sound; [exact COMPILE| | |exact DOMAIN|exact RUN].
  - change Int.min_signed with (-2147483648); lia.
  - pose proof (affine_inner_pointer_control_limits (affine_inner_pointer_syntax package)) as CAPS.
    rewrite Forall_forall in CAPS.
    destruct (CAPS cap ltac:(unfold cap; cbn; auto)) as [_ SAFE].
    exact (proj2 SAFE).
Qed.

Theorem snapshot_zero_width_condition_view entry :
  snapshot_first_reached_domain site bounds fe entry -> decision_run entry tree true ->
  MemoryNested.A.typed_view context (memory_source_parameter_values context entry) (entry_temps entry).
Proof.
  intros DOMAIN RUN; destruct (snapshot_zero_width_condition_facts DOMAIN RUN) as [WIDTH WORDS].
  pose proof (@snapshot_first_reached_header_view original site bounds fe entry DOMAIN) as HEADER.
  apply memory_source_parameter_view; intros identifier MEMBER.
  unfold context,memory_affine_inner_pointer_region_context,memory_affine_inner_pointer_parameters in MEMBER.
  rewrite <-app_assoc in MEMBER; apply in_app_or in MEMBER as [HEAD|BODY].
  - eapply memory_source_typed_word; [exact HEADER|exact HEAD].
  - apply WORDS; exact BODY.
Qed.

Theorem snapshot_zero_width_condition_property entry :
  snapshot_first_reached_domain site bounds fe entry -> decision_run entry tree true ->
  memory_affine_inner_pointer_zero_width_property shape expression cap entry.
Proof.
  intros DOMAIN RUN; destruct (snapshot_zero_width_condition_facts DOMAIN RUN) as [WIDTH WORDS].
  unfold first_reached_width_fact in WIDTH; destruct WIDTH as [REACHED [ALL REST]].
  unfold memory_affine_inner_pointer_zero_width_property; intros i I.
  rewrite memory_affine_inner_pointer_word_math.
  apply ALL; rewrite memory_source_word_temp in I; exact I.
Qed.

(** The endpoint syntax equation is a static factory obligation. This theorem
    establishes the dynamic model assumption for the newly checked C_opt. *)
Theorem snapshot_zero_width_condition_model entry first last :
  memory_source_endpoints row context expression=Some(first,last) ->
  snapshot_first_reached_domain site bounds fe entry -> decision_run entry tree true ->
  memory_source_zero_width_model cap row context expression
    (memory_source_parameter_values context entry)=true.
Proof.
  intros ENDS DOMAIN RUN.
  destruct (snapshot_zero_width_condition_facts DOMAIN RUN) as [WIDTH WORDS].
  unfold first_reached_width_fact in WIDTH; destruct WIDTH as [REACHED [ALL REST]].
  assert (POSITIVE:0<affine_prepared_valuation entry cache).
  { change (0<=Z.of_nat skip<affine_prepared_valuation entry cache) in REACHED; lia. }
  unfold context,memory_affine_inner_pointer_region_context,memory_affine_inner_pointer_parameters,
    memory_affine_inner_pointer_header,memory_source_context in ENDS|-*.
  cbn in ENDS|-*.
  unfold memory_source_parameter_values; fold (affine_prepared_valuation entry).
  eapply (proj2 (@memory_source_zero_width_model_exact expression row cache _
    (affine_prepared_valuation entry) cap first last POSITIVE ENDS)).
  exact ALL.
Qed.
End INPUTS.

Print Assumptions snapshot_zero_width_condition_facts.
Print Assumptions snapshot_zero_width_condition_view.
Print Assumptions snapshot_zero_width_condition_property.
Print Assumptions snapshot_zero_width_condition_model.
