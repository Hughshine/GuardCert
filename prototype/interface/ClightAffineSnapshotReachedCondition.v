From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightRedundantSet.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext GuardMemoryParametricSourceDomain GuardMemoryParametricGuard
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ClightFirstReachedWidth ClightAffineSnapshotSyntax ClightAffineSnapshotSourceInputs
  ClightAffineSnapshotPreparation ClightAffinePreparationEvidence ClightAffinePreparedState
  ClightAffineSnapshotLaterBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section CONDITION.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Let row:=affine_inner_pointer_row shape.
Let cache:=affine_inner_pointer_bound shape.
Let expression:=affine_inner_pointer_expression package.
Let header:=memory_affine_inner_pointer_header shape expression.
Let source_domain fe:=affine_snapshot_original_domain package(snapshot_root site)(snapshot_child site)
  (snapshot_child_cache site)(snapshot_original_header site)fe.
Let EVIDENCE fe:=@affine_snapshot_preparation_evidence(snapshot_cached_source site)package
  (snapshot_root site)(snapshot_child site)(snapshot_child_cache site)(snapshot_original_header site)
  (snapshot_header_word site)(snapshot_cached_body_exact site)fe.
Let CERT:=affine_inner_pointer_syntax package.
Variables low high : Z.
Variable skip : nat.
Variable bounds : list MemoryNested.A.interval.
Variable tree : decision_tree.
Hypothesis COMPILE : compile_first_reached_width low high skip row header bounds expression=Some tree.
Hypotheses (LOW:Int.min_signed<=low)(HIGH:high<=Int.max_signed).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.

Definition snapshot_first_reached_domain entry:=source_domain fe entry /\
  memory_affine_inner_pointer_header_accept shape(affine_inner_pointer_row_limit package)entry=true /\
  MemoryNested.A.env_within bounds(memory_source_parameter_values header entry).
Definition snapshot_first_reached_facts entry:=
  first_reached_width_fact expression(affine_prepared_valuation entry)row cache low high skip /\
  forall identifier,In identifier(affine_inner_pointer_body_parameters package++affine_inner_pointer_scalars package) ->
    exists word,(entry_temps entry)!identifier=Some(Vint word).

Lemma snapshot_first_reached_header_view entry : snapshot_first_reached_domain entry ->
  MemoryNested.A.typed_view header(memory_source_parameter_values header entry)(entry_temps entry).
Proof.
  intros [DOMAIN [HEADER RANGE]].
  eapply preparation_header_view with(EVIDENCE:=EVIDENCE fe).
  - pose proof(affine_inner_pointer_control_limits CERT)as CAPS; inversion CAPS; subst; tauto.
  - exact DOMAIN.
  - exact HEADER.
Qed.

Theorem snapshot_first_reached_condition_sound entry : snapshot_first_reached_domain entry ->
  decision_run entry tree true -> snapshot_first_reached_facts entry.
Proof.
  intros DOMAIN RUN; pose proof(snapshot_first_reached_header_view DOMAIN)as VIEW.
  destruct DOMAIN as [SOURCE [HEAD WITHIN]].
  assert(FACT:first_reached_width_fact expression(affine_prepared_valuation entry)row cache low high skip).
  { destruct entry as [ge locals temps memory].
    eapply compile_first_reached_width_sound; [exact COMPILE|exact VIEW|exact WITHIN|exact RUN]. }
  split; [exact FACT|].
  destruct(preparation_entry_words(EVIDENCE fe)entry SOURCE)as [ROW [CACHE WORDS]].
  assert(CAP:signed_range(affine_inner_pointer_row_limit package)).
  { pose proof(affine_inner_pointer_control_limits CERT)as CAPS; inversion CAPS; subst; tauto. }
  destruct(@memory_affine_inner_pointer_header_sound shape(affine_inner_pointer_row_limit package)entry
    CAP ROW CACHE HEAD)as [ZERO REST].
  destruct(first_reached_width_word_facts LOW HIGH FACT)as [EMPTY ACTIVE].
  eapply(@affine_snapshot_later_body_words original site fe entry skip).
  - exact SOURCE.
  - exact ZERO.
  - exact(proj1 FACT).
  - intros i I; rewrite affine_prepared_upper_math; exact(EMPTY i I).
  - rewrite affine_prepared_upper_math; exact ACTIVE.
Qed.

Lemma snapshot_first_reached_condition_total entry : snapshot_first_reached_domain entry ->
  exists flag,decision_run entry tree flag.
Proof.
  intro DOMAIN; pose proof(snapshot_first_reached_header_view DOMAIN)as VIEW.
  destruct DOMAIN as [SOURCE [HEAD WITHIN]],entry as [ge locals temps memory].
  destruct(@compile_first_reached_width_exact low high skip row header bounds expression tree
    (memory_source_parameter_values header(Entry ge locals temps memory))ge locals temps memory COMPILE VIEW WITHIN)
    as [first [last [previous [selected [_ [_ [_ EXACT]]]]]]].
  eexists; apply(proj2(EXACT _)); reflexivity.
Qed.

Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.

(** Acceptance produces the leaf-only input typing needed by later checks.
    Neither these inputs nor a cached-source completion are caller premises. *)
Definition snapshot_first_reached_condition : readonly_condition(readonly_clight_host fe observe)
  snapshot_first_reached_domain snapshot_first_reached_facts tree.
Proof.
  apply readonly_completed_tree_condition.
  - exact snapshot_first_reached_condition_total.
  - exact snapshot_first_reached_condition_sound.
Defined.
End CONDITION.

Print Assumptions snapshot_first_reached_header_view.
Print Assumptions snapshot_first_reached_condition_sound.
Print Assumptions snapshot_first_reached_condition_total.
Print Assumptions snapshot_first_reached_condition.
