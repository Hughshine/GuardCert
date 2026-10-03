From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr ClightGuard ClightNoWrap
  ClightRedundantSet ClightMatrixGuard ClightCountedLoop ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRegistryGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_guard_gate_exact first second s known accepted :
  (forall flag, decision_run s first flag <-> flag = known) ->
  (known = true -> forall flag, decision_run s second flag <-> flag = accepted) ->
  forall flag, decision_run s (decision_bind first second (Decision false)) flag <-> flag = known && accepted.
Proof.
  intros FIRST SECOND flag; destruct known.
  - apply memory_decision_bind_exact; [exact FIRST|apply SECOND; reflexivity].
  - change (command_run decision_test_language (conditional decision_test_language first second (Decision false)) s flag <-> flag = false).
    rewrite conditional_known by exact FIRST; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Lemma memory_triple_register_exact identifier value s : register_domain identifier s -> forall flag,
  decision_run s (register_tree identifier value) flag <-> flag = register_flag identifier value s.
Proof.
  intros DOMAIN flag; split.
  - intro RUN; eapply pure_tree_determinate; [apply register_tree_pure|exact RUN|apply register_tree_run; exact DOMAIN].
  - intro SAME; subst; apply register_tree_run; exact DOMAIN.
Qed.
Lemma memory_triple_range_exact identifier limit s : register_domain identifier s -> forall flag,
  decision_run s (register_range_tree identifier limit) flag <-> flag = register_range_flag identifier limit s.
Proof.
  intros DOMAIN flag; split.
  - intro RUN; eapply pure_tree_determinate; [apply register_range_tree_pure|exact RUN|apply register_range_tree_run; exact DOMAIN].
  - intro SAME; subst; apply register_range_tree_run; exact DOMAIN.
Qed.
Definition memory_triple_header_accept cap row row_bound s := register_flag row Int.zero s && register_range_flag row_bound cap s.
Definition memory_triple_header_tree cap row row_bound :=
  decision_bind (register_tree row Int.zero) (register_range_tree row_bound cap) (Decision false).
Definition memory_triple_guard_accept cap descriptors row row_bound column_bound depth_bound s :=
  memory_triple_header_accept cap row row_bound s &&
    (register_range_flag column_bound cap s && (register_range_flag depth_bound cap s && memory_registry_guard_accept descriptors s)).
Definition memory_triple_guard_tree cap descriptors row row_bound column_bound depth_bound :=
  decision_bind (memory_triple_header_tree cap row row_bound)
    (decision_bind (register_range_tree column_bound cap)
      (decision_bind (register_range_tree depth_bound cap) (memory_array_registry_tree descriptors) (Decision false))
      (Decision false)) (Decision false).
Definition memory_triple_guard_domain cap descriptors row row_bound column_bound depth_bound s :=
  register_domain row s /\ register_domain row_bound s /\
  (memory_triple_header_accept cap row row_bound s = true -> register_domain column_bound s /\
    (register_range_flag column_bound cap s = true -> register_domain depth_bound s /\
      (register_range_flag depth_bound cap s = true -> memory_registry_guard_domain descriptors s))).
Lemma memory_triple_header_sound cap row bound s :
  signed_range cap -> register_domain row s -> register_domain bound s ->
  memory_triple_header_accept cap row bound s = true ->
  (entry_temps s) ! row = Some (Vint Int.zero) /\ register_range bound cap s.
Proof.
  intros RANGE ROW BOUND ACCEPT; unfold memory_triple_header_accept in ACCEPT; apply andb_true_iff in ACCEPT as [ZERO COUNT].
  split; [eapply register_flag_evidence; eassumption|apply register_range_sound; assumption].
Qed.
Theorem memory_triple_guard_exact cap descriptors row row_bound column_bound depth_bound s :
  memory_triple_guard_domain cap descriptors row row_bound column_bound depth_bound s -> forall flag,
  decision_run s (memory_triple_guard_tree cap descriptors row row_bound column_bound depth_bound) flag <->
    flag = memory_triple_guard_accept cap descriptors row row_bound column_bound depth_bound s.
Proof.
  intros [ROW [BOUND CONTINUATION]] flag; unfold memory_triple_guard_tree,memory_triple_guard_accept.
  apply memory_guard_gate_exact.
  - unfold memory_triple_header_tree,memory_triple_header_accept; apply memory_decision_bind_exact.
    + apply memory_triple_register_exact; exact ROW.
    + apply memory_triple_range_exact; exact BOUND.
  - intro HEADER; destruct (CONTINUATION HEADER) as [COLUMN REST]; intro answer.
    apply memory_guard_gate_exact.
    + apply memory_triple_range_exact; exact COLUMN.
    + intro WIDTH; destruct (REST WIDTH) as [DEPTH ARRAYS]; intro result.
      apply memory_guard_gate_exact.
      * apply memory_triple_range_exact; exact DEPTH.
      * intro LENGTH; apply memory_registry_guard_exact; apply ARRAYS; exact LENGTH.
Qed.
Theorem memory_triple_guard_sound cap descriptors row row_bound column_bound depth_bound s :
  signed_range cap -> memory_triple_guard_domain cap descriptors row row_bound column_bound depth_bound s ->
  memory_triple_guard_accept cap descriptors row row_bound column_bound depth_bound s = true ->
  (entry_temps s) ! row = Some (Vint Int.zero) /\ register_range row_bound cap s /\
    register_range column_bound cap s /\ register_range depth_bound cap s /\ memory_registry_guard_property descriptors s.
Proof.
  intros RANGE [ROW [BOUND CONTINUATION]] ACCEPT.
  unfold memory_triple_guard_accept in ACCEPT; rewrite !andb_true_iff in ACCEPT.
  destruct ACCEPT as [HEADER [WIDTH [LENGTH ALIAS]]].
  destruct (memory_triple_header_sound RANGE ROW BOUND HEADER) as [ZERO NRANGE].
  destruct (CONTINUATION HEADER) as [COLUMN REST]; destruct (REST WIDTH) as [DEPTH ARRAYS].
  split; [exact ZERO|]; split; [exact NRANGE|]; split; [apply register_range_sound; assumption|].
  split; [apply register_range_sound; assumption|apply memory_registry_guard_accept_sound; [apply ARRAYS; exact LENGTH|exact ALIAS]].
Qed.
Definition memory_triple_guard_dimension cap descriptors row row_bound column_bound depth_bound :=
  @positive_dimension clight_entry unit
    (memory_triple_guard_domain cap descriptors row row_bound column_bound depth_bound)
    (fun _ s => memory_triple_guard_accept cap descriptors row row_bound column_bound depth_bound s = true)
    (fun _ => memory_triple_guard_accept cap descriptors row row_bound column_bound depth_bound)
    (fun _ s _ ACCEPT => ACCEPT).
Definition memory_triple_guard_primitives cap descriptors row row_bound column_bound depth_bound :
  check_primitives decision_test_language (memory_triple_guard_domain cap descriptors row row_bound column_bound depth_bound)
    (decide_atom (memory_triple_guard_dimension cap descriptors row row_bound column_bound depth_bound)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language
    (memory_triple_guard_domain cap descriptors row row_bound column_bound depth_bound)
    (decide_atom (memory_triple_guard_dimension cap descriptors row row_bound column_bound depth_bound))
    (fun _ => memory_triple_guard_tree cap descriptors row row_bound column_bound depth_bound) (fun _ => Decision true) _ _).
  - intros [] s flag DOMAIN.
    change (decision_run s (memory_triple_guard_tree cap descriptors row row_bound column_bound depth_bound) flag <->
      flag = checked_valid (decide_atom (memory_triple_guard_dimension cap descriptors row row_bound column_bound depth_bound) tt s)).
    rewrite memory_triple_guard_exact by exact DOMAIN.
    cbn [memory_triple_guard_dimension positive_dimension decide_atom];
      destruct (memory_triple_guard_accept cap descriptors row row_bound column_bound depth_bound s); reflexivity.
  - intros [] s flag expected DOMAIN ACCEPT.
    change (decision_run s (Decision true) flag <-> flag = expected).
    cbn [memory_triple_guard_dimension positive_dimension decide_atom] in ACCEPT.
    destruct (memory_triple_guard_accept cap descriptors row row_bound column_bound depth_bound s); try discriminate;
      inversion ACCEPT; subst; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Defined.
Print Assumptions memory_triple_guard_primitives.
