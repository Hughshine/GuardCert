From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightRectangularStore ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRegistryBackend GuardMemoryRegistryGuard.
Import ListNotations.
Set Implicit Arguments.

Definition memory_named_guard_domain base descriptors row bound inner_bound s :=
  rectangle_guard_domain row bound inner_bound s /\
  (rectangle_guard_accept base row bound inner_bound tt s = true ->
    memory_registry_guard_domain descriptors s).
Definition memory_named_guard_property base descriptors row bound inner_bound s :=
  rectangle_guard_property base row bound inner_bound tt s /\ memory_registry_guard_property descriptors s.
Definition memory_named_guard_accept base descriptors row bound inner_bound s :=
  rectangle_guard_accept base row bound inner_bound tt s && memory_registry_guard_accept descriptors s.
Definition memory_named_guard_tree base descriptors row bound inner_bound :=
  decision_bind (rectangle_guard_tree base row bound inner_bound)
    (memory_array_registry_tree descriptors) (Decision false).

Theorem memory_named_guard_accept_sound base descriptors row bound inner_bound s :
  rectangle_layout_valid base -> memory_named_guard_domain base descriptors row bound inner_bound s ->
  memory_named_guard_accept base descriptors row bound inner_bound s = true ->
  memory_named_guard_property base descriptors row bound inner_bound s.
Proof.
  intros VALID [DOMAIN ARRAYS] ACCEPT; apply andb_true_iff in ACCEPT as [RANGE ALIAS].
  split.
  - apply rectangle_guard_accept_sound; assumption.
  - apply memory_registry_guard_accept_sound; [apply ARRAYS; exact RANGE|exact ALIAS].
Qed.
Theorem memory_named_guard_exact base descriptors row bound inner_bound s :
  memory_named_guard_domain base descriptors row bound inner_bound s -> forall flag,
  decision_run s (memory_named_guard_tree base descriptors row bound inner_bound) flag <->
  flag = memory_named_guard_accept base descriptors row bound inner_bound s.
Proof.
  intros [DOMAIN ARRAYS] flag.
  assert (PREFIX : forall result,
    decision_run s (rectangle_guard_tree base row bound inner_bound) result <->
    result = rectangle_guard_accept base row bound inner_bound tt s).
  { intro result; split.
    - intro RUN; eapply pure_tree_determinate;
        [apply rectangle_guard_tree_pure|exact RUN|apply rectangle_guard_tree_run; exact DOMAIN].
    - intro SAME; subst; apply rectangle_guard_tree_run; exact DOMAIN. }
  unfold memory_named_guard_tree,memory_named_guard_accept.
  destruct (rectangle_guard_accept base row bound inner_bound tt s) eqn:RANGE.
  - apply memory_decision_bind_exact; [exact PREFIX|apply memory_registry_guard_exact; apply ARRAYS; reflexivity].
  - change (command_run decision_test_language
      (conditional decision_test_language (rectangle_guard_tree base row bound inner_bound)
        (memory_array_registry_tree descriptors) (Decision false)) s flag <-> flag = false).
    rewrite conditional_known by exact PREFIX; cbn.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Definition memory_named_guard_dimension base descriptors row bound inner_bound (VALID : rectangle_layout_valid base) :=
  @positive_dimension clight_entry unit (memory_named_guard_domain base descriptors row bound inner_bound)
    (fun _ => memory_named_guard_property base descriptors row bound inner_bound)
    (fun _ => memory_named_guard_accept base descriptors row bound inner_bound)
    (fun _ s => @memory_named_guard_accept_sound base descriptors row bound inner_bound s VALID).
Definition memory_named_guard_primitives base descriptors row bound inner_bound (VALID : rectangle_layout_valid base) :
  check_primitives decision_test_language (memory_named_guard_domain base descriptors row bound inner_bound)
    (decide_atom (@memory_named_guard_dimension base descriptors row bound inner_bound VALID)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language
    (memory_named_guard_domain base descriptors row bound inner_bound)
    (decide_atom (@memory_named_guard_dimension base descriptors row bound inner_bound VALID))
    (fun _ => memory_named_guard_tree base descriptors row bound inner_bound) (fun _ => Decision true) _ _).
  - intros [] s flag DOMAIN.
    change (decision_run s (memory_named_guard_tree base descriptors row bound inner_bound) flag <->
      flag = checked_valid (decide_atom (@memory_named_guard_dimension base descriptors row bound inner_bound VALID) tt s)).
    rewrite memory_named_guard_exact by exact DOMAIN.
    cbn [memory_named_guard_dimension positive_dimension decide_atom].
    destruct (memory_named_guard_accept base descriptors row bound inner_bound s); reflexivity.
  - intros [] s flag expected DOMAIN ACCEPT.
    change (decision_run s (Decision true) flag <-> flag = expected).
    cbn [memory_named_guard_dimension positive_dimension decide_atom] in ACCEPT.
    destruct (memory_named_guard_accept base descriptors row bound inner_bound s); try discriminate.
    inversion ACCEPT; subst expected.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Defined.
Print Assumptions memory_named_guard_exact.
Print Assumptions memory_named_guard_primitives.
