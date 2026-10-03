From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightRectangularStore ClightRectangularGuard ClightCountedLoop ClightNoWrap.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryTiledClight GuardMemoryRegistryBackend GuardMemoryRegistryGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This form avoids evaluating N+M before establishing its range. *)
Definition memory_ragged_width_test base :=
  L.LE (L.Var 0) (L.Sum (L.Sum (L.Constant (rectangle_stride base))
    (L.Mult (-1) (L.Var 1))) (L.Constant 1)).
Definition memory_ragged_positive_bounds base :=
  [MemoryNested.A.Interval 1 (rectangle_outer_limit base);
    MemoryNested.A.Interval 1 (rectangle_stride base)].
Definition compile_memory_ragged_width base bound parameter :=
  MemoryNested.A.lower_test [bound;parameter] (memory_ragged_positive_bounds base)
    (memory_ragged_width_test base).
Definition memory_ragged_width_flag base bound parameter s :=
  L.eval_test [Int.signed (temp_word bound (entry_temps s));
    Int.signed (temp_word parameter (entry_temps s))] (memory_ragged_width_test base).
Definition memory_ragged_width_property base bound parameter s :=
  Int.signed (temp_word bound (entry_temps s)) + Int.signed (temp_word parameter (entry_temps s))-1
    <= rectangle_stride base.

Lemma memory_ragged_width_sound base bound parameter s :
  memory_ragged_width_flag base bound parameter s = true ->
  memory_ragged_width_property base bound parameter s.
Proof.
  unfold memory_ragged_width_flag,memory_ragged_width_test,memory_ragged_width_property;
    cbn [L.eval_test L.eval_expr nth]; rewrite Z.leb_le; lia.
Qed.
Lemma memory_ragged_positive_view base bound parameter s :
  register_range bound (rectangle_outer_limit base) s -> register_range parameter (rectangle_stride base) s ->
  MemoryNested.A.typed_view [bound;parameter]
    [Int.signed (temp_word bound (entry_temps s));Int.signed (temp_word parameter (entry_temps s))] (entry_temps s) /\
  MemoryNested.A.env_within (memory_ragged_positive_bounds base)
    [Int.signed (temp_word bound (entry_temps s));Int.signed (temp_word parameter (entry_temps s))].
Proof.
  intros [[n N] NR] [[m M] MR]; split.
  - apply rectangle_tiled_parameter_view; [apply Int.signed_range|apply Int.signed_range| |];
      unfold temp_word; rewrite ?N,?M,Int.repr_signed; reflexivity.
  - intros [|[|index]] interval INDEX; cbn [memory_ragged_positive_bounds nth_error] in INDEX;
      try rewrite nth_error_nil in INDEX; try discriminate; inversion INDEX; subst interval;
      unfold MemoryNested.A.contains; cbn [MemoryNested.A.lower MemoryNested.A.upper nth]; lia.
Qed.
Lemma memory_ragged_width_exact base bound parameter tree s :
  compile_memory_ragged_width base bound parameter = Some tree ->
  register_range bound (rectangle_outer_limit base) s -> register_range parameter (rectangle_stride base) s ->
  forall flag, decision_run s tree flag <-> flag = memory_ragged_width_flag base bound parameter s.
Proof.
  intros LOWER N M flag; destruct (@memory_ragged_positive_view base bound parameter s N M) as [VIEW WITHIN].
  destruct s as [ge locals temps memory]; unfold memory_ragged_width_flag; cbn [entry_temps];
    eapply MemoryNested.A.lower_test_exact; [exact LOWER|exact WITHIN|exact VIEW].
Qed.

Definition memory_ragged_range_accept base row bound parameter s :=
  rectangle_guard_accept base row bound parameter tt s && memory_ragged_width_flag base bound parameter s.
Definition memory_ragged_guard_domain base descriptors row bound parameter s :=
  rectangle_guard_domain row bound parameter s /\
  (memory_ragged_range_accept base row bound parameter s = true -> memory_registry_guard_domain descriptors s).
Definition memory_ragged_guard_property base descriptors row bound parameter s :=
  rectangle_guard_property base row bound parameter tt s /\
  memory_ragged_width_property base bound parameter s /\ memory_registry_guard_property descriptors s.
Definition memory_ragged_guard_accept base descriptors row bound parameter s :=
  memory_ragged_range_accept base row bound parameter s && memory_registry_guard_accept descriptors s.
Definition memory_ragged_guard_tree base descriptors row bound parameter width_tree :=
  decision_bind (rectangle_guard_tree base row bound parameter)
    (decision_bind width_tree (memory_array_registry_tree descriptors) (Decision false)) (Decision false).

Theorem memory_ragged_guard_accept_sound base descriptors row bound parameter s :
  rectangle_layout_valid base -> memory_ragged_guard_domain base descriptors row bound parameter s ->
  memory_ragged_guard_accept base descriptors row bound parameter s = true ->
  memory_ragged_guard_property base descriptors row bound parameter s.
Proof.
  intros VALID [DOMAIN ARRAYS] ACCEPT; apply andb_true_iff in ACCEPT as [RANGES ALIAS].
  unfold memory_ragged_range_accept in RANGES; apply andb_true_iff in RANGES as [RANGE WIDTH].
  split; [apply rectangle_guard_accept_sound; assumption|]; split.
  - apply memory_ragged_width_sound; exact WIDTH.
  - apply memory_registry_guard_accept_sound; [apply ARRAYS; unfold memory_ragged_range_accept; rewrite RANGE,WIDTH; reflexivity|exact ALIAS].
Qed.
Theorem memory_ragged_guard_exact base descriptors row bound parameter width_tree s :
  rectangle_layout_valid base -> compile_memory_ragged_width base bound parameter = Some width_tree ->
  memory_ragged_guard_domain base descriptors row bound parameter s -> forall flag,
  decision_run s (memory_ragged_guard_tree base descriptors row bound parameter width_tree) flag <->
  flag = memory_ragged_guard_accept base descriptors row bound parameter s.
Proof.
  intros VALID LOWER [DOMAIN ARRAYS] flag.
  assert (PREFIX : forall result, decision_run s (rectangle_guard_tree base row bound parameter) result <->
    result = rectangle_guard_accept base row bound parameter tt s).
  { intro result; split.
    - intro RUN; eapply pure_tree_determinate;
      [apply rectangle_guard_tree_pure|exact RUN|apply rectangle_guard_tree_run; exact DOMAIN].
    - intro SAME; subst; apply rectangle_guard_tree_run; exact DOMAIN. }
  unfold memory_ragged_guard_tree,memory_ragged_guard_accept,memory_ragged_range_accept.
  destruct (rectangle_guard_accept base row bound parameter tt s) eqn:RANGE.
  - destruct (@rectangle_guard_accept_sound base row bound parameter VALID tt s DOMAIN RANGE) as [ZERO [N M]].
    assert (WIDTH : forall result, decision_run s width_tree result <->
      result = memory_ragged_width_flag base bound parameter s).
    { apply memory_ragged_width_exact; assumption. }
    apply memory_decision_bind_exact with (known := true)
      (accepted := memory_ragged_width_flag base bound parameter s && memory_registry_guard_accept descriptors s); [exact PREFIX|].
    clear flag; intro flag.
    destruct (memory_ragged_width_flag base bound parameter s) eqn:WIDE.
    + apply memory_decision_bind_exact with (known := true)
        (accepted := memory_registry_guard_accept descriptors s); [exact WIDTH|apply memory_registry_guard_exact; apply ARRAYS;
        unfold memory_ragged_range_accept; rewrite RANGE,WIDE; reflexivity].
    + change (command_run decision_test_language
        (conditional decision_test_language width_tree (memory_array_registry_tree descriptors) (Decision false)) s flag <-> flag = false).
      rewrite conditional_known by exact WIDTH; cbn.
      split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - change (command_run decision_test_language
      (conditional decision_test_language (rectangle_guard_tree base row bound parameter)
        (decision_bind width_tree (memory_array_registry_tree descriptors) (Decision false)) (Decision false)) s flag <-> flag = false).
    rewrite conditional_known by exact PREFIX; cbn.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Definition memory_ragged_guard_dimension base descriptors row bound parameter (VALID : rectangle_layout_valid base) :=
  @positive_dimension clight_entry unit (memory_ragged_guard_domain base descriptors row bound parameter)
    (fun _ => memory_ragged_guard_property base descriptors row bound parameter)
    (fun _ => memory_ragged_guard_accept base descriptors row bound parameter)
    (fun _ s => @memory_ragged_guard_accept_sound base descriptors row bound parameter s VALID).
Definition memory_ragged_guard_primitives base descriptors row bound parameter width_tree
  (VALID : rectangle_layout_valid base) (LOWER : compile_memory_ragged_width base bound parameter = Some width_tree) :
  check_primitives decision_test_language (memory_ragged_guard_domain base descriptors row bound parameter)
    (decide_atom (@memory_ragged_guard_dimension base descriptors row bound parameter VALID)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language
    (memory_ragged_guard_domain base descriptors row bound parameter)
    (decide_atom (@memory_ragged_guard_dimension base descriptors row bound parameter VALID))
    (fun _ => memory_ragged_guard_tree base descriptors row bound parameter width_tree) (fun _ => Decision true) _ _).
  - intros [] s flag DOMAIN.
    change (decision_run s (memory_ragged_guard_tree base descriptors row bound parameter width_tree) flag <->
      flag = checked_valid (decide_atom (@memory_ragged_guard_dimension base descriptors row bound parameter VALID) tt s)).
    rewrite memory_ragged_guard_exact by assumption.
    cbn [memory_ragged_guard_dimension positive_dimension decide_atom].
    destruct (memory_ragged_guard_accept base descriptors row bound parameter s); reflexivity.
  - intros [] s flag expected DOMAIN ACCEPT.
    change (decision_run s (Decision true) flag <-> flag = expected).
    cbn [memory_ragged_guard_dimension positive_dimension decide_atom] in ACCEPT.
    destruct (memory_ragged_guard_accept base descriptors row bound parameter s); try discriminate.
    inversion ACCEPT; subst expected.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Defined.
Print Assumptions memory_ragged_width_exact.
Print Assumptions memory_ragged_guard_primitives.
