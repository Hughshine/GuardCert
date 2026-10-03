From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightGuard ClightNoWrap ClightPureExpr ClightRedundantSet
  ClightRectangularStore ClightRectangularGuard PolCertAffineGuard.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryLoops GuardMemoryArrayBackend
  GuardMemoryRegistryBackend GuardMemoryRegistryGuard GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation
  GuardMemoryAffineSourceEndpoints GuardMemoryParametricWidth.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module MemorySourceRanges := MemoryNested.G.
Definition memory_source_parameter_values context s := map (fun identifier => Int.signed (temp_word identifier (entry_temps s))) context.
Definition memory_source_header_accept base row bound s :=
  register_flag row Int.zero s && register_range_flag bound (rectangle_outer_limit base) s.
Definition memory_source_header_tree base row bound :=
  Test (register_guard row Int.zero) (register_range_tree bound (rectangle_outer_limit base)) (Decision false).
Definition memory_source_range_accept context bounds s :=
  formula_accepts (MemorySourceRanges.atom_decide context bounds (memory_source_parameter_values context s))
    (MemorySourceRanges.bounds_formula bounds) s.
Definition memory_source_width_accept stride row context expression s :=
  match memory_source_endpoints row context expression with
  | Some (first,last) => L.eval_test (memory_source_parameter_values context s) (memory_source_endpoint_test stride first last)
  | None => false end.
Definition memory_source_guard_accept base descriptors row bound context bounds expression s :=
  memory_source_header_accept base row bound s && memory_source_range_accept context bounds s &&
  memory_source_width_accept (rectangle_stride base) row context expression s && memory_registry_guard_accept descriptors s.
Definition memory_source_guard_tree base descriptors row bound context bounds width_tree :=
  decision_bind (memory_source_header_tree base row bound)
    (decision_bind (MemorySourceRanges.range_guard context bounds)
      (decision_bind width_tree (memory_array_registry_tree descriptors) (Decision false)) (Decision false)) (Decision false).
Definition memory_source_guard_domain base descriptors row bound context bounds expression s :=
  register_domain row s /\ register_domain bound s /\
    (memory_source_header_accept base row bound s = true ->
      MemoryNested.A.typed_view context (memory_source_parameter_values context s) (entry_temps s)) /\
    (memory_source_header_accept base row bound s = true ->
      memory_source_range_accept context bounds s = true ->
      memory_source_width_accept (rectangle_stride base) row context expression s = true ->
      memory_registry_guard_domain descriptors s).
Lemma memory_source_header_exact base row bound s :
  register_domain row s -> register_domain bound s -> forall flag,
  decision_run s (memory_source_header_tree base row bound) flag <-> flag = memory_source_header_accept base row bound s.
Proof.
  intros ROW BOUND flag.
  assert (ZERO : forall result, decision_run s (register_tree row Int.zero) result <->
    result = register_flag row Int.zero s).
  { intro result; split.
    - intro RUN; eapply pure_tree_determinate with (t := register_tree row Int.zero);
        [unfold register_tree,register_guard; repeat constructor|exact RUN|apply register_tree_run; exact ROW].
    - intro SAME; subst result; apply register_tree_run; exact ROW. }
  assert (RANGE : forall result, decision_run s (register_range_tree bound (rectangle_outer_limit base)) result <->
    result = register_range_flag bound (rectangle_outer_limit base) s).
  { intro result; split.
    - intro RUN; eapply pure_tree_determinate with (t := register_range_tree bound (rectangle_outer_limit base));
        [apply register_range_tree_pure|exact RUN|apply register_range_tree_run; exact BOUND].
    - intro SAME; subst result; apply register_range_tree_run; exact BOUND. }
  unfold memory_source_header_tree,memory_source_header_accept.
  change (command_run decision_test_language
    (conditional decision_test_language (register_tree row Int.zero)
      (register_range_tree bound (rectangle_outer_limit base)) (Decision false)) s flag <->
    flag = register_flag row Int.zero s && register_range_flag bound (rectangle_outer_limit base) s).
  destruct (register_flag row Int.zero s) eqn:HEADER.
  - rewrite conditional_known by exact ZERO; cbn; apply RANGE.
  - rewrite conditional_known by exact ZERO; cbn.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst flag; constructor].
Qed.
Lemma memory_source_range_exact context bounds s :
  MemoryNested.A.typed_view context (memory_source_parameter_values context s) (entry_temps s) -> forall flag,
  decision_run s (MemorySourceRanges.range_guard context bounds) flag <-> flag = memory_source_range_accept context bounds s.
Proof.
  intros VIEW flag; unfold memory_source_range_accept.
  rewrite MemorySourceRanges.range_guard_environment with (env := memory_source_parameter_values context s).
  apply synthesized_tree_correct; exact VIEW.
Qed.
Lemma memory_source_width_exact stride row context bounds expression tree s :
  compile_memory_source_width stride row context bounds expression = Some tree ->
  MemoryNested.A.typed_view context (memory_source_parameter_values context s) (entry_temps s) ->
  MemoryNested.A.env_within bounds (memory_source_parameter_values context s) -> forall flag,
  decision_run s tree flag <-> flag = memory_source_width_accept stride row context expression s.
Proof.
  intros COMPILE VIEW RANGE flag; unfold compile_memory_source_width in COMPILE.
  unfold memory_source_width_accept.
  destruct (memory_source_endpoints row context expression) as [[first last]|] eqn:ENDPOINTS; [|discriminate].
  destruct s; eapply MemoryNested.A.lower_test_exact; eassumption.
Qed.
Theorem memory_source_guard_exact base descriptors row bound context bounds expression width_tree s :
  compile_memory_source_width (rectangle_stride base) row context bounds expression = Some width_tree ->
  memory_source_guard_domain base descriptors row bound context bounds expression s -> forall flag,
  decision_run s (memory_source_guard_tree base descriptors row bound context bounds width_tree) flag <->
    flag = memory_source_guard_accept base descriptors row bound context bounds expression s.
Proof.
  intros LOWER [ROW [BOUND [PARAMETERS ARRAYS]]] flag.
  assert (PREFIX : forall result, decision_run s (memory_source_header_tree base row bound) result <->
    result = memory_source_header_accept base row bound s) by (apply memory_source_header_exact; assumption).
  unfold memory_source_guard_tree,memory_source_guard_accept.
  destruct (memory_source_header_accept base row bound s) eqn:HEADER.
  - pose proof (PARAMETERS eq_refl) as VIEW.
    pose proof (@memory_source_range_exact context bounds s VIEW) as RANGES.
    destruct (memory_source_range_accept context bounds s) eqn:RANGE.
    + assert (WITHIN : MemoryNested.A.env_within bounds (memory_source_parameter_values context s)).
      { eapply MemorySourceRanges.range_guard_sound with (layout := context) (s := s);
          [exact VIEW|apply RANGES; reflexivity]. }
      pose proof (@memory_source_width_exact (rectangle_stride base) row context bounds expression width_tree s LOWER VIEW WITHIN) as WIDTHS.
      destruct (memory_source_width_accept (rectangle_stride base) row context expression s) eqn:WIDTH.
      * apply memory_decision_bind_exact with (known := true) (accepted := memory_registry_guard_accept descriptors s);
          [exact PREFIX|].
        intro result; apply memory_decision_bind_exact with (known := true) (accepted := memory_registry_guard_accept descriptors s);
          [exact RANGES|].
        intro answer; apply memory_decision_bind_exact with (known := true) (accepted := memory_registry_guard_accept descriptors s);
          [exact WIDTHS|].
        apply memory_registry_guard_exact; apply ARRAYS; reflexivity.
      * change (command_run decision_test_language
          (conditional decision_test_language (memory_source_header_tree base row bound)
            (decision_bind (MemorySourceRanges.range_guard context bounds)
              (decision_bind width_tree (memory_array_registry_tree descriptors) (Decision false)) (Decision false)) (Decision false)) s flag <-> flag = false).
        rewrite conditional_known by exact PREFIX; cbn.
        change (command_run decision_test_language
          (conditional decision_test_language (MemorySourceRanges.range_guard context bounds)
            (decision_bind width_tree (memory_array_registry_tree descriptors) (Decision false)) (Decision false)) s flag <-> flag = false).
        rewrite conditional_known by exact RANGES; cbn.
        change (command_run decision_test_language
          (conditional decision_test_language width_tree (memory_array_registry_tree descriptors) (Decision false)) s flag <-> flag = false).
        rewrite conditional_known by exact WIDTHS; cbn.
        split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst flag; constructor].
    + change (command_run decision_test_language
        (conditional decision_test_language (memory_source_header_tree base row bound)
          (decision_bind (MemorySourceRanges.range_guard context bounds)
            (decision_bind width_tree (memory_array_registry_tree descriptors) (Decision false)) (Decision false)) (Decision false)) s flag <-> flag = false).
      rewrite conditional_known by exact PREFIX; cbn.
      change (command_run decision_test_language
        (conditional decision_test_language (MemorySourceRanges.range_guard context bounds)
          (decision_bind width_tree (memory_array_registry_tree descriptors) (Decision false)) (Decision false)) s flag <-> flag = false).
      rewrite conditional_known by exact RANGES; cbn.
      split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst flag; constructor].
  - change (command_run decision_test_language
      (conditional decision_test_language (memory_source_header_tree base row bound)
        (decision_bind (MemorySourceRanges.range_guard context bounds)
          (decision_bind width_tree (memory_array_registry_tree descriptors) (Decision false)) (Decision false)) (Decision false)) s flag <-> flag = false).
    rewrite conditional_known by exact PREFIX; cbn.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst flag; constructor].
Qed.
Print Assumptions memory_source_guard_exact.
Definition memory_source_guard_property base descriptors row bound parameters bounds expression s :=
  (entry_temps s) ! row = Some (Vint Int.zero) /\ register_range bound (rectangle_outer_limit base) s /\
  MemoryNested.A.env_within bounds (memory_source_parameter_values (bound::parameters) s) /\
  (0 < memory_source_affine_math
    (memory_source_set_valuation (fun id => Int.signed (temp_word id (entry_temps s))) row 0) expression /\
    forall value, 0 <= value < Int.signed (temp_word bound (entry_temps s)) ->
      0 <= memory_source_affine_math
        (memory_source_set_valuation (fun id => Int.signed (temp_word id (entry_temps s))) row value) expression <= rectangle_stride base) /\
  memory_registry_guard_property descriptors s.
Lemma memory_source_header_sound base row bound s :
  rectangle_layout_valid base -> register_domain row s -> register_domain bound s ->
  memory_source_header_accept base row bound s = true ->
  (entry_temps s) ! row = Some (Vint Int.zero) /\ register_range bound (rectangle_outer_limit base) s.
Proof.
  intros VALID [word ROW] BOUND ACCEPT.
  unfold memory_source_header_accept in ACCEPT; apply andb_true_iff in ACCEPT as [ZERO RANGE].
  split.
  - unfold register_flag,temp_word in ZERO; rewrite ROW in ZERO; apply Int.same_if_eq in ZERO; subst word; exact ROW.
  - apply register_range_sound; [exact (proj1 (rectangle_limits VALID))|exact BOUND|exact RANGE].
Qed.
Theorem memory_source_guard_sound base descriptors row bound parameters bounds expression width_tree s :
  rectangle_layout_valid base ->
  compile_memory_source_width (rectangle_stride base) row (bound::parameters) bounds expression = Some width_tree ->
  memory_source_guard_domain base descriptors row bound (bound::parameters) bounds expression s ->
  memory_source_guard_accept base descriptors row bound (bound::parameters) bounds expression s = true ->
  memory_source_guard_property base descriptors row bound parameters bounds expression s.
Proof.
  intros VALID LOWER [ROW [BOUND [PARAMETERS ARRAYS]]] ACCEPT.
  unfold memory_source_guard_accept in ACCEPT; repeat rewrite andb_true_iff in ACCEPT.
  destruct ACCEPT as [[[HEADER RANGES] WIDTH] ALIAS].
  destruct (@memory_source_header_sound base row bound s VALID ROW BOUND HEADER) as [ZERO NRANGE].
  pose proof (PARAMETERS HEADER) as VIEW.
  assert (WITHIN : MemoryNested.A.env_within bounds (memory_source_parameter_values (bound::parameters) s)).
  { eapply MemorySourceRanges.range_guard_sound with (layout := bound::parameters) (s := s);
      [exact VIEW|apply memory_source_range_exact; [exact VIEW|symmetry; exact RANGES]]. }
  unfold memory_source_guard_property; split; [exact ZERO|]; split; [exact NRANGE|]; split; [exact WITHIN|]; split.
  - destruct s as [ge locals temps memory];
    eapply (@compile_memory_source_width_sound (rectangle_stride base) row bound parameters bounds expression width_tree
      (fun id => Int.signed (temp_word id temps)) ge locals temps memory);
      [exact (proj1 (proj2 NRANGE))|exact LOWER|exact VIEW|exact WITHIN|].
    apply (proj2 (@memory_source_width_exact (rectangle_stride base) row (bound::parameters) bounds expression width_tree
      (Entry ge locals temps memory) LOWER VIEW WITHIN true)); symmetry; exact WIDTH.
  - apply memory_registry_guard_accept_sound; [apply ARRAYS; assumption|exact ALIAS].
Qed.
Print Assumptions memory_source_guard_sound.

Definition memory_source_guard_dimension base descriptors row bound context bounds expression :=
  @positive_dimension clight_entry unit
    (memory_source_guard_domain base descriptors row bound context bounds expression)
    (fun _ s => memory_source_guard_accept base descriptors row bound context bounds expression s = true)
    (fun _ => memory_source_guard_accept base descriptors row bound context bounds expression)
    (fun _ s _ ACCEPT => ACCEPT).
Definition memory_source_guard_primitives base descriptors row bound context bounds expression width_tree
  (LOWER : compile_memory_source_width (rectangle_stride base) row context bounds expression = Some width_tree) :
  check_primitives decision_test_language
    (memory_source_guard_domain base descriptors row bound context bounds expression)
    (decide_atom (memory_source_guard_dimension base descriptors row bound context bounds expression)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language
    (memory_source_guard_domain base descriptors row bound context bounds expression)
    (decide_atom (memory_source_guard_dimension base descriptors row bound context bounds expression))
    (fun _ => memory_source_guard_tree base descriptors row bound context bounds width_tree) (fun _ => Decision true) _ _).
  - intros [] s flag DOMAIN.
    change (decision_run s (memory_source_guard_tree base descriptors row bound context bounds width_tree) flag <->
      flag = checked_valid (decide_atom (memory_source_guard_dimension base descriptors row bound context bounds expression) tt s)).
    rewrite (@memory_source_guard_exact base descriptors row bound context bounds expression width_tree s LOWER DOMAIN flag).
    cbn [memory_source_guard_dimension positive_dimension decide_atom].
    destruct (memory_source_guard_accept base descriptors row bound context bounds expression s); reflexivity.
  - intros [] s flag expected DOMAIN ACCEPT.
    change (decision_run s (Decision true) flag <-> flag = expected).
    cbn [memory_source_guard_dimension positive_dimension decide_atom] in ACCEPT.
    destruct (memory_source_guard_accept base descriptors row bound context bounds expression s); try discriminate.
    inversion ACCEPT; subst expected.
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Defined.
Print Assumptions memory_source_guard_primitives.
