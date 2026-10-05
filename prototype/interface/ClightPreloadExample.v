From Stdlib Require Import Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite.
Set Implicit Arguments.

Definition preload_word_type := Tint I32 Unsigned noattr.
Definition count_test count := Etempvar count preload_word_type.
Definition bound_load pointer :=
  Ederef (Etempvar pointer (Tpointer preload_word_type noattr)) preload_word_type.
Definition word_truth x := negb (Int.eq x Int.zero).

Definition loaded_word pointer entry := exists b offset x,
  (entry_temps entry) ! pointer = Some (Vptr b offset) /\
  Mem.loadv Mint32 (entry_memory entry) (Vptr b offset) = Some (Vint x).

(** Only a source-active path needs the pointer and load. In particular an
    empty outer loop may enter with an entirely uninitialized pointer. *)
Definition preload_domain count pointer entry := exists x,
  (entry_temps entry) ! count = Some (Vint x) /\
  (word_truth x = true -> loaded_word pointer entry).

Definition lazy_preload_tree count pointer :=
  Test (count_test count) (Test (bound_load pointer) (Decision true) (Decision false)) (Decision false).
Definition preload_premise count pointer entry :=
  expression_test (count_test count) entry true /\ expression_test (bound_load pointer) entry true.

Lemma count_test_exact count entry x :
  (entry_temps entry) ! count = Some (Vint x) -> forall answer,
  expression_test (count_test count) entry answer <-> answer = word_truth x.
Proof.
  intros LOOKUP answer; split.
  - intros [value [EVAL BOOL]]; apply scalar_temp_inv in EVAL.
    assert (SAME : value = Vint x) by congruence; subst value.
    change (Some (word_truth x) = Some answer) in BOOL; congruence.
  - intro SAME; subst answer; exists (Vint x); split.
    + apply eval_Etempvar; exact LOOKUP.
    + reflexivity.
Qed.

Lemma bound_load_value pointer entry b offset x :
  (entry_temps entry) ! pointer = Some (Vptr b offset) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr b offset) = Some (Vint x) ->
  forall value, eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry)
    (entry_memory entry) (bound_load pointer) value <-> value = Vint x.
Proof.
  intros LOOKUP LOAD value; split.
  - intro RUN; unfold bound_load in RUN; inversion RUN; subst.
    match goal with LV : eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ => inversion LV; subst end.
    match goal with EV : eval_expr _ _ _ _ (Etempvar _ _) _ |- _ => apply scalar_temp_inv in EV end.
    match goal with EV : (entry_temps entry) ! pointer = Some (Vptr ?block ?ofs) |- _ =>
      assert (SAME : Vptr block ofs = Vptr b offset) by congruence; injection SAME; intros; subst end.
    match goal with DEREF : deref_loc _ _ _ _ _ _ |- _ => inversion DEREF; subst; try discriminate end.
    match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
    congruence.
  - intro SAME; subst value; apply eval_Elvalue with (loc := b) (ofs := offset) (bf := Full).
    + apply eval_Ederef, eval_Etempvar; exact LOOKUP.
    + apply deref_loc_value with (chunk := Mint32); [reflexivity|exact LOAD].
Qed.

Lemma bound_load_test_exact pointer entry b offset x :
  (entry_temps entry) ! pointer = Some (Vptr b offset) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr b offset) = Some (Vint x) -> forall answer,
  expression_test (bound_load pointer) entry answer <-> answer = word_truth x.
Proof.
  intros LOOKUP LOAD answer; split.
  - intros [value [EVAL BOOL]].
    apply (proj1 (bound_load_value pointer entry LOOKUP LOAD value)) in EVAL; subst value.
    change (Some (word_truth x) = Some answer) in BOOL; congruence.
  - intro SAME; subst answer; exists (Vint x); split; [|reflexivity].
    apply (proj2 (bound_load_value pointer entry LOOKUP LOAD (Vint x))); reflexivity.
Qed.

Theorem lazy_preload_safe count pointer entry : preload_domain count pointer entry ->
  readonly_tree_safe entry (lazy_preload_tree count pointer).
Proof.
  intros [x [LOOKUP LOAD_IF_ACTIVE]]; cbn [lazy_preload_tree readonly_tree_safe]; split.
  - exists (word_truth x); apply (proj2 (count_test_exact count entry LOOKUP _)); reflexivity.
  - intros active CHECK; apply (proj1 (count_test_exact count entry LOOKUP active)) in CHECK.
    subst active; destruct (word_truth x) eqn:ACTIVE; cbn; [|constructor].
    destruct (LOAD_IF_ACTIVE eq_refl) as [b [offset [value [POINTER LOAD]]]].
    split.
    + exists (word_truth value); apply (proj2 (bound_load_test_exact pointer entry POINTER LOAD _)); reflexivity.
    + intros accepted _; destruct accepted; constructor.
Qed.

Definition lazy_preload_condition fe O (observe : fragment_observation -> O -> Prop) count pointer :
  readonly_condition (readonly_clight_host fe observe) (preload_domain count pointer)
    (preload_premise count pointer) (lazy_preload_tree count pointer).
Proof.
  constructor.
  - intros entry DOMAIN; apply lazy_preload_safe; exact DOMAIN.
  - intros entry DOMAIN; destruct (@readonly_tree_available (lazy_preload_tree count pointer) entry
      (@lazy_preload_safe count pointer entry DOMAIN)) as [accepted RUN].
    exists accepted, entry; split; [exact RUN|reflexivity].
  - intros entry accepted checked DOMAIN [RUN SAME]; split; [exact SAME|].
    intro ACCEPT; subst accepted; inversion RUN; subst.
    match goal with CHECK : expression_test (count_test count) entry ?active |- _ => destruct active end.
    + match goal with LEAF : decision_run entry (Test _ _ _) true |- _ => inversion LEAF; subst end.
      match goal with CHECK : expression_test (bound_load pointer) entry ?answer |- _ => destruct answer end.
      * split; assumption.
      * match goal with DEAD : decision_run _ (Decision false) true |- _ => inversion DEAD end.
    + match goal with DEAD : decision_run _ (Decision false) true |- _ => inversion DEAD end.
Defined.

Theorem empty_path_preload_refuses count pointer entry :
  (entry_temps entry) ! count = Some (Vint Int.zero) ->
  decision_run entry (lazy_preload_tree count pointer) false.
Proof.
  intro LOOKUP; apply run_test with (b := false).
  - apply (proj2 (count_test_exact count entry LOOKUP false)); reflexivity.
  - constructor.
Qed.

Theorem empty_path_needs_no_pointer count pointer entry :
  (entry_temps entry) ! count = Some (Vint Int.zero) -> preload_domain count pointer entry.
Proof.
  intro LOOKUP; exists Int.zero; split; [exact LOOKUP|].
  intro IMPOSSIBLE; discriminate IMPOSSIBLE.
Qed.

Lemma accepted_preload_is_unique count pointer entry :
  preload_domain count pointer entry -> preload_premise count pointer entry ->
  forall accepted, decision_run entry (lazy_preload_tree count pointer) accepted -> accepted = true.
Proof.
  intros [x [LOOKUP LOAD_IF_ACTIVE]] [COUNT BOUND] accepted RUN.
  assert (ACTIVE : word_truth x = true).
  { symmetry; apply (proj1 (count_test_exact count entry LOOKUP true)); exact COUNT. }
  destruct (LOAD_IF_ACTIVE ACTIVE) as [b [offset [value [POINTER LOAD]]]].
  assert (POSITIVE : word_truth value = true).
  { symmetry; apply (proj1 (bound_load_test_exact pointer entry POINTER LOAD true)); exact BOUND. }
  inversion RUN; subst.
  match goal with CHECK : expression_test (count_test count) entry ?choice |- _ =>
    apply (proj1 (count_test_exact count entry LOOKUP choice)) in CHECK;
    rewrite ACTIVE in CHECK; subst choice end.
  match goal with CHILD : decision_run entry (Test _ _ _) accepted |- _ => inversion CHILD; subst end.
  match goal with CHECK : expression_test (bound_load pointer) entry ?choice |- _ =>
    apply (proj1 (bound_load_test_exact pointer entry POINTER LOAD choice)) in CHECK;
    rewrite POSITIVE in CHECK; subst choice end.
  match goal with LEAF : decision_run entry (Decision true) accepted |- _ => inversion LEAF; reflexivity end.
Qed.

(** A genuine conditional branch rewrite on actual Clight statements. The
    supplied body can be a loop; this theorem concerns terminating executions.
    Region progress and its embedding in whole-program semantics are separate. *)
Theorem guarded_preload_branch_equivalent fe O (observe : fragment_observation -> O -> Prop)
  count pointer body :
  local_equivalence (readonly_clight_host fe observe) (preload_domain count pointer)
    (guarded_rewrite (readonly_clight_host fe observe)
      (tree_statement (lazy_preload_tree count pointer) body Sskip) body
      (lazy_preload_tree count pointer))
    (tree_statement (lazy_preload_tree count pointer) body Sskip).
Proof.
  apply guarded_rewrite_equivalent with (premise := preload_premise count pointer).
  - apply lazy_preload_condition.
  - intros entry observed [DOMAIN PREMISE]; split.
    + intro BODY; apply (proj2 (select_exact (readonly_clight_host fe observe)
        (lazy_preload_tree count pointer) body Sskip entry observed)).
      exists true, entry; split; [split; [|reflexivity]|exact BODY].
      destruct PREMISE as [COUNT BOUND]; apply run_test with (b := true); [exact COUNT|].
      apply run_test with (b := true); [exact BOUND|constructor].
    + intro SOURCE; apply (proj1 (select_exact (readonly_clight_host fe observe)
        (lazy_preload_tree count pointer) body Sskip entry observed)) in SOURCE.
      destruct SOURCE as [accepted [checked [[RUN SAME] BODY]]]; subst checked.
      pose proof (@accepted_preload_is_unique count pointer entry DOMAIN PREMISE accepted RUN) as TRUE.
      subst accepted; exact BODY.
Qed.

Print Assumptions count_test_exact.
Print Assumptions bound_load_value.
Print Assumptions bound_load_test_exact.
Print Assumptions lazy_preload_safe.
Print Assumptions lazy_preload_condition.
Print Assumptions empty_path_preload_refuses.
Print Assumptions empty_path_needs_no_pointer.
Print Assumptions accepted_preload_is_unique.
Print Assumptions guarded_preload_branch_equivalent.
