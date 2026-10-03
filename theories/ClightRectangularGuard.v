From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import Values.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightNoWrap ClightCountedLoop ClightRedundantSet ClightPositiveCheck ClightMatrixGuard ClightRectangularStore.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition rectangle_outer_limit d := rectangle_extent d / rectangle_stride d.
Lemma rectangle_limits d : rectangle_layout_valid d ->
  signed_range (rectangle_outer_limit d) /\ signed_range (rectangle_stride d) /\
  0 < rectangle_outer_limit d /\ rectangle_outer_limit d * rectangle_stride d <= rectangle_extent d.
Proof.
  intros [E [EM [S [SE PTR]]]].
  pose proof (Z.div_mod (rectangle_extent d) (rectangle_stride d) ltac:(lia)) as DIV.
  pose proof (Z.mod_pos_bound (rectangle_extent d) (rectangle_stride d) S) as MOD.
  unfold rectangle_outer_limit, signed_range; change Int.min_signed with (-2147483648).
  repeat split; nia.
Qed.
Lemma rectangle_point_bound d N M i j : rectangle_layout_valid d ->
  0 < N <= rectangle_outer_limit d -> 0 < M <= rectangle_stride d ->
  0 <= i < N -> 0 <= j < M -> 0 <= i * rectangle_stride d + j < rectangle_extent d.
Proof.
  intros VALID NBOUND MBOUND I J; pose proof (rectangle_limits VALID) as LIMITS.
  unfold rectangle_layout_valid in VALID; nia.
Qed.

Definition register_positive x s := Int.lt Int.zero (temp_word x (entry_temps s)).
Definition register_at_most x limit s := negb (Int.lt (Int.repr limit) (temp_word x (entry_temps s))).
Definition register_range_flag x limit s := register_positive x s && register_at_most x limit s.
Definition register_range x limit s :=
  register_domain x s /\ 0 < Int.signed (temp_word x (entry_temps s)) <= limit.
Definition register_positive_expr x := Ebinop Olt (Econst_int Int.zero type_int32s)
  (Etempvar x type_int32s) type_int32s.
Definition register_at_most_expr x limit := Ebinop Ole (Etempvar x type_int32s)
  (Econst_int (Int.repr limit) type_int32s) type_int32s.
Definition register_range_tree x limit := Test (register_positive_expr x)
  (Test (register_at_most_expr x limit) (Decision true) (Decision false)) (Decision false).

Lemma register_positive_sound x s : register_positive x s = true ->
  0 < Int.signed (temp_word x (entry_temps s)).
Proof.
  unfold register_positive, Int.lt; rewrite Int.signed_zero.
  destruct (zlt 0 (Int.signed (temp_word x (entry_temps s)))); congruence.
Qed.
Lemma register_range_sound x limit s : signed_range limit -> register_domain x s ->
  register_range_flag x limit s = true -> register_range x limit s.
Proof.
  intros LIMIT DOMAIN ACCEPT; unfold register_range_flag in ACCEPT; apply andb_true_iff in ACCEPT as [POS MAX].
  split; [exact DOMAIN|split; [apply register_positive_sound; exact POS|]].
  unfold register_at_most, Int.lt in MAX; rewrite Int.signed_repr in MAX by exact LIMIT.
  destruct (zlt limit (Int.signed (temp_word x (entry_temps s)))); cbn in MAX; [discriminate|lia].
Qed.
Lemma register_positive_test x s : register_domain x s ->
  expression_test (register_positive_expr x) s (register_positive x s).
Proof.
  intros [n LOOKUP]; exists (Val.of_bool (Int.lt Int.zero n)); split.
  - eapply eval_Ebinop; [constructor|constructor; exact LOOKUP|reflexivity].
  - unfold register_positive, temp_word; rewrite LOOKUP; apply bool_of_bool.
Qed.
Lemma register_at_most_test x limit s : register_domain x s ->
  expression_test (register_at_most_expr x limit) s (register_at_most x limit s).
Proof.
  intros [n LOOKUP]; exists (Val.of_bool (negb (Int.lt (Int.repr limit) n))); split.
  - eapply eval_Ebinop; [constructor; exact LOOKUP|constructor|reflexivity].
  - unfold register_at_most, temp_word; rewrite LOOKUP; apply bool_of_bool.
Qed.
Lemma register_range_tree_run x limit s : register_domain x s ->
  decision_run s (register_range_tree x limit) (register_range_flag x limit s).
Proof.
  intro DOMAIN; unfold register_range_tree, register_range_flag.
  eapply run_test; [apply register_positive_test; exact DOMAIN|].
  destruct (register_positive x s); cbn; [|constructor].
  eapply run_test; [apply register_at_most_test; exact DOMAIN|].
  destruct (register_at_most x limit s); constructor.
Qed.
Lemma register_range_tree_pure x limit : pure_tree (register_range_tree x limit).
Proof. repeat constructor. Qed.

Definition rectangle_guard_domain row bound inner_bound s :=
  register_domain row s /\ register_domain bound s /\
  (register_equals row Int.zero tt s -> 0 < Int.signed (temp_word bound (entry_temps s)) ->
    register_domain inner_bound s).
Definition rectangle_guard_property d row bound inner_bound (_ : unit) s :=
  register_equals row Int.zero tt s /\ register_range bound (rectangle_outer_limit d) s /\
    register_range inner_bound (rectangle_stride d) s.
Definition rectangle_guard_accept d row bound inner_bound (_ : unit) s :=
  register_flag row Int.zero s && register_range_flag bound (rectangle_outer_limit d) s &&
    register_range_flag inner_bound (rectangle_stride d) s.
Definition rectangle_guard_tree d row bound inner_bound :=
  Test (register_guard row Int.zero)
    (Test (register_positive_expr bound)
      (Test (register_at_most_expr bound (rectangle_outer_limit d))
        (register_range_tree inner_bound (rectangle_stride d)) (Decision false))
      (Decision false)) (Decision false).

Lemma rectangle_guard_accept_sound d row bound inner_bound : rectangle_layout_valid d ->
  forall a s, rectangle_guard_domain row bound inner_bound s ->
    rectangle_guard_accept d row bound inner_bound a s = true ->
    rectangle_guard_property d row bound inner_bound a s.
Proof.
  intros VALID [] s [I [N M]] ACCEPT.
  unfold rectangle_guard_accept in ACCEPT; apply andb_true_iff in ACCEPT as [PREFIX INNER].
  apply andb_true_iff in PREFIX as [ITER BOUND].
  pose proof (register_flag_evidence Int.zero I ITER) as ZERO.
  destruct (rectangle_limits VALID) as [NL [ML REST]].
  pose proof (register_range_sound NL N BOUND) as RANGE.
  split; [exact ZERO|split; [exact RANGE|]].
  apply register_range_sound; auto; apply M; [exact ZERO|exact (proj1 (proj2 RANGE))].
Qed.
Lemma rectangle_guard_tree_pure d row bound inner_bound : pure_tree (rectangle_guard_tree d row bound inner_bound).
Proof. unfold rectangle_guard_tree; repeat constructor. Qed.
Lemma rectangle_guard_tree_run d row bound inner_bound s : rectangle_guard_domain row bound inner_bound s ->
  decision_run s (rectangle_guard_tree d row bound inner_bound) (rectangle_guard_accept d row bound inner_bound tt s).
Proof.
  intros [I [N M]]; unfold rectangle_guard_tree, rectangle_guard_accept, register_range_flag.
  eapply run_test; [apply register_expression_test; exact I|].
  destruct (register_flag row Int.zero s) eqn:ITER; cbn; [|constructor].
  eapply run_test; [apply register_positive_test; exact N|].
  destruct (register_positive bound s) eqn:POS; cbn; [|constructor].
  eapply run_test; [apply register_at_most_test; exact N|].
  destruct (register_at_most bound (rectangle_outer_limit d) s); cbn; [|constructor].
  apply register_range_tree_run; apply M; [eapply register_flag_evidence; eauto|apply register_positive_sound; exact POS].
Qed.
Definition rectangle_guard_dimension d row bound inner_bound (VALID : rectangle_layout_valid d) :=
  @positive_dimension clight_entry unit (rectangle_guard_domain row bound inner_bound)
    (rectangle_guard_property d row bound inner_bound) (rectangle_guard_accept d row bound inner_bound)
    (@rectangle_guard_accept_sound d row bound inner_bound VALID).
Definition rectangle_guard_primitives d row bound inner_bound (VALID : rectangle_layout_valid d) :=
  @positive_tree_primitives unit (rectangle_guard_domain row bound inner_bound)
    (rectangle_guard_property d row bound inner_bound) (rectangle_guard_accept d row bound inner_bound)
    (@rectangle_guard_accept_sound d row bound inner_bound VALID)
    (fun _ => rectangle_guard_tree d row bound inner_bound)
    (fun _ => rectangle_guard_tree_pure d row bound inner_bound)
    (fun a s DOMAIN => match a with tt => rectangle_guard_tree_run d DOMAIN end).

Print Assumptions rectangle_guard_primitives.
