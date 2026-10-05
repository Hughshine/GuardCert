From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightCountedLoop CompCertStoreSchedule RectangularSchedule
  ClightRectangularStore ClightRectangularGuard ClightRectangularRegion.
From GuardInterface Require Import ClightReadonlyCellSwap ClightStableLoadBody.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_rectangle_offset d i j := Ptrofs.repr (4*(i*rectangle_stride d+j)).

Lemma loaded_rectangle_store_word d (VALID : rectangle_layout_valid d) block i j before final :
  0 <= i*rectangle_stride d+j < rectangle_extent d ->
  store_action_run (rectangle_action block (rectangle_stride d) (rect_payload d) (i,j)) before final ->
  writable_word before block (loaded_rectangle_offset d i j).
Proof.
  intros RANGE STORE; split; unfold loaded_rectangle_offset; rewrite Ptrofs.unsigned_repr by
    (apply (@rect_small_offset_bound d VALID); lia).
  - eapply Mem.store_valid_access_3; exact STORE.
  - pose proof (@rect_small_offset_bound d VALID (4*(i*rectangle_stride d+j)+4) ltac:(lia)) as END.
    unfold Ptrofs.max_unsigned in END; lia.
Qed.
Lemma loaded_rectangle_storev d (VALID : rectangle_layout_valid d) block i j before final :
  0 <= i*rectangle_stride d+j < rectangle_extent d ->
  store_action_run (rectangle_action block (rectangle_stride d) (rect_payload d) (i,j)) before final ->
  Mem.storev Mint32 before (Vptr block (loaded_rectangle_offset d i j)) (rect_payload d i j) = Some final.
Proof.
  intros RANGE STORE; apply word_storev_from_store.
  - exact (@loaded_rectangle_store_word d VALID block i j before final RANGE STORE).
  - unfold loaded_rectangle_offset; rewrite Ptrofs.unsigned_repr by (apply (@rect_small_offset_bound d VALID); lia).
    exact STORE.
Qed.

Lemma loaded_rectangle_row_permissions d ge locals array i count lower before final :
  counted_iterations (rect_point d ge locals array i) count lower before final ->
  forall block ofs, writable_word final block ofs -> writable_word before block ofs.
Proof.
  intros RUN; induction RUN; intros block ofs WORD; [exact WORD|].
  destruct H as [other [ARRAY STORE]].
  destruct (IHRUN block ofs WORD) as [ACCESS END]; split; [|exact END].
  eapply Mem.store_valid_access_2; [exact STORE|exact ACCESS].
Qed.

Lemma loaded_rectangle_row_words d (VALID : rectangle_layout_valid d) ge locals array block i M count lower before final :
  rect_array_binding d ge locals array block -> 0 <= i < rectangle_outer_limit d -> 0 < M <= rectangle_stride d ->
  0 <= lower -> lower + Z.of_nat count <= M ->
  counted_iterations (rect_point d ge locals array i) count lower before final ->
  forall j, lower <= j < lower + Z.of_nat count -> writable_word before block (loaded_rectangle_offset d i j).
Proof.
  intros ARRAY IR MR LOW HIGH RUN; induction RUN; intros j RANGE; [cbn in RANGE; lia|].
  destruct H as [other [OTHER STORE]].
  assert (SAME : block = other) by (eapply rect_array_binding_unique; eassumption); subst other.
  destruct (Z.eq_dec j x) as [HERE|LATER].
  - subst j; eapply loaded_rectangle_store_word; [exact VALID| |exact STORE].
    apply rectangle_point_bound with (N := rectangle_outer_limit d) (M := M); try assumption.
    + pose proof (rectangle_limits VALID); lia.
    + rewrite Nat2Z.inj_succ in HIGH; lia.
  - assert (WORD : writable_word s1 block (loaded_rectangle_offset d i j)).
    { apply IHRUN; try lia; rewrite Nat2Z.inj_succ in *; lia. }
    destruct WORD as [ACCESS END]; split; [|exact END].
    eapply Mem.store_valid_access_2; [exact STORE|exact ACCESS].
Qed.

Lemma loaded_rectangle_row_load d (VALID : rectangle_layout_valid d) ge locals array block i M count lower
  before final q qofs upper :
  rect_array_binding d ge locals array block -> 0 <= i < rectangle_outer_limit d -> 0 < M <= rectangle_stride d ->
  0 <= lower -> lower + Z.of_nat count <= M ->
  (forall j, 0 <= j < M -> Vptr block (loaded_rectangle_offset d i j) <> Vptr q qofs) ->
  Mem.loadv Mint32 before (Vptr q qofs) = Some upper ->
  counted_iterations (rect_point d ge locals array i) count lower before final ->
  Mem.loadv Mint32 final (Vptr q qofs) = Some upper.
Proof.
  intros ARRAY IR MR LOW HIGH APART READ RUN; induction RUN; [exact READ|].
  destruct H as [other [OTHER STORE]].
  assert (SAME : block = other) by (eapply rect_array_binding_unique; eassumption); subst other.
  apply IHRUN; try lia; try (rewrite Nat2Z.inj_succ in HIGH; lia).
  eapply mint32_load_survives_apart_store.
  - apply loaded_rectangle_storev; [exact VALID| |exact STORE].
    apply rectangle_point_bound with (N := rectangle_outer_limit d) (M := M); try assumption.
    + pose proof (rectangle_limits VALID); lia.
    + rewrite Nat2Z.inj_succ in HIGH; lia.
  - exact READ.
  - apply APART; rewrite Nat2Z.inj_succ in HIGH; lia.
Qed.

Print Assumptions loaded_rectangle_store_word.
Print Assumptions loaded_rectangle_row_permissions.
Print Assumptions loaded_rectangle_row_words.
Print Assumptions loaded_rectangle_row_load.
