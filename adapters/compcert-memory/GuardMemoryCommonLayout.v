From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Integers.
From Guard Require Import ClightRectangularStore ClightRectangularGuard.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_common_layout first second :=
  let stride := Z.min (rectangle_stride first) (rectangle_stride second) in
  let rows := Z.min (rectangle_outer_limit first) (rectangle_outer_limit second) in
  RectangleShape (rows*stride) stride 0 0.
Lemma memory_common_layout_facts first second :
  rectangle_layout_valid first -> rectangle_layout_valid second ->
  0 < rectangle_stride (memory_common_layout first second) /\
  rectangle_stride (memory_common_layout first second) <= rectangle_stride first /\
  rectangle_stride (memory_common_layout first second) <= rectangle_stride second /\
  rectangle_outer_limit (memory_common_layout first second) =
    Z.min (rectangle_outer_limit first) (rectangle_outer_limit second) /\
  rectangle_layout_valid (memory_common_layout first second).
Proof.
  intros FIRST SECOND.
  pose proof (rectangle_limits FIRST) as [_ [_ [FP FB]]].
  pose proof (rectangle_limits SECOND) as [_ [_ [SP SB]]].
  destruct FIRST as [FE [FM [FS [FSE FPOINTER]]]].
  destruct SECOND as [SE [SM [SS [SSE SPOINTER]]]].
  pose proof (Z.le_min_l (rectangle_stride first) (rectangle_stride second)) as FSTRIDE.
  pose proof (Z.le_min_r (rectangle_stride first) (rectangle_stride second)) as SSTRIDE.
  pose proof (Z.le_min_l (rectangle_outer_limit first) (rectangle_outer_limit second)) as FROWS.
  pose proof (Z.le_min_r (rectangle_outer_limit first) (rectangle_outer_limit second)) as SROWS.
  assert (STRIDE : 0 < Z.min (rectangle_stride first) (rectangle_stride second)) by (apply Z.min_glb_lt; assumption).
  assert (ROWS : 0 < Z.min (rectangle_outer_limit first) (rectangle_outer_limit second)) by (apply Z.min_glb_lt; assumption).
  assert (EXTENT : Z.min (rectangle_outer_limit first) (rectangle_outer_limit second)*
    Z.min (rectangle_stride first) (rectangle_stride second) <= rectangle_extent first) by nia.
  unfold memory_common_layout; cbn [rectangle_stride rectangle_extent].
  split; [exact STRIDE|]; split; [exact FSTRIDE|]; split; [exact SSTRIDE|]; split.
  - unfold rectangle_outer_limit; cbn [rectangle_extent rectangle_stride].
    rewrite Z.div_mul by lia; reflexivity.
  - unfold rectangle_layout_valid; cbn [rectangle_extent rectangle_stride]; repeat split; nia.
Qed.
Lemma memory_common_layout_valid first second :
  rectangle_layout_valid first -> rectangle_layout_valid second -> rectangle_layout_valid (memory_common_layout first second).
Proof. intros FIRST SECOND; exact (proj2 (proj2 (proj2 (proj2 (memory_common_layout_facts FIRST SECOND))))). Qed.
Lemma memory_common_layout_points first second N i j :
  rectangle_layout_valid first -> rectangle_layout_valid second ->
  0 < N <= rectangle_outer_limit (memory_common_layout first second) ->
  0 <= i < N -> 0 <= j < rectangle_stride (memory_common_layout first second) ->
  0 <= i*rectangle_stride first+j < rectangle_extent first /\
    0 <= i*rectangle_stride second+j < rectangle_extent second.
Proof.
  intros FIRST SECOND NB I J.
  destruct (memory_common_layout_facts FIRST SECOND) as [STRIDE [FSTRIDE [SSTRIDE [ROWS VALID]]]].
  pose proof (Z.le_min_l (rectangle_outer_limit first) (rectangle_outer_limit second)) as FN.
  pose proof (Z.le_min_r (rectangle_outer_limit first) (rectangle_outer_limit second)) as SN.
  rewrite ROWS in NB; split;
    [eapply rectangle_point_bound with (M := rectangle_stride (memory_common_layout first second)) (N := N); eauto; lia|
     eapply rectangle_point_bound with (M := rectangle_stride (memory_common_layout first second)) (N := N); eauto; lia].
Qed.
Print Assumptions memory_common_layout_facts.
Print Assumptions memory_common_layout_points.
