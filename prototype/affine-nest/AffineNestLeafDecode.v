From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryNaryCompute
  GuardMemoryWindowCells GuardMemoryIntervalBox.
From GuardAffineNest Require Import AffineNestValuation AffineNestLeafModel AffineNestLeafLoop.
Import ListNotations.
Set Implicit Arguments.

Definition affine_checked_leaf_code (coordinates geometry scalars : list ident) operations :=
  L.Seq(affine_leaf_sequence (length coordinates) (length(geometry++scalars))
    (map memory_nary_compute_instruction operations)).

Theorem affine_checked_leaf_decode source bounds lower upper coordinates geometry scalars pointers operations
  (certificate:affine_leaf_certificate source bounds lower upper (coordinates++geometry) scalars pointers operations)
  fe ge locals valuation initial temps memory after final tail :
  affine_word_view (coordinates++(geometry++scalars)) valuation temps ->
  temp_agree pointers initial temps -> interval_ranges bounds(map valuation(coordinates++geometry)) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  L.loop_semantics (affine_checked_leaf_code coordinates geometry scalars operations)
    (map valuation(rev coordinates++(geometry++scalars))++tail)
    (RuntimeState(window_multi_pointer_locations initial lower upper) memory)
    (RuntimeState(window_multi_pointer_locations initial lower upper) final).
Proof.
  intros WORDS POINTERS RANGES SOURCE.
  destruct (@affine_leaf_real_memory_decode source bounds lower upper (coordinates++geometry) scalars
    pointers operations certificate fe ge locals valuation initial temps memory after final
    RANGES ltac:(rewrite <-app_assoc; exact WORDS) POINTERS SOURCE) as [POINT EXIT].
  unfold affine_checked_leaf_code.
  rewrite map_app,map_rev,<-app_assoc.
  replace (length coordinates) with (length(map valuation coordinates)) by apply length_map.
  replace (length(geometry++scalars)) with (length(map valuation(geometry++scalars))) by apply length_map.
  apply(proj2(@affine_leaf_sequence_semantics (map memory_nary_compute_instruction operations)
    (map valuation coordinates) (map valuation(geometry++scalars)) tail _ _)).
  rewrite <-map_app,app_assoc; exact POINT.
Qed.
Print Assumptions affine_checked_leaf_code.
Print Assumptions affine_checked_leaf_decode.
