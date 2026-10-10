From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCaptureReceipt GuardMemoryDoubleTreeCaptureFacts
  GuardMemoryLongExpressionCapture.
Import ListNotations.
Set Implicit Arguments.

Definition double_tree_cache_distinct headers (cache : ident -> ident) :=
  forall first second, In first headers -> In second headers -> cache first=cache second -> first=second.
Definition double_tree_cache_word ge memory cache (temps : temp_env) header :=
  temps ! (cache header)=Some (Vint (Int.repr (double_tree_observed_value ge memory header))).

(** A later check may recapture an observer already used by an earlier subtree.
    That write stores the same word. Other headers require distinct cache names;
    no defined load of the observer is assumed before this check. *)
Lemma double_tree_captured_preserves_observer ge locals memory temps bound cache flag input lower upper observer block :
  double_global_binding ge locals (tree_bound_header bound) block -> Mem.load Mint64 memory block 0=Some (Vlong input) ->
  cache observer<>flag -> (cache observer=cache (tree_bound_header bound) -> observer=tree_bound_header bound) ->
  double_tree_cache_word ge memory cache temps observer ->
  double_tree_cache_word ge memory cache (double_tree_captured temps bound cache flag input lower upper) observer.
Proof.
  intros BIND LOAD FLAG DISTINCT WORD.
  destruct (peq observer (tree_bound_header bound)) as [SAME|DIFFERENT].
  - subst observer; unfold double_tree_cache_word,double_tree_captured,memory_long_expression_captured in *.
    rewrite PTree.gso by exact FLAG.
    destruct (memory_long_expression_accept input (lower (tree_bound_header bound)) (upper (tree_bound_header bound)));
      [rewrite PTree.gss|exact WORD].
    rewrite memory_long_loword_signed,(@double_tree_observed_load ge locals memory _ block input BIND LOAD); reflexivity.
  - unfold double_tree_cache_word,double_tree_captured; rewrite memory_long_expression_captured_frame; [exact WORD| |exact FLAG].
    intro SAME; apply DIFFERENT,DISTINCT; exact SAME.
Qed.

Theorem double_tree_capture_preserves_cache ge locals memory cache flag lower upper tree temps after accepted :
  double_tree_capture_receipt ge locals memory cache flag lower upper tree temps after accepted ->
  forall headers observer, incl (double_source_tree_headers tree) headers -> double_tree_cache_distinct headers cache ->
  In observer headers -> cache observer<>flag -> double_tree_cache_word ge memory cache temps observer ->
  double_tree_cache_word ge memory cache after observer.
Proof.
  intro RECEIPT; induction RECEIPT; intros headers observer HEADERS DISTINCT MEMBER FLAG WORD; try exact WORD.
  - apply IHRECEIPT2 with (headers:=headers); try assumption.
    + intros header INSIDE; apply HEADERS; cbn; apply in_or_app; right; exact INSIDE.
    + apply IHRECEIPT1 with (headers:=headers); try assumption.
      intros header INSIDE; apply HEADERS; cbn; apply in_or_app; left; exact INSIDE.
  - eapply double_tree_captured_preserves_observer; [exact H0|exact H1|exact FLAG| |exact WORD].
    apply DISTINCT; [exact MEMBER|apply HEADERS; cbn; left; reflexivity].
  - eapply double_tree_captured_preserves_observer; [exact H0|exact H1|exact FLAG| |exact WORD].
    apply DISTINCT; [exact MEMBER|apply HEADERS; cbn; left; reflexivity].
  - apply IHRECEIPT with (headers:=headers); try assumption.
    + intros header INSIDE; apply HEADERS; cbn; right; exact INSIDE.
    + eapply double_tree_captured_preserves_observer; [exact H0|exact H1|exact FLAG| |exact WORD].
      apply DISTINCT; [exact MEMBER|apply HEADERS; cbn; left; reflexivity].
Qed.

Print Assumptions double_tree_captured_preserves_observer.
Print Assumptions double_tree_capture_preserves_cache.
