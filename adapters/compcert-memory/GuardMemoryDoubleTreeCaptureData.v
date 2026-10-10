From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleSourceTreeData
  GuardMemoryLongControl GuardMemoryLongRangeCapture GuardMemoryLongExpressionCapture
  GuardMemoryLongSourceAffine GuardMemoryRectangularCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_tree_cached_bound bound cache :=
  let parameter:=Ecast (Etempvar (cache (tree_bound_header bound)) memory_signed_int_type) memory_long_type in
  match tree_bound_offset bound with
  | None=>parameter
  | Some offset=>Ebinop Osub parameter (Econst_int offset memory_signed_int_type) memory_long_type end.
Definition double_tree_cached_active start bound cache :=
  Ebinop Olt (double_tree_initial start) (double_tree_cached_bound bound cache) memory_signed_int_type.
Definition double_tree_capture_word bound cache flag lower upper :=
  memory_long_expression_capture (Evar (tree_bound_header bound) memory_long_type)
    (cache (tree_bound_header bound)) flag (lower (tree_bound_header bound)) (upper (tree_bound_header bound)).
Definition double_tree_captured temps bound cache flag input lower upper :=
  memory_long_expression_captured temps (cache (tree_bound_header bound)) flag input
    (lower (tree_bound_header bound)) (upper (tree_bound_header bound)).
Definition double_tree_capture_accept bound input lower upper :=
  memory_long_expression_accept input (lower (tree_bound_header bound)) (upper (tree_bound_header bound)).

(** The check traverses the whole source shape once, with no source assignments
    or loop-counter writes. Each reached range captures its original header;
    the cached comparison decides whether child checks may be evaluated.
    Repeated shared headers are recaptured in this initial implementation. *)
Fixpoint double_tree_capture_code tree cache flag lower upper : statement := match tree with
  | DoubleTreeSkip | DoubleTreePoint _ _=>Sskip
  | DoubleTreeSequence first second=>Ssequence
      (double_tree_capture_code first cache flag lower upper) (double_tree_capture_code second cache flag lower upper)
  | DoubleTreeRange _ _ start bound child=>Sifthenelse (Etempvar flag memory_signed_int_type)
      (Ssequence (double_tree_capture_word bound cache flag lower upper)
        (Sifthenelse (Etempvar flag memory_signed_int_type)
          (Sifthenelse (double_tree_cached_active start bound cache)
            (double_tree_capture_code child cache flag lower upper) Sskip) Sskip)) Sskip
  end.
Definition double_tree_capture_private tree (cache : ident -> ident) (flag : ident) :=
  flag::map cache (double_source_tree_headers tree).
Lemma double_tree_capture_writes tree cache flag lower upper :
  writes_only (double_tree_capture_private tree cache flag) (double_tree_capture_code tree cache flag lower upper).
Proof.
  induction tree; cbn [double_tree_capture_code double_tree_capture_private double_source_tree_headers] in *;
    try solve [constructor].
  - apply writes_sequence.
    + eapply writes_only_weaken; [|exact IHtree1].
      intros key [SAME|MEMBER]; [left; exact SAME|right; cbn [double_source_tree_headers];
        rewrite map_app; apply in_or_app; left; exact MEMBER].
    + eapply writes_only_weaken; [|exact IHtree2].
      intros key [SAME|MEMBER]; [left; exact SAME|right; cbn [double_source_tree_headers];
        rewrite map_app; apply in_or_app; right; exact MEMBER].
  - apply writes_if; [apply writes_sequence|constructor].
    + eapply writes_only_weaken; [|apply memory_long_expression_capture_writes].
      intros key [SAME|[SAME|[]]]; subst key; unfold double_tree_capture_private;
        cbn [double_source_tree_headers map In]; auto.
    + apply writes_if; [apply writes_if|constructor]; [|constructor].
      eapply writes_only_weaken; [|exact IHtree].
      intros key [SAME|MEMBER]; [left; exact SAME|right; cbn [double_source_tree_headers map]; right; exact MEMBER].
Qed.
Lemma double_tree_captured_flag temps bound cache flag input lower upper :
  (double_tree_captured temps bound cache flag input lower upper) ! flag=
    Some (Vint (if double_tree_capture_accept bound input lower upper then Int.one else Int.zero)).
Proof. unfold double_tree_captured,memory_long_expression_captured; apply PTree.gss. Qed.
Lemma double_tree_captured_cache temps bound cache flag input lower upper :
  flag<>cache (tree_bound_header bound) -> double_tree_capture_accept bound input lower upper=true ->
  (double_tree_captured temps bound cache flag input lower upper) ! (cache (tree_bound_header bound))=
    Some (Vint (Int64.loword input)).
Proof.
  intros FRESH ACCEPT; unfold double_tree_captured,memory_long_expression_captured.
  rewrite PTree.gso by congruence; unfold double_tree_capture_accept in ACCEPT.
  rewrite ACCEPT; apply PTree.gss.
Qed.

Print Assumptions double_tree_capture_writes.
Print Assumptions double_tree_captured_flag.
Print Assumptions double_tree_captured_cache.
