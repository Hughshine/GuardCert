From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From Guard Require Import ClightCountedLoop.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryScalarChecker GuardMemoryCanonicalPrepare.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Numeric setup's existing cap evidence licenses the new machine bounds.
    No caller-side range certificate or additional runtime probe is required. *)
Theorem canonical_static_bounds_ranges cap counts values :
  2*cap-1 <= Int.max_signed ->
  MemoryNested.A.env_within (memory_scalar_static_bounds (length counts) cap (length values)) (counts++values) ->
  Forall canonical_count_range counts.
Proof.
  intros CAP; induction counts as [|count counts IH]; intro WITHIN; [constructor|].
  assert (HEAD : 1 <= count <= cap).
  { specialize (WITHIN O (MemoryNested.A.Interval 1 cap) eq_refl); exact WITHIN. }
  constructor.
  - unfold canonical_count_range,signed_range; pose proof Int.min_signed_neg; lia.
  - apply IH; intros index interval POSITION.
    specialize (WITHIN (S index) interval); apply WITHIN; exact POSITION.
Qed.

Print Assumptions canonical_static_bounds_ranges.
