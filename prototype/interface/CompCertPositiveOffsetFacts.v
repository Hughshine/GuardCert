From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
Local Open Scope Z_scope.

(** A profile of the actual word result can imply an arithmetic presumption.
    This rule requires a nonnegative signed offset; it is not a rule for
    arbitrary expressions or a replacement for evaluating the source bound. *)
Theorem nonnegative_added_offset_exact raw delta :
  0 <= Int.signed delta -> 0 <= Int.signed(Int.add raw delta) ->
  Int.signed(Int.add raw delta) = Int.signed raw + Int.signed delta.
Proof.
  intros DELTA RESULT.
  pose proof(Int.signed_range raw) as RAW.
  pose proof(Int.signed_range delta) as OFFSET.
  rewrite Int.add_signed in *.
  set (sum := Int.signed raw + Int.signed delta) in *.
  destruct(Z_le_dec sum Int.max_signed) as [SAFE|WRAP].
  - apply Int.signed_repr. unfold sum; lia.
  - assert(LOW:0<=sum) by
      (unfold Int.max_signed in WRAP; pose proof Int.half_modulus_pos; lia).
    assert(HIGH:sum<Int.modulus).
    { unfold sum; unfold Int.max_signed in RAW,OFFSET.
      rewrite Int.half_modulus_modulus; lia. }
    rewrite Int.signed_repr_eq, Z.mod_small in RESULT by lia.
    rewrite zlt_false in RESULT by (unfold Int.max_signed in WRAP; lia).
    lia.
Qed.

Corollary nonnegative_added_offset_in_range raw delta :
  0 <= Int.signed delta -> 0 <= Int.signed(Int.add raw delta) ->
  Int.min_signed <= Int.signed raw + Int.signed delta <= Int.max_signed.
Proof.
  intros DELTA RESULT; rewrite <- (nonnegative_added_offset_exact raw delta DELTA RESULT).
  apply Int.signed_range.
Qed.

Definition positive_offset_profile raw delta cap : bool :=
  (0 <=? Int.signed delta) &&
  (1 <=? Int.signed(Int.add raw delta)) &&
  (Int.signed(Int.add raw delta) <=? cap).

Theorem positive_offset_profile_sound raw delta cap :
  positive_offset_profile raw delta cap = true ->
  Int.signed(Int.add raw delta) = Int.signed raw + Int.signed delta /\
  1 <= Int.signed raw + Int.signed delta <= cap /\
  Int.min_signed <= Int.signed raw + Int.signed delta <= Int.max_signed.
Proof.
  unfold positive_offset_profile; rewrite !andb_true_iff, !Z.leb_le.
  intros [[DELTA POSITIVE] CAP].
  assert(EXACT:Int.signed(Int.add raw delta)=Int.signed raw+Int.signed delta)
    by (apply nonnegative_added_offset_exact; lia).
  split; [exact EXACT|split; [lia|]].
  rewrite <- EXACT; apply Int.signed_range.
Qed.

Example positive_offset_one_accepts_raw_zero :
  positive_offset_profile Int.zero Int.one 32 = true.
Proof. vm_compute; reflexivity. Qed.

Example positive_offset_one_rejects_wrapped_root :
  positive_offset_profile(Int.repr Int.max_signed) Int.one 32 = false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions nonnegative_added_offset_exact.
Print Assumptions nonnegative_added_offset_in_range.
Print Assumptions positive_offset_profile_sound.
Print Assumptions positive_offset_one_accepts_raw_zero.
Print Assumptions positive_offset_one_rejects_wrapped_root.
