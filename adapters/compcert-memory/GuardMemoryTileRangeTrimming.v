From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryTiledRectangles.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma memory_trimmed_flat_range {A} (events : Z -> list A) count :
  forall cut, 0 <= cut <= Z.of_nat count ->
  (forall x, cut <= x < Z.of_nat count -> events x = []) ->
  flat_map events (Zrange 0 (Z.of_nat count)) = flat_map events (Zrange 0 cut).
Proof.
  induction count as [|count IH]; intros cut BOUND EMPTY.
  - assert (ZERO : cut = 0) by (cbn in BOUND; lia); subst cut; reflexivity.
  - destruct (Z.eq_dec cut (Z.of_nat (S count))) as [->|DIFFERENT]; [reflexivity|].
    assert (BOUND' : 0 <= cut <= Z.of_nat count) by (rewrite Nat2Z.inj_succ in *; lia).
    rewrite Zrange_end by (rewrite Nat2Z.inj_succ; lia).
    replace (Z.of_nat (S count)-1) with (Z.of_nat count) by (rewrite Nat2Z.inj_succ; lia).
    rewrite flat_map_app; cbn; rewrite EMPTY by (rewrite Nat2Z.inj_succ; lia); rewrite app_nil_r.
    apply IH; [exact BOUND'|intros; apply EMPTY; rewrite Nat2Z.inj_succ; lia].
Qed.
Lemma memory_tile_count_bounds bound width :
  0 < bound -> 0 < width ->
  0 <= rectangle_tile_count bound width <= bound /\ bound <= width*rectangle_tile_count bound width.
Proof.
  intros POS WIDTH; unfold rectangle_tile_count.
  pose proof (Z.div_mod (bound+width-1) width ltac:(lia)) as DIV.
  pose proof (Z.mod_pos_bound (bound+width-1) width WIDTH) as MOD.
  assert (LOWER : 0 <= (bound+width-1)/width) by (apply Z.div_pos; lia).
  assert (UPPER : (bound+width-1)/width <= bound).
  { apply Z.div_le_upper_bound; nia. }
  split; [lia|nia].
Qed.
Lemma memory_guarded_tile_range {A} (events : Z -> list A) bound width :
  0 < bound -> 0 < width ->
  flat_map (fun tile => if width*tile <=? bound-1 then events tile else []) (Zrange 0 bound) =
  flat_map (fun tile => if width*tile <=? bound-1 then events tile else [])
    (Zrange 0 (rectangle_tile_count bound width)).
Proof.
  intros POS WIDTH; destruct (@memory_tile_count_bounds bound width POS WIDTH) as [COUNT CEIL].
  replace bound with (Z.of_nat (Z.to_nat bound)) at 1 by (rewrite Z2Nat.id; lia).
  apply memory_trimmed_flat_range; [rewrite Z2Nat.id by lia; exact COUNT|].
  intros tile RANGE; rewrite Z2Nat.id in RANGE by lia.
  assert (FALSE : (width*tile <=? bound-1) = false) by (apply Z.leb_gt; nia).
  rewrite FALSE; reflexivity.
Qed.
Print Assumptions memory_guarded_tile_range.
