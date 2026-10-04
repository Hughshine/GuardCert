From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryScalarTiling GuardMemoryLoopTrace
  GuardMemoryTileRangeTrimming GuardMemoryBoundedSourceTiling GuardMemoryBoundedSourceChecker
  GuardMemoryStartedScalarTiling GuardMemoryArrayBackend.
Import ListNotations.
Local Open Scope Z_scope.
Lemma window_negative_range_split {A} (events : Z -> list A) count bound :
  0 <= bound ->
  flat_map events (Zrange (-Z.of_nat count) bound) =
  flat_map events (Zrange (-Z.of_nat count) 0) ++ flat_map events (Zrange 0 bound).
Proof.
  intro BOUND; induction count as [|count IH].
  - change (flat_map events (Zrange 0 bound) = [] ++ flat_map events (Zrange 0 bound)); reflexivity.
  - pose proof (Nat2Z.is_nonneg count) as NONNEG.
    rewrite (Zrange_begin (-Z.of_nat (S count)) bound) by (rewrite Nat2Z.inj_succ; lia).
    rewrite (Zrange_begin (-Z.of_nat (S count)) 0) by (rewrite Nat2Z.inj_succ; lia).
    replace (-Z.of_nat (S count)+1) with (-Z.of_nat count) by (rewrite Nat2Z.inj_succ; lia).
    cbn [flat_map]; rewrite IH,app_assoc; reflexivity.
Qed.
Lemma window_nonpositive_range_split {A} (events : Z -> list A) lower bound :
  lower <= 0 -> 0 <= bound ->
  flat_map events (Zrange lower bound) =
  flat_map events (Zrange lower 0) ++ flat_map events (Zrange 0 bound).
Proof.
  intros LOWER BOUND.
  replace lower with (-Z.of_nat (Z.to_nat (-lower))) by (rewrite Z2Nat.id by lia; lia).
  apply window_negative_range_split; exact BOUND.
Qed.
Lemma window_guarded_tile_range {A} (events : Z -> list A) lower bound width :
  lower <= 0 -> 0 < bound -> 0 < width ->
  flat_map (fun tile => if width*tile <=? bound-1 then events tile else []) (Zrange lower bound) =
  flat_map (fun tile => if width*tile <=? bound-1 then events tile else [])
    (Zrange lower ((bound+width-1)/width)).
Proof.
  intros LOWER BOUND WIDTH.
  rewrite window_nonpositive_range_split by lia.
  rewrite (window_nonpositive_range_split _ lower ((bound+width-1)/width));
    [|exact LOWER|apply Z.div_pos; lia].
  rewrite memory_guarded_tile_range by assumption; reflexivity.
Qed.
Definition window_tiled dimensions scalars instructions root_lower bi bj (efficient : bool) :=
  L.Loop (L.Constant (root_lower/bi))
    (if efficient then L.Div (L.Sum (L.Var 0) (L.Constant (bi-1))) bi else L.Var 0)
    (L.Guard (L.LE (L.Mult bi (L.Var 0)) (L.Sum (L.Var 1) (L.Constant (-1))))
      (memory_started_scalar_tile_columns dimensions scalars instructions bi bj efficient)).
Definition window_tiled_loop dimensions scalars instructions root_lower bi bj :=
  window_tiled dimensions scalars instructions root_lower bi bj true.
Theorem window_tile_trimming dimensions scalars instructions root_lower bi bj N M parameters before after :
  root_lower <= 0 -> 0 < N -> 0 < M -> 0 < bi -> 0 < bj ->
  (L.loop_semantics (window_tiled dimensions scalars instructions root_lower bi bj false) (N::M::parameters) before after <->
    L.loop_semantics (window_tiled_loop dimensions scalars instructions root_lower bi bj) (N::M::parameters) before after).
Proof.
  intros LOWER NP MP BI BJ; rewrite !memory_loop_trace_correct.
  assert (BLOCK_LOWER : root_lower/bi <= 0) by (apply Z.div_le_upper_bound; nia).
  assert (TRACE : memory_loop_trace (window_tiled dimensions scalars instructions root_lower bi bj false) (N::M::parameters) =
    memory_loop_trace (window_tiled_loop dimensions scalars instructions root_lower bi bj) (N::M::parameters)).
  { unfold window_tiled_loop,window_tiled.
    change (flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_started_scalar_tile_columns dimensions scalars instructions bi bj false) (ti::N::M::parameters) else []) (Zrange (root_lower/bi) N) =
      flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_started_scalar_tile_columns dimensions scalars instructions bi bj true) (ti::N::M::parameters) else []) (Zrange (root_lower/bi) ((N+(bi-1))/bi))).
    replace (N+ -1) with (N-1) by lia; replace (N+(bi-1)) with (N+bi-1) by lia.
    rewrite (@window_guarded_tile_range _
      (fun ti => memory_loop_trace (memory_started_scalar_tile_columns dimensions scalars instructions bi bj false) (ti::N::M::parameters))
      (root_lower/bi) N bi BLOCK_LOWER NP BI).
    apply flat_map_ext; intro ti; destruct (bi*ti <=? N-1); [|reflexivity].
    apply memory_started_scalar_tile_columns_trimming; assumption. }
  rewrite TRACE; reflexivity.
Qed.
Definition checked_window_tiling bounds source_loop dimensions scalars instructions context arrays root_lower bi bj :=
  checked_memory_bounded_source_tiling bounds source_loop
    (window_tiled dimensions scalars instructions root_lower bi bj false) context arrays
    (repeat (memory_scalar_tiling_witness dimensions (length context) bi bj) (length instructions)).
Theorem checked_window_tiling_correct bounds source_loop dimensions scalars instructions context arrays root_lower bi bj first_cap second_cap :
  nth_error bounds O = Some (MemoryNested.A.Interval 1 first_cap) ->
  nth_error bounds 1%nat = Some (MemoryNested.A.Interval 1 second_cap) ->
  (2 <= length context)%nat -> root_lower <= 0 -> 0 < bi -> 0 < bj ->
  mayReturn (checked_window_tiling bounds source_loop dimensions scalars instructions context arrays root_lower bi bj) true ->
  memory_bounded_source_certificate bounds source_loop context (window_tiled_loop dimensions scalars instructions root_lower bi bj).
Proof.
  intros FIRST SECOND CONTEXT LOWER BI BJ CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  assert (ARITY : (2 <= length parameters)%nat) by (rewrite LENGTH; exact CONTEXT).
  destruct parameters as [|N [|M parameters]]; cbn in ARITY; try (exfalso; lia).
  assert (NP : 0 < N) by (pose proof (WITHIN O _ FIRST) as RANGE; unfold MemoryNested.A.contains in RANGE; cbn in RANGE; lia).
  assert (MP : 0 < M) by (pose proof (WITHIN 1%nat _ SECOND) as RANGE; unfold MemoryNested.A.contains in RANGE; cbn in RANGE; lia).
  apply (proj1 (@window_tile_trimming dimensions scalars instructions root_lower bi bj N M parameters before after LOWER NP MP BI BJ)).
  unfold checked_window_tiling in CHECK.
  exact (@checked_memory_bounded_source_tiling_correct bounds source_loop
    (window_tiled dimensions scalars instructions root_lower bi bj false) context arrays
    (repeat (memory_scalar_tiling_witness dimensions (length context) bi bj) (length instructions))
    CHECK (N::M::parameters) before after LENGTH WITHIN NONALIAS SOURCE).
Qed.
Print Assumptions window_guarded_tile_range.
Print Assumptions window_tile_trimming.
Print Assumptions checked_window_tiling_correct.
