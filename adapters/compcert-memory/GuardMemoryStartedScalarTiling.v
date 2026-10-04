From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryScalarTiling GuardMemoryLoopTrace GuardMemoryTileRangeTrimming GuardMemoryBoundedSourceTiling GuardMemoryBoundedSourceChecker GuardMemoryArrayBackend.
Import ListNotations.
Local Open Scope Z_scope.
Definition memory_started_scalar_tile_points dimensions scalars instructions bi bj :=
  L.Loop (L.Mult bi (L.Var 1)) (L.Sum (L.Mult bi (L.Var 1)) (L.Constant bi))
    (L.Guard (L.And (L.LE (L.Var (dimensions+scalars+3)%nat) (L.Var 0))
      (L.LE (L.Var 0) (L.Sum (L.Var 3) (L.Constant (-1)))))
      (L.Loop (L.Mult bj (L.Var 1)) (L.Sum (L.Mult bj (L.Var 1)) (L.Constant bj))
        (L.Guard (L.LE (L.Var 0) (L.Sum (L.Var 5) (L.Constant (-1))))
          (memory_scalar_tiled_inner 2 (dimensions-2)%nat scalars instructions)))).
Definition memory_started_scalar_tile_columns dimensions scalars instructions bi bj (efficient : bool) :=
  L.Loop (L.Constant 0) (if efficient then L.Div (L.Sum (L.Var 2) (L.Constant (bj-1))) bj else L.Var 2)
    (L.Guard (L.LE (L.Mult bj (L.Var 0)) (L.Sum (L.Var 3) (L.Constant (-1))))
      (memory_started_scalar_tile_points dimensions scalars instructions bi bj)).
Definition memory_started_scalar_tiled dimensions scalars instructions bi bj (efficient : bool) :=
  L.Loop (L.Constant 0) (if efficient then L.Div (L.Sum (L.Var 0) (L.Constant (bi-1))) bi else L.Var 0)
    (L.Guard (L.LE (L.Mult bi (L.Var 0)) (L.Sum (L.Var 1) (L.Constant (-1))))
      (memory_started_scalar_tile_columns dimensions scalars instructions bi bj efficient)).
Definition memory_started_scalar_tiled_loop dimensions scalars instructions bi bj :=
  memory_started_scalar_tiled dimensions scalars instructions bi bj true.
Lemma memory_started_scalar_tile_columns_trimming dimensions scalars instructions bi bj ti N M parameters :
  0 < M -> 0 < bj ->
  memory_loop_trace (memory_started_scalar_tile_columns dimensions scalars instructions bi bj false) (ti::N::M::parameters) =
    memory_loop_trace (memory_started_scalar_tile_columns dimensions scalars instructions bi bj true) (ti::N::M::parameters).
Proof.
  intros MP BJ; unfold memory_started_scalar_tile_columns.
  change (flat_map (fun tj => if bj*tj <=? M+ -1 then
    memory_loop_trace (memory_started_scalar_tile_points dimensions scalars instructions bi bj) (tj::ti::N::M::parameters) else []) (Zrange 0 M) =
    flat_map (fun tj => if bj*tj <=? M+ -1 then
    memory_loop_trace (memory_started_scalar_tile_points dimensions scalars instructions bi bj) (tj::ti::N::M::parameters) else []) (Zrange 0 ((M+(bj-1))/bj))).
  replace (M + -1) with (M-1) by lia; replace (M+(bj-1)) with (M+bj-1) by lia.
  apply memory_guarded_tile_range; assumption.
Qed.
Theorem memory_started_scalar_tile_trimming dimensions scalars instructions bi bj N M parameters before after :
  0 < N -> 0 < M -> 0 < bi -> 0 < bj ->
  (L.loop_semantics (memory_started_scalar_tiled dimensions scalars instructions bi bj false) (N::M::parameters) before after <->
    L.loop_semantics (memory_started_scalar_tiled dimensions scalars instructions bi bj true) (N::M::parameters) before after).
Proof.
  intros NP MP BI BJ; rewrite !memory_loop_trace_correct.
  assert (TRACE : memory_loop_trace (memory_started_scalar_tiled dimensions scalars instructions bi bj false) (N::M::parameters) =
    memory_loop_trace (memory_started_scalar_tiled dimensions scalars instructions bi bj true) (N::M::parameters)).
  { unfold memory_started_scalar_tiled.
    change (flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_started_scalar_tile_columns dimensions scalars instructions bi bj false) (ti::N::M::parameters) else []) (Zrange 0 N) =
      flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_started_scalar_tile_columns dimensions scalars instructions bi bj true) (ti::N::M::parameters) else []) (Zrange 0 ((N+(bi-1))/bi))).
    replace (N+ -1) with (N-1) by lia; replace (N+(bi-1)) with (N+bi-1) by lia.
    rewrite (@memory_guarded_tile_range _
      (fun ti => memory_loop_trace (memory_started_scalar_tile_columns dimensions scalars instructions bi bj false) (ti::N::M::parameters)) N bi NP BI).
    apply flat_map_ext; intro ti; destruct (bi*ti <=? N-1); [|reflexivity].
    apply memory_started_scalar_tile_columns_trimming; assumption. }
  rewrite TRACE; reflexivity.
Qed.
Definition checked_memory_started_scalar_tiling bounds source_loop dimensions scalars instructions context arrays bi bj :=
  checked_memory_bounded_source_tiling bounds source_loop
    (memory_started_scalar_tiled dimensions scalars instructions bi bj false) context arrays
    (repeat (memory_scalar_tiling_witness dimensions (length context) bi bj) (length instructions)).
Theorem checked_memory_started_scalar_tiling_correct bounds source_loop dimensions scalars instructions context arrays bi bj first_cap second_cap :
  nth_error bounds O = Some (MemoryNested.A.Interval 1 first_cap) ->
  nth_error bounds 1%nat = Some (MemoryNested.A.Interval 1 second_cap) ->
  (2 <= length context)%nat -> 0 < bi -> 0 < bj ->
  mayReturn (checked_memory_started_scalar_tiling bounds source_loop dimensions scalars instructions context arrays bi bj) true ->
  memory_bounded_source_certificate bounds source_loop context (memory_started_scalar_tiled_loop dimensions scalars instructions bi bj).
Proof.
  intros FIRST SECOND CONTEXT BI BJ CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  assert (ARITY : (2 <= length parameters)%nat) by (rewrite LENGTH; exact CONTEXT).
  destruct parameters as [|N [|M parameters]]; cbn in ARITY; try (exfalso; lia).
  assert (NP : 0 < N) by (pose proof (WITHIN O _ FIRST) as RANGE; unfold MemoryNested.A.contains in RANGE; cbn in RANGE; lia).
  assert (MP : 0 < M) by (pose proof (WITHIN 1%nat _ SECOND) as RANGE; unfold MemoryNested.A.contains in RANGE; cbn in RANGE; lia).
  unfold memory_started_scalar_tiled_loop.
  apply (proj1 (@memory_started_scalar_tile_trimming dimensions scalars instructions bi bj N M parameters before after NP MP BI BJ)).
  unfold checked_memory_started_scalar_tiling in CHECK.
  exact (@checked_memory_bounded_source_tiling_correct bounds source_loop
    (memory_started_scalar_tiled dimensions scalars instructions bi bj false) context arrays
    (repeat (memory_scalar_tiling_witness dimensions (length context) bi bj) (length instructions))
    CHECK (N::M::parameters) before after LENGTH WITHIN NONALIAS SOURCE).
Qed.
Print Assumptions memory_started_scalar_tile_trimming.
Print Assumptions checked_memory_started_scalar_tiling_correct.
