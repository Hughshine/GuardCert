From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Misc.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemorySequenceLoops GuardMemoryTiledRectangles GuardMemoryTileRangeTrimming.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_ragged_tile_j instructions (bi bj : Z) :=
  L.Loop (L.Mult bj (L.Var 1)) (L.Sum (L.Mult bj (L.Var 1)) (L.Constant bj))
    (L.Guard (L.LE (L.Var 0) (L.Sum (L.Sum (L.Var 1) (L.Var 5)) (L.Constant (-1))))
      (L.Seq (memory_instruction_sequence instructions))).
Definition memory_ragged_tile_i instructions (bi bj : Z) :=
  L.Loop (L.Mult bi (L.Var 1)) (L.Sum (L.Mult bi (L.Var 1)) (L.Constant bi))
    (L.Guard (L.LE (L.Var 0) (L.Sum (L.Var 3) (L.Constant (-1))))
      (memory_ragged_tile_j instructions bi bj)).
Definition memory_ragged_tile_column_keep bj :=
  L.LE (L.Mult bj (L.Var 0)) (L.Sum (L.Sum (L.Var 2) (L.Var 3)) (L.Constant (-2))).
Definition memory_ragged_tile_row_keep bi :=
  L.LE (L.Mult bi (L.Var 0)) (L.Sum (L.Var 1) (L.Constant (-1))).
Definition memory_ragged_tile_width := L.Sum (L.Sum (L.Var 1) (L.Var 2)) (L.Constant (-1)).
Definition memory_ragged_tile_columns_bound bj (efficient : bool) :=
  if efficient then L.Div (L.Sum memory_ragged_tile_width (L.Constant (bj-1))) bj
  else memory_ragged_tile_width.
Definition memory_ragged_tile_columns instructions (bi bj : Z) (efficient : bool) :=
  L.Loop (L.Constant 0) (memory_ragged_tile_columns_bound bj efficient)
    (L.Guard (memory_ragged_tile_column_keep bj) (memory_ragged_tile_i instructions bi bj)).
Definition memory_ragged_tile_rows_bound bi (efficient : bool) :=
  if efficient then L.Div (L.Sum (L.Var 0) (L.Constant (bi-1))) bi else L.Var 0.
Definition memory_ragged_tiled_loop instructions (bi bj : Z) (efficient : bool) :=
  L.Loop (L.Constant 0) (memory_ragged_tile_rows_bound bi efficient)
    (L.Guard (memory_ragged_tile_row_keep bi) (memory_ragged_tile_columns instructions bi bj efficient)).

Lemma memory_ragged_column_trimming instructions bi bj N M ti :
  0 < N -> 0 < M -> 0 < bj ->
  memory_loop_trace (memory_ragged_tile_columns instructions bi bj false) [ti;N;M] =
  memory_loop_trace (memory_ragged_tile_columns instructions bi bj true) [ti;N;M].
Proof.
  intros NP MP BJ; unfold memory_ragged_tile_columns,memory_ragged_tile_columns_bound,
    memory_ragged_tile_width,memory_ragged_tile_column_keep.
  cbn -[Zrange Z.add Z.mul Z.div Z.leb memory_loop_trace].
  change (flat_map (fun tj => if bj*tj <=? N+M-2
    then memory_loop_trace (memory_ragged_tile_i instructions bi bj) [tj;ti;N;M] else []) (Zrange 0 (N+M+ -1)) =
    flat_map (fun tj => if bj*tj <=? N+M-2
    then memory_loop_trace (memory_ragged_tile_i instructions bi bj) [tj;ti;N;M] else [])
      (Zrange 0 ((N+M+ -1+(bj-1))/bj))).
  replace (N+M+ -1) with (N+M-1) by lia.
  replace (N+M-2) with ((N+M-1)-1) by lia.
  replace (N+M-1+(bj-1)) with (N+M-1+bj-1) by lia.
  apply memory_guarded_tile_range; lia.
Qed.
Theorem memory_ragged_tile_trimming instructions bi bj N M before after :
  0 < N -> 0 < M -> 0 < bi -> 0 < bj ->
  (L.loop_semantics (memory_ragged_tiled_loop instructions bi bj false) [N;M] before after <->
   L.loop_semantics (memory_ragged_tiled_loop instructions bi bj true) [N;M] before after).
Proof.
  intros NP MP BI BJ; rewrite !memory_loop_trace_correct.
  assert (TRACE : memory_loop_trace (memory_ragged_tiled_loop instructions bi bj false) [N;M] =
    memory_loop_trace (memory_ragged_tiled_loop instructions bi bj true) [N;M]).
  { unfold memory_ragged_tiled_loop,memory_ragged_tile_rows_bound,memory_ragged_tile_row_keep.
    cbn -[Zrange Z.add Z.mul Z.div Z.leb memory_loop_trace].
    change (flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_ragged_tile_columns instructions bi bj false) [ti;N;M] else []) (Zrange 0 N) =
      flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_ragged_tile_columns instructions bi bj true) [ti;N;M] else [])
        (Zrange 0 ((N+(bi-1))/bi))).
    replace (N+ -1) with (N-1) by lia; replace (N+(bi-1)) with (N+bi-1) by lia.
    rewrite (@memory_guarded_tile_range _
      (fun ti => memory_loop_trace (memory_ragged_tile_columns instructions bi bj false) [ti;N;M]) N bi NP BI).
    apply flat_map_ext; intro ti; destruct (bi*ti <=? N-1); [|reflexivity].
    apply memory_ragged_column_trimming; assumption. }
  rewrite TRACE; reflexivity.
Qed.
Print Assumptions memory_ragged_tile_trimming.
