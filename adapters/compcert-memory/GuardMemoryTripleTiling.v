From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryLoopTrace
  GuardMemoryExtractedTiling GuardMemoryTileRangeTrimming GuardMemoryNaryLoops GuardMemoryTripleChecker.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_triple_tile_points instructions bi bj :=
  L.Loop (L.Mult bi (L.Var 1)) (L.Sum (L.Mult bi (L.Var 1)) (L.Constant bi))
    (L.Guard (L.LE (L.Var 0) (L.Sum (L.Var 3) (L.Constant (-1))))
      (L.Loop (L.Mult bj (L.Var 1)) (L.Sum (L.Mult bj (L.Var 1)) (L.Constant bj))
        (L.Guard (L.LE (L.Var 0) (L.Sum (L.Var 5) (L.Constant (-1))))
          (L.Loop (L.Constant 0) (L.Var 6) (L.Seq (memory_nary_instruction_sequence 3 instructions)))))).
Definition memory_triple_tile_columns instructions bi bj (efficient : bool) :=
  L.Loop (L.Constant 0) (if efficient then L.Div (L.Sum (L.Var 2) (L.Constant (bj-1))) bj else L.Var 2)
    (L.Guard (L.LE (L.Mult bj (L.Var 0)) (L.Sum (L.Var 3) (L.Constant (-1))))
      (memory_triple_tile_points instructions bi bj)).
Definition memory_triple_tiled_loop instructions bi bj (efficient : bool) :=
  L.Loop (L.Constant 0) (if efficient then L.Div (L.Sum (L.Var 0) (L.Constant (bi-1))) bi else L.Var 0)
    (L.Guard (L.LE (L.Mult bi (L.Var 0)) (L.Sum (L.Var 1) (L.Constant (-1))))
      (memory_triple_tile_columns instructions bi bj efficient)).
Lemma memory_triple_tile_columns_trimming instructions bi bj ti N M L :
  0 < M -> 0 < bj ->
  memory_loop_trace (memory_triple_tile_columns instructions bi bj false) [ti;N;M;L] =
    memory_loop_trace (memory_triple_tile_columns instructions bi bj true) [ti;N;M;L].
Proof.
  intros MP BJ; unfold memory_triple_tile_columns.
  change (flat_map (fun tj => if bj*tj <=? M+ -1 then
    memory_loop_trace (memory_triple_tile_points instructions bi bj) [tj;ti;N;M;L] else []) (Zrange 0 M) =
    flat_map (fun tj => if bj*tj <=? M+ -1 then
    memory_loop_trace (memory_triple_tile_points instructions bi bj) [tj;ti;N;M;L] else []) (Zrange 0 ((M+(bj-1))/bj))).
  replace (M + -1) with (M-1) by lia; replace (M+(bj-1)) with (M+bj-1) by lia.
  apply memory_guarded_tile_range; assumption.
Qed.
Theorem memory_triple_tile_trimming instructions bi bj N M L before after :
  0 < N -> 0 < M -> 0 < bi -> 0 < bj ->
  (L.loop_semantics (memory_triple_tiled_loop instructions bi bj false) [N;M;L] before after <->
    L.loop_semantics (memory_triple_tiled_loop instructions bi bj true) [N;M;L] before after).
Proof.
  intros NP MP BI BJ; rewrite !memory_loop_trace_correct.
  assert (TRACE : memory_loop_trace (memory_triple_tiled_loop instructions bi bj false) [N;M;L] =
    memory_loop_trace (memory_triple_tiled_loop instructions bi bj true) [N;M;L]).
  { unfold memory_triple_tiled_loop.
    cbn -[Zrange Z.add Z.mul Z.div Z.leb memory_loop_trace memory_triple_tile_columns].
    change (flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_triple_tile_columns instructions bi bj false) [ti;N;M;L] else []) (Zrange 0 N) =
      flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_triple_tile_columns instructions bi bj true) [ti;N;M;L] else []) (Zrange 0 ((N+(bi-1))/bi))).
    replace (N+ -1) with (N-1) by lia; replace (N+(bi-1)) with (N+bi-1) by lia.
    rewrite (@memory_guarded_tile_range _
      (fun ti => memory_loop_trace (memory_triple_tile_columns instructions bi bj false) [ti;N;M;L]) N bi NP BI).
    apply flat_map_ext; intro ti; destruct (bi*ti <=? N-1); [|reflexivity].
    apply memory_triple_tile_columns_trimming; assumption. }
  rewrite TRACE; reflexivity.
Qed.
Definition memory_triple_tiling_witness dimension bi bj : statement_tiling_witness :=
  {| stw_point_dim := 3; stw_links :=
      [{| tl_expr := {| ae_var_coeffs := [1;0;0]; ae_param_coeffs := repeat 0 dimension; ae_const := 0 |}; tl_tile_size := bi |};
       {| tl_expr := {| ae_var_coeffs := [0;0;1;0]; ae_param_coeffs := repeat 0 dimension; ae_const := 0 |}; tl_tile_size := bj |}] |}.
Definition checked_memory_triple_tiling cap instructions context arrays bi bj :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_extracted_tiling_loops
    (memory_triple_assumed_loop cap (memory_nary_rectangle 0 3 instructions),context,vars)
    (memory_triple_assumed_loop cap (memory_triple_tiled_loop instructions bi bj false),context,vars)
    (repeat (memory_triple_tiling_witness (length context) bi bj) (length instructions)).
Theorem checked_memory_triple_tiling_correct cap instructions context arrays bi bj :
  length context = 3%nat -> 0 < bi -> 0 < bj ->
  mayReturn (checked_memory_triple_tiling cap instructions context arrays bi bj) true ->
  memory_triple_candidate_certificate cap instructions context (memory_triple_tiled_loop instructions bi bj true).
Proof.
  intros CONTEXT BI BJ CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  assert (NL : length parameters = 3%nat) by (rewrite LENGTH; exact CONTEXT).
  destruct parameters as [|N [|M [|K rest]]]; cbn in NL; try discriminate.
  destruct rest; cbn in NL; [|discriminate].
  assert (NP : 0 < N) by (pose proof (WITHIN O _ eq_refl) as RANGE; unfold MemoryNested.A.contains in RANGE; cbn in RANGE; lia).
  assert (MP : 0 < M) by (pose proof (WITHIN 1%nat _ eq_refl) as RANGE; unfold MemoryNested.A.contains in RANGE; cbn in RANGE; lia).
  apply (proj1 (@memory_triple_tile_trimming instructions bi bj N M K before after NP MP BI BJ)).
  unfold checked_memory_triple_tiling in CHECK.
  apply memory_triple_assumed_execution with (cap := cap); [exact WITHIN|].
  pose proof (@validated_memory_extracted_tiling_loops_at
    (memory_triple_assumed_loop cap (memory_nary_rectangle 0 3 instructions))
    (memory_triple_assumed_loop cap (memory_triple_tiled_loop instructions bi bj false)) context
    (map (fun array => (array,tt)) (context++arrays))
    (repeat (memory_triple_tiling_witness (length context) bi bj) (length instructions)) (rev [N;M;K]) before after
    ltac:(rewrite length_rev; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply VALID; apply memory_triple_assumed_execution; assumption.
Qed.
Print Assumptions checked_memory_triple_tiling_correct.
