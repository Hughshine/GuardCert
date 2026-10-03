From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryLoopTrace
  GuardMemoryExtractedTiling GuardMemoryTileRangeTrimming GuardMemoryNaryLoops GuardMemoryRecursiveChecker GuardMemoryScalarChecker GuardMemoryScalarLoops GuardMemoryScalarCandidates GuardMemoryRecursiveTiling.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint memory_scalar_tiled_inner depth remaining scalars instructions : L.stmt := match remaining with
  | O => memory_carry_scalar_arguments (depth+2)%nat depth scalars (L.Seq (memory_nary_instruction_sequence depth instructions))
  | S rest => L.Loop (L.Constant 0) (L.Var (2*depth+2)%nat)
      (memory_scalar_tiled_inner (S depth) rest scalars instructions) end.
Definition memory_scalar_tile_points dimensions scalars instructions bi bj :=
  L.Loop (L.Mult bi (L.Var 1)) (L.Sum (L.Mult bi (L.Var 1)) (L.Constant bi))
    (L.Guard (L.LE (L.Var 0) (L.Sum (L.Var 3) (L.Constant (-1))))
      (L.Loop (L.Mult bj (L.Var 1)) (L.Sum (L.Mult bj (L.Var 1)) (L.Constant bj))
        (L.Guard (L.LE (L.Var 0) (L.Sum (L.Var 5) (L.Constant (-1))))
          (memory_scalar_tiled_inner 2 (dimensions-2)%nat scalars instructions)))).
Definition memory_scalar_tile_columns dimensions scalars instructions bi bj (efficient : bool) :=
  L.Loop (L.Constant 0) (if efficient then L.Div (L.Sum (L.Var 2) (L.Constant (bj-1))) bj else L.Var 2)
    (L.Guard (L.LE (L.Mult bj (L.Var 0)) (L.Sum (L.Var 3) (L.Constant (-1))))
      (memory_scalar_tile_points dimensions scalars instructions bi bj)).
Definition memory_scalar_tiled_loop dimensions scalars instructions bi bj (efficient : bool) :=
  L.Loop (L.Constant 0) (if efficient then L.Div (L.Sum (L.Var 0) (L.Constant (bi-1))) bi else L.Var 0)
    (L.Guard (L.LE (L.Mult bi (L.Var 0)) (L.Sum (L.Var 1) (L.Constant (-1))))
      (memory_scalar_tile_columns dimensions scalars instructions bi bj efficient)).
Lemma memory_scalar_tile_columns_trimming dimensions scalars instructions bi bj ti N M parameters :
  0 < M -> 0 < bj ->
  memory_loop_trace (memory_scalar_tile_columns dimensions scalars instructions bi bj false) (ti::N::M::parameters) =
    memory_loop_trace (memory_scalar_tile_columns dimensions scalars instructions bi bj true) (ti::N::M::parameters).
Proof.
  intros MP BJ; unfold memory_scalar_tile_columns.
  change (flat_map (fun tj => if bj*tj <=? M+ -1 then
    memory_loop_trace (memory_scalar_tile_points dimensions scalars instructions bi bj) (tj::ti::N::M::parameters) else []) (Zrange 0 M) =
    flat_map (fun tj => if bj*tj <=? M+ -1 then
    memory_loop_trace (memory_scalar_tile_points dimensions scalars instructions bi bj) (tj::ti::N::M::parameters) else []) (Zrange 0 ((M+(bj-1))/bj))).
  replace (M + -1) with (M-1) by lia; replace (M+(bj-1)) with (M+bj-1) by lia.
  apply memory_guarded_tile_range; assumption.
Qed.
Theorem memory_scalar_tile_trimming dimensions scalars instructions bi bj N M parameters before after :
  0 < N -> 0 < M -> 0 < bi -> 0 < bj ->
  (L.loop_semantics (memory_scalar_tiled_loop dimensions scalars instructions bi bj false) (N::M::parameters) before after <->
    L.loop_semantics (memory_scalar_tiled_loop dimensions scalars instructions bi bj true) (N::M::parameters) before after).
Proof.
  intros NP MP BI BJ; rewrite !memory_loop_trace_correct.
  assert (TRACE : memory_loop_trace (memory_scalar_tiled_loop dimensions scalars instructions bi bj false) (N::M::parameters) =
    memory_loop_trace (memory_scalar_tiled_loop dimensions scalars instructions bi bj true) (N::M::parameters)).
  { unfold memory_scalar_tiled_loop.
    change (flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_scalar_tile_columns dimensions scalars instructions bi bj false) (ti::N::M::parameters) else []) (Zrange 0 N) =
      flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_scalar_tile_columns dimensions scalars instructions bi bj true) (ti::N::M::parameters) else []) (Zrange 0 ((N+(bi-1))/bi))).
    replace (N+ -1) with (N-1) by lia; replace (N+(bi-1)) with (N+bi-1) by lia.
    rewrite (@memory_guarded_tile_range _
      (fun ti => memory_loop_trace (memory_scalar_tile_columns dimensions scalars instructions bi bj false) (ti::N::M::parameters)) N bi NP BI).
    apply flat_map_ext; intro ti; destruct (bi*ti <=? N-1); [|reflexivity].
    apply memory_scalar_tile_columns_trimming; assumption. }
  rewrite TRACE; reflexivity.
Qed.
Definition memory_scalar_tiling_witness dimensions dimension bi bj : statement_tiling_witness :=
  {| stw_point_dim := dimensions; stw_links :=
      [{| tl_expr := {| ae_var_coeffs := 1::repeat 0 (dimensions-1); ae_param_coeffs := repeat 0 dimension; ae_const := 0 |}; tl_tile_size := bi |};
       {| tl_expr := {| ae_var_coeffs := [0;0;1]++repeat 0 (dimensions-2); ae_param_coeffs := repeat 0 dimension; ae_const := 0 |}; tl_tile_size := bj |}] |}.
Definition checked_memory_scalar_tiling dimensions cap scalars instructions context arrays bi bj :=
  let vars := map (fun array => (array,tt)) (context++arrays) in
  checked_memory_extracted_tiling_loops
    (memory_scalar_assumed_loop dimensions cap scalars (memory_scalar_rectangle 0 dimensions scalars instructions),context,vars)
    (memory_scalar_assumed_loop dimensions cap scalars (memory_scalar_tiled_loop dimensions scalars instructions bi bj false),context,vars)
    (repeat (memory_scalar_tiling_witness dimensions (length context) bi bj) (length instructions)).
Theorem checked_memory_scalar_tiling_correct dimensions cap scalars instructions context arrays bi bj :
  length context = (dimensions+scalars)%nat -> (2 <= dimensions)%nat -> 0 < bi -> 0 < bj ->
  mayReturn (checked_memory_scalar_tiling dimensions cap scalars instructions context arrays bi bj) true ->
  memory_scalar_candidate_certificate dimensions cap scalars instructions context (memory_scalar_tiled_loop dimensions scalars instructions bi bj true).
Proof.
  intros CONTEXT DIMENSIONS BI BJ CHECK parameters before after LENGTH WITHIN NONALIAS SOURCE.
  destruct dimensions as [|[|remaining]]; try lia.
  assert (ARITY : length parameters = (S (S remaining)+scalars)%nat) by (rewrite LENGTH; exact CONTEXT).
  destruct parameters as [|N [|M parameters]]; cbn in ARITY; try discriminate.
  assert (NP : 0 < N) by (pose proof (WITHIN O _ eq_refl) as RANGE; unfold MemoryNested.A.contains in RANGE; cbn in RANGE; lia).
  assert (MP : 0 < M) by (pose proof (WITHIN 1%nat _ eq_refl) as RANGE; unfold MemoryNested.A.contains in RANGE; cbn in RANGE; lia).
  apply (proj1 (@memory_scalar_tile_trimming (S (S remaining)) scalars instructions bi bj N M parameters before after NP MP BI BJ)).
  unfold checked_memory_scalar_tiling in CHECK.
  apply memory_scalar_assumed_execution with (dimensions := S (S remaining)) (cap := cap) (scalars := scalars); [exact WITHIN|].
  pose proof (@validated_memory_extracted_tiling_loops_at
    (memory_scalar_assumed_loop (S (S remaining)) cap scalars (memory_scalar_rectangle 0 (S (S remaining)) scalars instructions))
    (memory_scalar_assumed_loop (S (S remaining)) cap scalars (memory_scalar_tiled_loop (S (S remaining)) scalars instructions bi bj false)) context
    (map (fun array => (array,tt)) (context++arrays))
    (repeat (memory_scalar_tiling_witness (S (S remaining)) (length context) bi bj) (length instructions))
    (rev (N::M::parameters)) before after ltac:(rewrite length_rev; exact LENGTH) NONALIAS CHECK) as VALID.
  rewrite rev_involutive in VALID; apply VALID; apply memory_scalar_assumed_execution; assumption.
Qed.
Print Assumptions checked_memory_scalar_tiling_correct.
