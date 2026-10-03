From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Misc ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness.
From Vpl Require Import Impure.
From Guard Require Import ClightRectangularStore.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryArrayBackend GuardMemorySequenceLoops GuardMemoryLoopTrace GuardMemoryExtractedTiling
  GuardMemoryTiledRectangles GuardMemoryTileRangeTrimming GuardMemoryNamedOperations
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceEndpoints GuardMemoryParametricLoops GuardMemoryParametricChecker.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This candidate construction is untrusted. The same extractor, domain
    correspondence and dependence certificate checker validate its result. *)
Fixpoint memory_parametric_tiled_expression expression :=
  match expression with
  | L.Constant value => L.Constant value
  | L.Var O => L.Var 1
  | L.Var (S index) => L.Var (S index+3)
  | L.Sum first second => L.Sum (memory_parametric_tiled_expression first) (memory_parametric_tiled_expression second)
  | L.Mult factor value => L.Mult factor (memory_parametric_tiled_expression value)
  | L.Div value divisor => L.Div (memory_parametric_tiled_expression value) divisor
  | L.Mod value divisor => L.Mod (memory_parametric_tiled_expression value) divisor
  | L.Min first second => L.Min (memory_parametric_tiled_expression first) (memory_parametric_tiled_expression second)
  | L.Max first second => L.Max (memory_parametric_tiled_expression first) (memory_parametric_tiled_expression second) end.
Definition memory_parametric_tile_points instructions encoded bi bj :=
  L.Loop (L.Mult bi (L.Var 1)) (L.Sum (L.Mult bi (L.Var 1)) (L.Constant bi))
    (L.Guard (L.LE (L.Var 0) (L.Sum (L.Var 3) (L.Constant (-1))))
      (L.Loop (L.Mult bj (L.Var 1)) (L.Sum (L.Mult bj (L.Var 1)) (L.Constant bj))
        (L.Guard (L.LE (L.Var 0) (L.Sum (memory_parametric_tiled_expression encoded) (L.Constant (-1))))
          (L.Seq (memory_instruction_sequence instructions))))).
Definition memory_parametric_tile_columns instructions encoded stride bi bj (efficient : bool) :=
  L.Loop (L.Constant 0)
    (L.Constant (if efficient then rectangle_tile_count stride bj else stride))
    (L.Guard (L.LE (L.Mult bj (L.Var 0)) (L.Constant (stride-1)))
      (memory_parametric_tile_points instructions encoded bi bj)).
Definition memory_parametric_tiled_loop instructions encoded stride bi bj (efficient : bool) :=
  L.Loop (L.Constant 0)
    (if efficient then L.Div (L.Sum (L.Var 0) (L.Constant (bi-1))) bi else L.Var 0)
    (L.Guard (L.LE (L.Mult bi (L.Var 0)) (L.Sum (L.Var 1) (L.Constant (-1))))
      (memory_parametric_tile_columns instructions encoded stride bi bj efficient)).
Lemma memory_parametric_tile_columns_trimming instructions encoded stride bi bj ti parameters :
  0 < stride -> 0 < bj ->
  memory_loop_trace (memory_parametric_tile_columns instructions encoded stride bi bj false) (ti::parameters) =
    memory_loop_trace (memory_parametric_tile_columns instructions encoded stride bi bj true) (ti::parameters).
Proof.
  intros STRIDE BJ; unfold memory_parametric_tile_columns.
  cbn -[Zrange Z.add Z.mul Z.div Z.leb memory_loop_trace rectangle_tile_count].
  apply memory_guarded_tile_range; assumption.
Qed.
Theorem memory_parametric_tile_trimming instructions encoded stride bi bj N parameters before after :
  0 < N -> 0 < stride -> 0 < bi -> 0 < bj ->
  (L.loop_semantics (memory_parametric_tiled_loop instructions encoded stride bi bj false) (N::parameters) before after <->
    L.loop_semantics (memory_parametric_tiled_loop instructions encoded stride bi bj true) (N::parameters) before after).
Proof.
  intros NP STRIDE BI BJ; rewrite !memory_loop_trace_correct.
  assert (TRACE : memory_loop_trace (memory_parametric_tiled_loop instructions encoded stride bi bj false) (N::parameters) =
    memory_loop_trace (memory_parametric_tiled_loop instructions encoded stride bi bj true) (N::parameters)).
  { unfold memory_parametric_tiled_loop.
    cbn -[Zrange Z.add Z.mul Z.div Z.leb memory_loop_trace memory_parametric_tile_columns].
    change (flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_parametric_tile_columns instructions encoded stride bi bj false) (ti::N::parameters) else []) (Zrange 0 N) =
      flat_map (fun ti => if bi*ti <=? N+ -1 then
      memory_loop_trace (memory_parametric_tile_columns instructions encoded stride bi bj true) (ti::N::parameters) else [])
        (Zrange 0 ((N+(bi-1))/bi))).
    replace (N+ -1) with (N-1) by lia.
    replace (N+(bi-1)) with (N+bi-1) by lia.
    rewrite (@memory_guarded_tile_range _
      (fun ti => memory_loop_trace (memory_parametric_tile_columns instructions encoded stride bi bj false) (ti::N::parameters)) N bi NP BI).
    apply flat_map_ext; intro ti; destruct (bi*ti <=? N-1); [|reflexivity].
    apply memory_parametric_tile_columns_trimming; assumption. }
  rewrite TRACE; reflexivity.
Qed.
Definition memory_parametric_tiling_witness dimension row_width column_width : statement_tiling_witness :=
  {| stw_point_dim := 2; stw_links :=
      [{| tl_expr := {| ae_var_coeffs := [1;0]; ae_param_coeffs := repeat 0 dimension; ae_const := 0 |};
          tl_tile_size := row_width |};
       {| tl_expr := {| ae_var_coeffs := [0;0;1]; ae_param_coeffs := repeat 0 dimension; ae_const := 0 |};
          tl_tile_size := column_width |}] |}.
Definition checked_named_parametric_tiling base operations row context bounds expression encoded bi bj :=
  let instructions := map named_operation_instruction operations in
  let vars := map (fun array => (array,tt)) (context++flat_map named_operation_arrays operations) in
  checked_memory_extracted_tiling_loops
    (memory_parametric_assumed_loop base row context bounds expression (memory_parametric_sequence encoded instructions),context,vars)
    (memory_parametric_assumed_loop base row context bounds expression
      (memory_parametric_tiled_loop instructions encoded (rectangle_stride base) bi bj false),context,vars)
    (repeat (memory_parametric_tiling_witness (length context) bi bj) (length instructions)).
Theorem checked_named_parametric_tiling_correct base operations row context bounds expression encoded bi bj :
  0 < rectangle_stride base -> 0 < bi -> 0 < bj ->
  (forall parameters, MemoryNested.A.env_within bounds parameters -> 0 < nth O parameters 0) ->
  mayReturn (checked_named_parametric_tiling base operations row context bounds expression encoded bi bj) true ->
  memory_parametric_candidate_certificate base operations row context bounds expression encoded
    (memory_parametric_tiled_loop (map named_operation_instruction operations) encoded (rectangle_stride base) bi bj true).
Proof.
  intros STRIDE BI BJ POSITIVE CHECK parameters before after LENGTH WITHIN WIDTH NONALIAS SOURCE.
  destruct parameters as [|N parameters].
  - specialize (POSITIVE [] WITHIN); cbn in POSITIVE; lia.
  - apply (proj1 (@memory_parametric_tile_trimming (map named_operation_instruction operations) encoded
      (rectangle_stride base) bi bj N parameters before after (POSITIVE _ WITHIN) STRIDE BI BJ)).
    unfold checked_named_parametric_tiling in CHECK.
    apply memory_parametric_assumed_execution with (base := base) (row := row) (context := context)
      (bounds := bounds) (expression := expression); [exact WITHIN|exact WIDTH|].
    pose proof (@validated_memory_extracted_tiling_loops_at
      (memory_parametric_assumed_loop base row context bounds expression
        (memory_parametric_sequence encoded (map named_operation_instruction operations)))
      (memory_parametric_assumed_loop base row context bounds expression
        (memory_parametric_tiled_loop (map named_operation_instruction operations) encoded (rectangle_stride base) bi bj false))
      context (map (fun array => (array,tt)) (context++flat_map named_operation_arrays operations))
      (repeat (memory_parametric_tiling_witness (length context) bi bj) (length operations)) (rev (N::parameters)) before after
      ltac:(rewrite length_rev; exact LENGTH) NONALIAS ltac:(rewrite length_map in CHECK; exact CHECK)) as VALID.
    rewrite rev_involutive in VALID; apply VALID.
    apply memory_parametric_assumed_execution; assumption.
Qed.
Print Assumptions checked_named_parametric_tiling_correct.
