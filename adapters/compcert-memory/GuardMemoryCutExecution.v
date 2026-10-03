From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation.
From polcert.lib Require Import Misc Linalg LinalgExt ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import RectangularSchedule RectangularIteration ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemoryTilingProgress GuardMemoryTiledRectangles GuardMemoryTiledExecution
  GuardMemoryAffineDomains GuardMemoryConditionalLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_rectangle_event_point instruction n m event :=
  rectangle_poly_point instruction rectangle_row_schedule n m
    (nth 1 (event_environment event) 0) (nth 0 (event_environment event) 0).
Lemma memory_rectangle_trace_members instruction n m event :
  In event (memory_loop_trace (memory_rectangle_loop instruction) [n;m]) ->
  exists i j, event = MemoryLoopEvent instruction [j;i;n;m] [i;j].
Proof.
  unfold memory_rectangle_loop; cbn -[Zrange]; intro MEMBER.
  apply in_flat_map in MEMBER as [i [_ MEMBER]].
  apply in_flat_map in MEMBER as [j [_ MEMBER]].
  cbn in MEMBER; destruct MEMBER as [EQ|ABSENT]; [|contradiction].
  exists i,j; symmetry; exact EQ.
Qed.
Lemma memory_rectangle_trace_points instruction rows columns :
  map (memory_rectangle_event_point instruction (Z.of_nat rows) (Z.of_nat columns))
    (memory_loop_trace (memory_rectangle_loop instruction) [Z.of_nat rows;Z.of_nat columns]) =
  rectangle_poly_points instruction rectangle_row_schedule (Z.of_nat rows) (Z.of_nat columns) rows columns.
Proof.
  unfold memory_rectangle_loop; cbn -[Zrange].
  rewrite memory_map_flat_map,rectangle_points_expand.
  rewrite (@memory_range_zseq rows 0 (Z.of_nat rows)) by lia.
  apply flat_map_ext; intro i.
  rewrite (@memory_range_zseq columns 0 (Z.of_nat columns)) by lia.
  rewrite memory_map_flat_map.
  change (flat_map (fun j => [rectangle_poly_point instruction rectangle_row_schedule
    (Z.of_nat rows) (Z.of_nat columns) i j]) (zseq 0 columns) =
    map (rectangle_poly_point instruction rectangle_row_schedule (Z.of_nat rows) (Z.of_nat columns) i)
      (zseq 0 columns)).
  induction (zseq 0 columns); cbn; [reflexivity|rewrite IHl; reflexivity].
Qed.
Lemma memory_rectangle_event_execution instruction n m i j before after :
  memory_event_step (MemoryLoopEvent instruction [j;i;n;m] [i;j]) before after <->
  PL.instr_point_sema (rectangle_poly_point instruction rectangle_row_schedule n m i j) before after.
Proof.
  rewrite rectangle_poly_point_exec; unfold memory_event_step; cbn; split.
  - intros [writes [reads [WRITES [READS RUN]]]]; subst writes reads;
      repeat split; assumption || reflexivity.
  - intro RUN; exists (memory_write_cells instruction [i;j]),(memory_read_cells instruction [i;j]); exact RUN.
Qed.

Definition memory_cut_source_program instruction stride a b c : PL.t :=
  ([restrict_memory_instruction [affine_cut_constraint a b c]
      (rectangle_poly_instruction instruction stride rectangle_row_schedule)], [1%positive;2%positive],
   [(1%positive,tt);(2%positive,tt);(fst (instruction_write instruction),tt)]).
Definition memory_cut_tiled_program instruction stride bi bj a b c : PL.t :=
  ([restrict_memory_instruction [tiled_affine_cut_constraint a b c]
      (rectangle_tiled_instruction instruction stride bi bj)], [1%positive;2%positive],
   [(1%positive,tt);(2%positive,tt);(fst (instruction_write instruction),tt)]).
Definition memory_cut_source_loop instruction a b c :=
  guard_memory_instructions (memory_affine_cut_test a b c) (memory_rectangle_loop instruction).
Definition memory_cut_tiled_loop instruction bi bj a b c :=
  guard_memory_instructions (memory_affine_cut_test a b c) (rectangle_tiled_loop instruction bi bj).

Theorem memory_cut_source_points instruction a b c rows columns before after :
  L.loop_semantics (memory_cut_source_loop instruction a b c) [Z.of_nat rows;Z.of_nat columns] before after <->
  PL.instr_point_list_semantics (restrict_memory_points [affine_cut_constraint a b c]
    (rectangle_poly_points instruction rectangle_row_schedule (Z.of_nat rows) (Z.of_nat columns) rows columns))
    before after.
Proof.
  unfold memory_cut_source_loop,restrict_memory_points; rewrite <- memory_rectangle_trace_points.
  apply conditional_memory_loop_points.
  - intros event MEMBER; apply memory_rectangle_trace_members in MEMBER as [i [j ->]].
    change (in_poly [Z.of_nat rows;Z.of_nat columns;i;j] [affine_cut_constraint a b c] =
      L.eval_test [j;i;Z.of_nat rows;Z.of_nat columns] (memory_affine_cut_test a b c)).
    rewrite affine_cut_at; reflexivity.
  - intros event first final MEMBER; apply memory_rectangle_trace_members in MEMBER as [i [j ->]].
    apply memory_rectangle_event_execution.
Qed.
Theorem memory_cut_tiled_points instruction bi bj a b c n m before after :
  L.loop_semantics (memory_cut_tiled_loop instruction bi bj a b c) [n;m] before after <->
  PL.instr_point_list_semantics (restrict_memory_points [tiled_affine_cut_constraint a b c]
    (rectangle_tiled_points instruction n m bi bj)) before after.
Proof.
  unfold memory_cut_tiled_loop,restrict_memory_points; rewrite <- rectangle_tiled_trace_points.
  apply conditional_memory_loop_points.
  - intros event MEMBER; apply rectangle_tiled_trace_members in MEMBER as [ti [tj [i [j ->]]]].
    change (in_poly [n;m;ti;tj;i;j] [tiled_affine_cut_constraint a b c] =
      L.eval_test [j;i;tj;ti;n;m] (memory_affine_cut_test a b c)).
    rewrite tiled_affine_cut_at; reflexivity.
  - intros event first final MEMBER; apply rectangle_tiled_trace_members in MEMBER as [ti [tj [i [j ->]]]].
    apply rectangle_tiled_event_execution.
Qed.

Theorem memory_cut_source_to_poly instruction stride a b c rows columns before after :
  Z.of_nat columns <= stride ->
  L.loop_semantics (memory_cut_source_loop instruction a b c) [Z.of_nat rows;Z.of_nat columns] before after ->
  PL.poly_instance_list_semantics [Z.of_nat rows;Z.of_nat columns]
    (memory_cut_source_program instruction stride a b c) before after.
Proof.
  intros STRIDE RUN; apply memory_cut_source_points in RUN.
  eapply PL.PolyPointListSema with
    (ipl := restrict_memory_points [affine_cut_constraint a b c]
      (rectangle_poly_points instruction rectangle_row_schedule (Z.of_nat rows) (Z.of_nat columns) rows columns))
    (sorted_ipl := restrict_memory_points [affine_cut_constraint a b c]
      (rectangle_poly_points instruction rectangle_row_schedule (Z.of_nat rows) (Z.of_nat columns) rows columns)).
  - reflexivity.
  - apply flatten_memory_restricted_domains with
      (instructions := [rectangle_poly_instruction instruction stride rectangle_row_schedule]);
      apply rectangle_poly_flatten; exact STRIDE.
  - reflexivity.
  - unfold restrict_memory_points; apply StronglySorted_Sorted,memory_strongly_sorted_filter.
    apply Sorted_StronglySorted; [exact PL.ILSema.instr_point_sched_le_trans|apply rectangle_row_points_sorted].
  - exact RUN.
Qed.

Theorem memory_cut_tiled_poly_to_loop instruction stride bi bj a b c n m before after :
  0 < bi -> 0 < bj -> m <= stride ->
  PL.poly_instance_list_semantics [n;m] (memory_cut_tiled_program instruction stride bi bj a b c) before after ->
  L.loop_semantics (memory_cut_tiled_loop instruction bi bj a b c) [n;m] before after.
Proof.
  intros BI BJ STRIDE EXEC.
  inversion EXEC as [params program pis context vars initial final flattened ordered PROGRAM FLAT PERM SORTED RUN]; subst.
  unfold memory_cut_tiled_program in PROGRAM; inversion PROGRAM; subst pis context vars; clear PROGRAM.
  set (canonical := restrict_memory_points [tiled_affine_cut_constraint a b c]
    (rectangle_tiled_points instruction n m bi bj)).
  assert (CANONICAL : flattened = canonical).
  { eapply PL.flatten_instrs_det; [exact FLAT|].
    apply flatten_memory_restricted_domains with (instructions := [rectangle_tiled_instruction instruction stride bi bj]);
      apply rectangle_tiled_flatten; assumption. }
  subst flattened.
  assert (ORDER : canonical = ordered).
  { apply memory_sorted_permutation_unique.
    - unfold canonical,restrict_memory_points; apply StronglySorted_Sorted,memory_strongly_sorted_filter.
      apply Sorted_StronglySorted; [exact PL.ILSema.instr_point_sched_le_trans|].
      pose proof (@rectangle_tiled_points_sorted instruction n m bi bj); tauto.
    - unfold canonical,restrict_memory_points; apply NoDup_filter.
      pose proof (@rectangle_tiled_points_sorted instruction n m bi bj); tauto.
    - intros first second FIRST SECOND EQ; unfold canonical,restrict_memory_points in FIRST,SECOND.
      apply filter_In in FIRST as [FIRST _]; apply filter_In in SECOND as [SECOND _].
      eapply rectangle_tiled_timestamp_unique; eauto.
    - exact PERM.
    - exact SORTED. }
  subst ordered; apply memory_cut_tiled_points; exact RUN.
Qed.

Theorem validated_memory_cut_tiling instruction stride bi bj a b c rows columns before after :
  0 < bi -> 0 < bj -> Z.of_nat columns <= stride -> GuardMemoryInstr.NonAlias before ->
  mayReturn (validate_memory_tiling_equivalence
    (memory_cut_source_program instruction stride a b c)
    (memory_cut_tiled_program instruction stride bi bj a b c) [rectangle_tiling_witness bi bj]) true ->
  L.loop_semantics (memory_cut_source_loop instruction a b c) [Z.of_nat rows;Z.of_nat columns] before after ->
  L.loop_semantics (memory_cut_tiled_loop instruction bi bj a b c) [Z.of_nat rows;Z.of_nat columns] before after.
Proof.
  intros BI BJ STRIDE NONALIAS CHECK SOURCE.
  apply memory_cut_tiled_poly_to_loop with (stride := stride); [exact BI|exact BJ|exact STRIDE|].
  unfold memory_cut_source_program,memory_cut_tiled_program in CHECK |- *.
  eapply validated_memory_single_tiling_progress_at; [reflexivity|exact NONALIAS|exact CHECK|].
  apply memory_cut_source_to_poly; assumption.
Qed.

Print Assumptions validated_memory_cut_tiling.

Definition memory_cut_point instruction a b c i j before after :=
  if (a*i+b*j <=? c) then memory_point instruction i j before after else after = before.
Lemma memory_cut_instruction_loop instruction a b c i j env before after :
  L.loop_semantics (L.Guard (memory_affine_cut_test a b c) (L.Instr instruction [L.Var 1;L.Var 0]))
    (j::i::env) before after <-> memory_cut_point instruction a b c i j before after.
Proof.
  unfold memory_cut_point; split.
  - intro RUN; inversion RUN; subst;
      match goal with TEST : L.eval_test _ _ = _ |- _ =>
        rewrite memory_affine_cut_test_at in TEST; rewrite TEST end.
    + exact (proj1 (@memory_instruction_loop instruction i j env before after) H1).
    + reflexivity.
  - destruct (a*i+b*j <=? c) eqn:TEST; intro RUN.
    + apply L.LGuardTrue; [exact (proj2 (@memory_instruction_loop instruction i j env before after) RUN)|exact TEST].
    + subst after; apply L.LGuardFalse; exact TEST.
Qed.
Lemma memory_cut_row_loop instruction a b c i rows columns before after :
  L.loop_semantics (L.Loop (L.Constant 0) (L.Var 2) (L.Guard (memory_affine_cut_test a b c) (L.Instr instruction [L.Var 1;L.Var 0])))
    [i;Z.of_nat rows;Z.of_nat columns] before after <->
  counted_iterations (memory_cut_point instruction a b c i) columns 0 before after.
Proof.
  split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper code before' after' RUN]; subst.
      change (Iter.iter_semantics (fun j => L.loop_semantics
        (L.Guard (memory_affine_cut_test a b c) (L.Instr instruction [L.Var 1;L.Var 0])) [j;i;Z.of_nat rows;Z.of_nat columns])
        (Zrange 0 (Z.of_nat columns)) before after) in RUN.
      apply (proj1 (@memory_range_iterations columns _ 0 (Z.of_nat columns) before after ltac:(lia))) in RUN.
      eapply counted_iterations_map; [|exact RUN]; intros j first final STEP.
      apply (proj1 (@memory_cut_instruction_loop instruction a b c i j [Z.of_nat rows;Z.of_nat columns] first final)); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations columns _ 0 (Z.of_nat columns) _ _ ltac:(lia))).
    eapply counted_iterations_map; [|exact EXEC]; intros j first final STEP.
    apply (proj2 (@memory_cut_instruction_loop instruction a b c i j [Z.of_nat rows;Z.of_nat columns] first final)); exact STEP.
Qed.

Theorem memory_cut_rectangle_loop_iterations instruction a b c rows columns before after :
  L.loop_semantics (memory_cut_source_loop instruction a b c) [Z.of_nat rows;Z.of_nat columns] before after <->
  rectangular_iterations (memory_cut_point instruction a b c) rows columns before after.
Proof.
  unfold memory_cut_source_loop,memory_rectangle_loop; cbn [guard_memory_instructions]; unfold rectangular_iterations; split.
  - intro EXEC; inversion EXEC as [| | | | | env' lower upper code before' after' RUN]; subst.
      change (Iter.iter_semantics (fun i => L.loop_semantics
        (L.Loop (L.Constant 0) (L.Var 2) (L.Guard (memory_affine_cut_test a b c) (L.Instr instruction [L.Var 1;L.Var 0])))
        [i;Z.of_nat rows;Z.of_nat columns]) (Zrange 0 (Z.of_nat rows)) before after) in RUN.
      apply (proj1 (@memory_range_iterations rows _ 0 (Z.of_nat rows) before after ltac:(lia))) in RUN.
      eapply counted_iterations_map; [|exact RUN]; intros i first final STEP.
      apply (proj1 (@memory_cut_row_loop instruction a b c i rows columns first final)); exact STEP.
  - intro EXEC; apply L.LLoop.
    apply (proj2 (@memory_range_iterations rows _ 0 (Z.of_nat rows) _ _ ltac:(lia))).
    eapply counted_iterations_map; [|exact EXEC]; intros i first final STEP.
    apply (proj2 (@memory_cut_row_loop instruction a b c i rows columns first final)); exact STEP.
Qed.


Lemma memory_cut_point_locations instruction a b c i j before after :
  memory_cut_point instruction a b c i j before after -> runtime_locations after = runtime_locations before.
Proof. unfold memory_cut_point; destruct (_ <=? _); [apply memory_point_locations|intro EQ; subst; reflexivity]. Qed.
Theorem memory_cut_rectangle_lift locations instruction physical a b c rows columns before after :
  (forall i j first final, 0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns ->
    (physical i j first final <-> memory_cut_point instruction a b c i j
      (RuntimeState locations first) (RuntimeState locations final))) ->
  (rectangular_iterations physical rows columns before after <->
   L.loop_semantics (memory_cut_source_loop instruction a b c) [Z.of_nat rows;Z.of_nat columns]
     (RuntimeState locations before) (RuntimeState locations after)).
Proof.
  intro POINT; rewrite memory_cut_rectangle_loop_iterations; unfold rectangular_iterations.
  apply (@counted_memory_lift locations
    (fun i => counted_iterations (physical i) columns 0)
    (fun i => counted_iterations (memory_cut_point instruction a b c i) columns 0)
    0 (Z.of_nat rows)).
  - intros i first final IBOUND; apply counted_memory_lift with (floor := 0) (upper := Z.of_nat columns).
    + intros; apply POINT; assumption.
    + intros; eapply memory_cut_point_locations; eauto.
    + lia.
    + lia.
  - intros i first final ROW; eapply counted_locations; [|exact ROW].
    intros; eapply memory_cut_point_locations; eauto.
  - lia.
  - lia.
Qed.
Print Assumptions memory_cut_rectangle_lift.
