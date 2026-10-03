From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation.
From polcert.lib Require Import Misc ListExt Linalg LinalgExt ImpureAlarmConfig.
From polcert.src Require Import Base.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryLoops GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemoryLoopTrace GuardMemoryTilingProgress GuardMemoryTiledRectangles.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition rectangle_tiled_event_point instruction n m event :=
  rectangle_tiled_point instruction n m
    (nth 3 (event_environment event) 0) (nth 2 (event_environment event) 0)
    (nth 1 (event_environment event) 0) (nth 0 (event_environment event) 0).

Lemma rectangle_tiled_trace_points instruction n m bi bj :
  map (rectangle_tiled_event_point instruction n m)
    (memory_loop_trace (rectangle_tiled_loop instruction bi bj) [n;m]) =
  rectangle_tiled_points instruction n m bi bj.
Proof.
  unfold rectangle_tiled_loop, rectangle_tiled_tj_loop, rectangle_tiled_i_loop,
    rectangle_tiled_j_loop, rectangle_tiled_body, rectangle_tiled_tail,
    rectangle_tiled_points, rectangle_tiled_tj_points, rectangle_tiled_i_points,
    rectangle_tiled_j_points, rectangle_tile_count.
  cbn -[Zrange Z.add Z.mul Z.sub Z.div Z.leb rectangle_tiled_point].
  replace (n + (bi-1)) with (n+bi-1) by ring.
  replace (m + (bj-1)) with (m+bj-1) by ring.
  rewrite memory_map_flat_map; apply flat_map_ext; intro ti.
  rewrite memory_map_flat_map; apply flat_map_ext; intro tj.
  replace (bi*ti+bi) with (bi*(ti+1)) by ring.
  rewrite memory_map_flat_map; apply flat_map_ext; intro i.
  replace (bj*tj+bj) with (bj*(tj+1)) by ring.
  rewrite memory_map_flat_map, <- memory_guarded_list.
  apply flat_map_ext; intro j.
  change (map (rectangle_tiled_event_point instruction n m)
    (if rectangle_tiled_keep n m i j
     then [MemoryLoopEvent instruction [j;i;tj;ti;n;m] [i;j]] else []) =
    if rectangle_tiled_keep n m i j then [rectangle_tiled_point instruction n m ti tj i j] else []).
  destruct (rectangle_tiled_keep n m i j); reflexivity.
Qed.

Lemma rectangle_tiled_trace_members instruction n m bi bj event :
  In event (memory_loop_trace (rectangle_tiled_loop instruction bi bj) [n;m]) ->
  exists ti tj i j, event = MemoryLoopEvent instruction [j;i;tj;ti;n;m] [i;j].
Proof.
  unfold rectangle_tiled_loop, rectangle_tiled_tj_loop, rectangle_tiled_i_loop,
    rectangle_tiled_j_loop, rectangle_tiled_body, rectangle_tiled_tail.
  cbn -[Zrange Z.add Z.mul Z.sub Z.div Z.leb].
  intro MEMBER.
  apply in_flat_map in MEMBER as [ti [_ MEMBER]].
  apply in_flat_map in MEMBER as [tj [_ MEMBER]].
  apply in_flat_map in MEMBER as [i [_ MEMBER]].
  apply in_flat_map in MEMBER as [j [_ MEMBER]].
  destruct ((i <=? n + -1) && (j <=? m + -1)) eqn:KEEP;
    cbn in MEMBER; [|contradiction].
  destruct MEMBER as [SAME|ABSENT]; [|contradiction].
  exists ti,tj,i,j; symmetry; exact SAME.
Qed.

Lemma rectangle_tiled_event_execution instruction n m ti tj i j before after :
  memory_event_step (MemoryLoopEvent instruction [j;i;tj;ti;n;m] [i;j]) before after <->
  PL.instr_point_sema (rectangle_tiled_point instruction n m ti tj i j) before after.
Proof.
  rewrite rectangle_tiled_point_exec; unfold memory_event_step; cbn; split.
  - intros [writes [reads [WRITES [READS RUN]]]]; subst writes reads; repeat split; assumption || reflexivity.
  - intro RUN; exists (memory_write_cells instruction [i;j]), (memory_read_cells instruction [i;j]); exact RUN.
Qed.

Theorem rectangle_tiled_loop_points instruction n m bi bj before after :
  L.loop_semantics (rectangle_tiled_loop instruction bi bj) [n;m] before after <->
  PL.instr_point_list_semantics (rectangle_tiled_points instruction n m bi bj) before after.
Proof.
  rewrite memory_loop_trace_correct, <- rectangle_tiled_trace_points.
  apply memory_trace_points; intros event first final MEMBER.
  apply rectangle_tiled_trace_members in MEMBER as [ti [tj [i [j ->]]]].
  change (memory_event_step (MemoryLoopEvent instruction [j;i;tj;ti;n;m] [i;j]) first final <->
    PL.instr_point_sema (rectangle_tiled_point instruction n m ti tj i j) first final).
  apply rectangle_tiled_event_execution.
Qed.

Print Assumptions rectangle_tiled_loop_points.

Lemma memory_four_timestamp_eq a b c d a' b' c' d' :
  lex_compare [a;b;c;d] [a';b';c';d'] = Eq -> a=a' /\ b=b' /\ c=c' /\ d=d'.
Proof.
  unfold lex_compare.
  destruct (Z.compare a a') eqn:A; try discriminate.
  destruct (Z.compare b b') eqn:B; try discriminate.
  destruct (Z.compare c c') eqn:C; try discriminate.
  destruct (Z.compare d d') eqn:D; try discriminate.
  intro EQ; repeat split; apply Z.compare_eq_iff; assumption.
Qed.
Lemma rectangle_tiled_timestamp_unique instruction n m bi bj first second :
  In first (rectangle_tiled_points instruction n m bi bj) ->
  In second (rectangle_tiled_points instruction n m bi bj) ->
  PL.ILSema.instr_point_sched_eq first second -> first = second.
Proof.
  intros FIRST SECOND EQ.
  apply rectangle_tiled_members in FIRST as [ti [tj [i [j [-> _]]]]].
  apply rectangle_tiled_members in SECOND as [ti' [tj' [i' [j' [-> _]]]]].
  unfold PL.ILSema.instr_point_sched_eq, PL.ILSema.instr_point_sched_eqb in EQ.
  apply comparison_eqb_iff_eq in EQ.
  change (lex_compare [ti;tj;i;j] [ti';tj';i';j'] = Eq) in EQ.
  apply memory_four_timestamp_eq in EQ as [-> [-> [-> ->]]]; reflexivity.
Qed.

Theorem rectangle_tiled_poly_to_loop instruction stride n m bi bj before after :
  0 < bi -> 0 < bj -> m <= stride ->
  PL.poly_instance_list_semantics [n;m] (rectangle_tiled_program instruction stride bi bj) before after ->
  L.loop_semantics (rectangle_tiled_loop instruction bi bj) [n;m] before after.
Proof.
  intros BI BJ STRIDE EXEC.
  inversion EXEC as [params program pis context vars initial final flattened ordered PROGRAM FLAT PERM SORTED RUN]; subst.
  unfold rectangle_tiled_program in PROGRAM; inversion PROGRAM; subst pis context vars; clear PROGRAM.
  assert (CANONICAL : flattened = rectangle_tiled_points instruction n m bi bj).
  { eapply PL.flatten_instrs_det; [exact FLAT|apply rectangle_tiled_flatten; assumption]. }
  subst flattened.
  assert (ORDER : rectangle_tiled_points instruction n m bi bj = ordered).
  { apply memory_sorted_permutation_unique.
    - pose proof (@rectangle_tiled_points_sorted instruction n m bi bj); tauto.
    - pose proof (@rectangle_tiled_points_sorted instruction n m bi bj); tauto.
    - intros; eapply rectangle_tiled_timestamp_unique; eauto.
    - exact PERM.
    - exact SORTED. }
  subst ordered; apply rectangle_tiled_loop_points; exact RUN.
Qed.

Theorem validated_memory_rectangle_tiling instruction stride bi bj rows columns before after :
  0 < bi -> 0 < bj -> Z.of_nat columns <= stride -> GuardMemoryInstr.NonAlias before ->
  mayReturn (validate_memory_tiling_equivalence
    (rectangle_poly_program instruction stride rectangle_row_schedule)
    (rectangle_tiled_program instruction stride bi bj) [rectangle_tiling_witness bi bj]) true ->
  L.loop_semantics (memory_rectangle_loop instruction) [Z.of_nat rows;Z.of_nat columns] before after ->
  L.loop_semantics (rectangle_tiled_loop instruction bi bj) [Z.of_nat rows;Z.of_nat columns] before after.
Proof.
  intros BI BJ STRIDE NONALIAS CHECK SOURCE.
  apply rectangle_tiled_poly_to_loop with (stride := stride); [exact BI|exact BJ|exact STRIDE|].
  unfold rectangle_poly_program, rectangle_tiled_program in CHECK |- *.
  eapply validated_memory_single_tiling_progress_at; [reflexivity|exact NONALIAS|exact CHECK|].
  apply memory_rectangle_loop_to_poly; assumption.
Qed.

Print Assumptions rectangle_tiled_poly_to_loop.
Print Assumptions validated_memory_rectangle_tiling.
