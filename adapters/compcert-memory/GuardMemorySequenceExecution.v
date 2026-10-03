From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation.
From polcert.lib Require Import Linalg LinalgExt Misc ListExt ImpureAlarmConfig.
From polcert.src Require Import Base.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryLoops
  GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles GuardMemoryLoopTrace GuardMemoryIndexedTrace
  GuardMemoryTilingProgress GuardMemoryTilingMultipleProgress GuardMemoryTiledRectangles GuardMemorySequenceLoops
  GuardMemorySequencePolyhedral GuardMemorySequenceOrder.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma indexed_memory_trace_points events (emit : indexed_memory_event -> PL.InstrPoint) :
  (forall event before after, In event events ->
    (indexed_memory_event_step event before after <-> PL.instr_point_sema (emit event) before after)) ->
  forall before after, Iter.iter_semantics indexed_memory_event_step events before after <->
    PL.instr_point_list_semantics (map emit events) before after.
Proof.
  induction events as [|event events IH]; intros CORRECT before after; cbn; split; intro RUN.
  - inversion RUN; subst; constructor; reflexivity.
  - inversion RUN; subst; unfold GuardMemoryInstr.State.eq in *; subst; constructor.
  - inversion RUN; subst; econstructor.
    + apply CORRECT; [left; reflexivity|eassumption].
    + apply IH; [intros; apply CORRECT; right; assumption|eassumption].
  - inversion RUN; subst; econstructor.
    + apply CORRECT; [left; reflexivity|eassumption].
    + apply IH; [intros; apply CORRECT; right; assumption|eassumption].
Qed.
Lemma indexed_memory_sequence_map {A} (emit : indexed_memory_event -> A) instructions : forall base env,
  map emit (indexed_memory_list_trace base (memory_instruction_sequence instructions) env) =
  memory_site_points base (fun site instruction => emit (IndexedMemoryEvent site
    (MemoryLoopEvent instruction env [L.eval_expr env (L.Var 1);L.eval_expr env (L.Var 0)]))) instructions.
Proof.
  induction instructions; intros base env; cbn; [reflexivity|].
  replace (base+1)%nat with (S base) by lia; rewrite IHinstructions; reflexivity.
Qed.
Lemma memory_guarded_flat_list {A B} (keep : A -> bool) (f : A -> list B) xs :
  flat_map (fun x => if keep x then f x else []) xs = flat_map f (filter keep xs).
Proof. induction xs; cbn; [reflexivity|destruct (keep a); cbn; rewrite IHxs; reflexivity]. Qed.
Definition memory_sequence_source_event n m event :=
  let payload := indexed_event_payload event in
  memory_sequence_source_point (indexed_event_site event) (event_instruction payload) n m
    (nth 1 (event_environment payload) 0) (nth 0 (event_environment payload) 0).
Definition memory_sequence_tiled_event n m event :=
  let payload := indexed_event_payload event in
  memory_sequence_tiled_point (indexed_event_site event) (event_instruction payload) n m
    (nth 3 (event_environment payload) 0) (nth 2 (event_environment payload) 0)
    (nth 1 (event_environment payload) 0) (nth 0 (event_environment payload) 0).
Lemma memory_sequence_source_trace_points instructions n m :
  map (memory_sequence_source_event n m)
    (indexed_memory_loop_trace O (memory_rectangle_sequence instructions) [n;m]) =
  memory_sequence_source_points instructions n m.
Proof.
  unfold memory_rectangle_sequence,memory_sequence_source_points.
  cbn -[Zrange indexed_memory_list_trace memory_instruction_sequence memory_sequence_source_event memory_site_points].
  rewrite memory_map_flat_map; apply flat_map_ext; intro i.
  rewrite memory_map_flat_map; apply flat_map_ext; intro j.
  rewrite indexed_memory_sequence_map; reflexivity.
Qed.
Lemma memory_sequence_tiled_trace_points instructions n m bi bj :
  map (memory_sequence_tiled_event n m)
    (indexed_memory_loop_trace O (memory_tiled_sequence instructions bi bj) [n;m]) =
  memory_sequence_tiled_points instructions n m bi bj.
Proof.
  unfold memory_tiled_sequence,memory_tiled_sequence_tj,memory_tiled_sequence_i,memory_tiled_sequence_j,
    memory_tiled_sequence_body,rectangle_tiled_tail,memory_sequence_tiled_points,
    memory_sequence_tiled_tj_points,memory_sequence_tiled_i_points,memory_sequence_tiled_j_points,rectangle_tile_count.
  cbn -[Zrange Z.add Z.mul Z.sub Z.div Z.leb indexed_memory_list_trace memory_instruction_sequence
    memory_sequence_tiled_event memory_site_points].
  replace (n+(bi-1)) with (n+bi-1) by ring.
  replace (m+(bj-1)) with (m+bj-1) by ring.
  rewrite memory_map_flat_map; apply flat_map_ext; intro ti.
  rewrite memory_map_flat_map; apply flat_map_ext; intro tj.
  replace (bi*ti+bi) with (bi*(ti+1)) by ring.
  rewrite memory_map_flat_map; apply flat_map_ext; intro i.
  replace (bj*tj+bj) with (bj*(tj+1)) by ring.
  rewrite memory_map_flat_map,<-memory_guarded_flat_list.
  apply flat_map_ext; intro j.
  change (map (memory_sequence_tiled_event n m)
    (if rectangle_tiled_keep n m i j then indexed_memory_list_trace O
      (memory_instruction_sequence instructions) [j;i;tj;ti;n;m] else []) =
    if rectangle_tiled_keep n m i j then memory_site_points O
      (fun site instruction => memory_sequence_tiled_point site instruction n m ti tj i j) instructions else []).
  destruct (rectangle_tiled_keep n m i j); [rewrite indexed_memory_sequence_map|]; reflexivity.
Qed.
Lemma memory_sequence_source_trace_members instructions n m event :
  In event (indexed_memory_loop_trace O (memory_rectangle_sequence instructions) [n;m]) ->
  exists site instruction i j, event = IndexedMemoryEvent site (MemoryLoopEvent instruction [j;i;n;m] [i;j]).
Proof.
  unfold memory_rectangle_sequence.
  cbn -[Zrange indexed_memory_list_trace memory_instruction_sequence].
  intro MEMBER; apply in_flat_map in MEMBER as [i [_ MEMBER]].
  apply in_flat_map in MEMBER as [j [_ MEMBER]].
  apply indexed_memory_sequence_member in MEMBER as [site [instruction [_ ->]]].
  exists site,instruction,i,j; reflexivity.
Qed.
Lemma memory_sequence_tiled_trace_members instructions n m bi bj event :
  In event (indexed_memory_loop_trace O (memory_tiled_sequence instructions bi bj) [n;m]) ->
  exists site instruction ti tj i j, event = IndexedMemoryEvent site (MemoryLoopEvent instruction [j;i;tj;ti;n;m] [i;j]).
Proof.
  unfold memory_tiled_sequence,memory_tiled_sequence_tj,memory_tiled_sequence_i,memory_tiled_sequence_j,
    memory_tiled_sequence_body,rectangle_tiled_tail.
  cbn -[Zrange Z.add Z.mul Z.sub Z.div Z.leb indexed_memory_list_trace memory_instruction_sequence].
  intro MEMBER.
  apply in_flat_map in MEMBER as [ti [_ MEMBER]].
  apply in_flat_map in MEMBER as [tj [_ MEMBER]].
  apply in_flat_map in MEMBER as [i [_ MEMBER]].
  apply in_flat_map in MEMBER as [j [_ MEMBER]].
  destruct ((i <=? n + -1) && (j <=? m + -1)); [|contradiction].
  apply indexed_memory_sequence_member in MEMBER as [site [instruction [_ ->]]].
  exists site,instruction,ti,tj,i,j; reflexivity.
Qed.
Lemma memory_sequence_event_execution site instruction i j rest before after :
  indexed_memory_event_step (IndexedMemoryEvent site (MemoryLoopEvent instruction (j::i::rest) [i;j])) before after <->
  memory_point instruction i j before after.
Proof.
  unfold indexed_memory_event_step,memory_event_step; cbn; split.
  - intros [writes [reads [WRITES [READS RUN]]]]; subst writes reads; repeat split; assumption || reflexivity.
  - intro RUN; exists (memory_write_cells instruction [i;j]),(memory_read_cells instruction [i;j]); exact RUN.
Qed.
Theorem memory_sequence_source_loop_points instructions n m before after :
  L.loop_semantics (memory_rectangle_sequence instructions) [n;m] before after <->
  PL.instr_point_list_semantics (memory_sequence_source_points instructions n m) before after.
Proof.
  rewrite (indexed_memory_loop_execution _ O),<-memory_sequence_source_trace_points.
  apply indexed_memory_trace_points; intros event first final MEMBER.
  apply memory_sequence_source_trace_members in MEMBER as [site [instruction [i [j ->]]]].
  change (indexed_memory_event_step (IndexedMemoryEvent site (MemoryLoopEvent instruction [j;i;n;m] [i;j])) first final <->
    PL.instr_point_sema (memory_sequence_source_point site instruction n m i j) first final).
  rewrite memory_sequence_source_point_exec; apply memory_sequence_event_execution.
Qed.
Theorem memory_sequence_tiled_loop_points instructions n m bi bj before after :
  L.loop_semantics (memory_tiled_sequence instructions bi bj) [n;m] before after <->
  PL.instr_point_list_semantics (memory_sequence_tiled_points instructions n m bi bj) before after.
Proof.
  rewrite (indexed_memory_loop_execution _ O),<-memory_sequence_tiled_trace_points.
  apply indexed_memory_trace_points; intros event first final MEMBER.
  apply memory_sequence_tiled_trace_members in MEMBER as [site [instruction [ti [tj [i [j ->]]]]]].
  change (indexed_memory_event_step (IndexedMemoryEvent site (MemoryLoopEvent instruction [j;i;tj;ti;n;m] [i;j])) first final <->
    PL.instr_point_sema (memory_sequence_tiled_point site instruction n m ti tj i j) first final).
  rewrite memory_sequence_tiled_point_exec; apply memory_sequence_event_execution.
Qed.

Theorem memory_sequence_source_loop_to_poly instructions stride n m before after :
  m <= stride -> L.loop_semantics (memory_rectangle_sequence instructions) [n;m] before after ->
  PL.poly_instance_list_semantics [n;m] (memory_sequence_source_program instructions stride) before after.
Proof.
  intros STRIDE RUN.
  pose proof (@memory_sequence_source_points_strongly_sorted instructions n m) as ORDER.
  destruct (memory_sequence_strict_order_properties ORDER) as [NODUP [SORTED UNIQUE]].
  destruct (@memory_sequence_ordered_flatten [n;m] (memory_sequence_source_instructions O instructions stride)
    (memory_sequence_source_points instructions n m)
    ltac:(intros; apply memory_sequence_source_coverage; exact STRIDE) NODUP)
    as [flattened [FLAT PERM]].
  eapply PL.PolyPointListSema with (ipl := flattened)
    (sorted_ipl := memory_sequence_source_points instructions n m).
  - reflexivity.
  - exact FLAT.
  - exact PERM.
  - exact SORTED.
  - apply memory_sequence_source_loop_points; exact RUN.
Qed.
Theorem memory_sequence_tiled_poly_to_loop instructions stride n m bi bj before after :
  0 < bi -> 0 < bj -> m <= stride ->
  PL.poly_instance_list_semantics [n;m] (memory_sequence_tiled_program instructions stride bi bj) before after ->
  L.loop_semantics (memory_tiled_sequence instructions bi bj) [n;m] before after.
Proof.
  intros BI BJ STRIDE EXEC.
  pose proof (@memory_sequence_tiled_points_strongly_sorted instructions n m bi bj) as ORDER.
  destruct (memory_sequence_strict_order_properties ORDER) as [NODUP [SORTED UNIQUE]].
  destruct (@memory_sequence_ordered_flatten [n;m] (memory_sequence_tiled_instructions O instructions stride bi bj)
    (memory_sequence_tiled_points instructions n m bi bj)
    ltac:(intros; apply memory_sequence_tiled_coverage; assumption) NODUP)
    as [canonical [FLATTEN PERMUTE]].
  inversion EXEC as [params program pis context vars initial final flattened ordered PROGRAM FLAT PERM SORTED' RUN]; subst.
  unfold memory_sequence_tiled_program in PROGRAM; inversion PROGRAM; subst pis context vars; clear PROGRAM.
  assert (CANONICAL : flattened = canonical) by (eapply PL.flatten_instrs_det; eauto).
  subst flattened.
  assert (SAME : memory_sequence_tiled_points instructions n m bi bj = ordered).
  { apply memory_sorted_permutation_unique; auto.
    eapply Permutation_trans; [symmetry; exact PERMUTE|exact PERM]. }
  subst ordered; apply memory_sequence_tiled_loop_points; exact RUN.
Qed.
Theorem validated_memory_sequence_tiling instructions stride bi bj n m before after :
  0 < bi -> 0 < bj -> m <= stride -> GuardMemoryInstr.NonAlias before ->
  mayReturn (validate_memory_tiling_equivalence
    (memory_sequence_source_program instructions stride)
    (memory_sequence_tiled_program instructions stride bi bj)
    (repeat (rectangle_tiling_witness bi bj) (length instructions))) true ->
  L.loop_semantics (memory_rectangle_sequence instructions) [n;m] before after ->
  L.loop_semantics (memory_tiled_sequence instructions bi bj) [n;m] before after.
Proof.
  intros BI BJ STRIDE NONALIAS CHECK SOURCE.
  apply memory_sequence_tiled_poly_to_loop with (stride := stride); [exact BI|exact BJ|exact STRIDE|].
  unfold memory_sequence_source_program,memory_sequence_tiled_program in CHECK |- *.
  eapply validated_memory_multiple_tiling_progress_at; [reflexivity|exact NONALIAS|exact CHECK|].
  apply memory_sequence_source_loop_to_poly; assumption.
Qed.
Print Assumptions memory_sequence_source_loop_to_poly.
Print Assumptions memory_sequence_tiled_poly_to_loop.
Print Assumptions validated_memory_sequence_tiling.
