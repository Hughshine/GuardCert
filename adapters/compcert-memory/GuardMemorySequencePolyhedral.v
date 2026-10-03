From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation.
From polcert.lib Require Import Linalg LinalgExt Misc.
From polcert.src Require Import PointWitness Base.
From Guard Require Import RectangularSchedule RectangularIteration.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemoryRectangles GuardMemoryLoopTrace GuardMemoryIndexedTrace GuardMemorySequenceLoops
  GuardMemoryPolyhedralRectangles GuardMemoryTiledRectangles GuardMemoryTilingMultipleProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition append_memory_site_schedule dimensions site (instruction : PL.PolyInstr) : PL.PolyInstr :=
  {| PL.pi_depth := PL.pi_depth instruction; PL.pi_instr := PL.pi_instr instruction;
     PL.pi_poly := PL.pi_poly instruction;
     PL.pi_schedule := PL.pi_schedule instruction ++ [(repeat 0 dimensions,Z.of_nat site)];
     PL.pi_point_witness := PL.pi_point_witness instruction;
     PL.pi_transformation := PL.pi_transformation instruction;
     PL.pi_access_transformation := PL.pi_access_transformation instruction;
     PL.pi_waccess := PL.pi_waccess instruction; PL.pi_raccess := PL.pi_raccess instruction |}.
Fixpoint memory_sequence_source_instructions site instructions stride : list PL.PolyInstr :=
  match instructions with
  | [] => []
  | instruction::rest => append_memory_site_schedule 4 site
      (rectangle_poly_instruction instruction stride rectangle_row_schedule) ::
      memory_sequence_source_instructions (S site) rest stride
  end.
Fixpoint memory_sequence_tiled_instructions site instructions stride bi bj : list PL.PolyInstr :=
  match instructions with
  | [] => []
  | instruction::rest => append_memory_site_schedule 6 site
      (rectangle_tiled_instruction instruction stride bi bj) ::
      memory_sequence_tiled_instructions (S site) rest stride bi bj
  end.
Definition memory_sequence_source_program instructions stride : PL.t :=
  (memory_sequence_source_instructions O instructions stride,[1%positive;2%positive],
   [(1%positive,tt);(2%positive,tt);(3%positive,tt)]).
Definition memory_sequence_tiled_program instructions stride bi bj : PL.t :=
  (memory_sequence_tiled_instructions O instructions stride bi bj,[1%positive;2%positive],
   [(1%positive,tt);(2%positive,tt);(3%positive,tt)]).
Definition memory_sequence_source_point site instruction n m i j : PL.InstrPoint :=
  {| PL.ILSema.ip_nth := site; PL.ILSema.ip_index := [n;m;i;j];
     PL.ILSema.ip_transformation := rectangle_projection;
     PL.ILSema.ip_time_stamp := [i;j;Z.of_nat site]; PL.ILSema.ip_instruction := instruction;
     PL.ILSema.ip_depth := 2 |}.
Definition memory_sequence_tiled_point site instruction n m ti tj i j : PL.InstrPoint :=
  {| PL.ILSema.ip_nth := site; PL.ILSema.ip_index := [n;m;ti;tj;i;j];
     PL.ILSema.ip_transformation := rectangle_tiled_projection;
     PL.ILSema.ip_time_stamp := [ti;tj;i;j;Z.of_nat site]; PL.ILSema.ip_instruction := instruction;
     PL.ILSema.ip_depth := 4 |}.

Lemma dot_product_repeat_zero dimensions xs : dot_product (repeat 0 dimensions) xs = 0.
Proof. revert xs; induction dimensions; intros xs; destruct xs; cbn; auto. Qed.
Lemma appended_site_schedule_at dimensions site schedule index :
  affine_product (schedule ++ [(repeat 0 dimensions,Z.of_nat site)]) index =
  affine_product schedule index ++ [Z.of_nat site].
Proof. unfold affine_product; rewrite map_app; cbn; rewrite dot_product_repeat_zero; reflexivity. Qed.
Lemma memory_sequence_source_schedule site n m i j :
  affine_product (rectangle_row_schedule ++ [(repeat 0 4,Z.of_nat site)]) [n;m;i;j] = [i;j;Z.of_nat site].
Proof. rewrite appended_site_schedule_at,row_schedule_at; reflexivity. Qed.
Lemma memory_sequence_tiled_schedule site n m ti tj i j :
  affine_product (rectangle_tiled_schedule ++ [(repeat 0 6,Z.of_nat site)]) [n;m;ti;tj;i;j] = [ti;tj;i;j;Z.of_nat site].
Proof. rewrite appended_site_schedule_at,tiled_schedule_at; reflexivity. Qed.
Lemma memory_sequence_source_instruction_nth instructions : forall base stride position instruction,
  nth_error instructions position = Some instruction ->
  nth_error (memory_sequence_source_instructions base instructions stride) position = Some
    (append_memory_site_schedule 4 (base+position)%nat (rectangle_poly_instruction instruction stride rectangle_row_schedule)).
Proof.
  induction instructions; intros base stride position instruction NTH; destruct position; cbn in NTH |- *;
    try discriminate; [inversion NTH; subst a; rewrite Nat.add_0_r; reflexivity|].
  rewrite (IHinstructions (S base) stride position instruction NTH); f_equal; f_equal; lia.
Qed.
Lemma memory_sequence_tiled_instruction_nth instructions : forall base stride bi bj position instruction,
  nth_error instructions position = Some instruction ->
  nth_error (memory_sequence_tiled_instructions base instructions stride bi bj) position = Some
    (append_memory_site_schedule 6 (base+position)%nat (rectangle_tiled_instruction instruction stride bi bj)).
Proof.
  induction instructions; intros base stride bi bj position instruction NTH; destruct position; cbn in NTH |- *;
    try discriminate; [inversion NTH; subst a; rewrite Nat.add_0_r; reflexivity|].
  rewrite (IHinstructions (S base) stride bi bj position instruction NTH); f_equal; f_equal; lia.
Qed.

Lemma memory_sequence_source_point_exec site instruction n m i j before after :
  PL.instr_point_sema (memory_sequence_source_point site instruction n m i j) before after <->
  memory_point instruction i j before after.
Proof.
  split.
  - intro RUN; inversion RUN as [writes reads EXECUTION].
    change (GuardMemoryInstr.instr_semantics instruction
      (affine_product rectangle_projection [n;m;i;j]) writes reads before after) in EXECUTION.
    rewrite projection_at in EXECUTION.
    destruct EXECUTION as [WRITES [READS EXECUTION]]; subst writes reads; repeat split; assumption || reflexivity.
  - intro RUN; apply PL.ILSema.ip_sema_intro with
      (wcs := memory_write_cells instruction [i;j]) (rcs := memory_read_cells instruction [i;j]).
    change (GuardMemoryInstr.instr_semantics instruction (affine_product rectangle_projection [n;m;i;j]) (memory_write_cells instruction [i;j]) (memory_read_cells instruction [i;j]) before after).
    rewrite projection_at; exact RUN.
Qed.
Lemma memory_sequence_tiled_point_exec site instruction n m ti tj i j before after :
  PL.instr_point_sema (memory_sequence_tiled_point site instruction n m ti tj i j) before after <->
  memory_point instruction i j before after.
Proof.
  split.
  - intro RUN; inversion RUN as [writes reads EXECUTION].
    change (GuardMemoryInstr.instr_semantics instruction
      (affine_product rectangle_tiled_projection [n;m;ti;tj;i;j]) writes reads before after) in EXECUTION.
    rewrite tiled_projection_at in EXECUTION.
    destruct EXECUTION as [WRITES [READS EXECUTION]]; subst writes reads; repeat split; assumption || reflexivity.
  - intro RUN; apply PL.ILSema.ip_sema_intro with
      (wcs := memory_write_cells instruction [i;j]) (rcs := memory_read_cells instruction [i;j]).
    change (GuardMemoryInstr.instr_semantics instruction (affine_product rectangle_tiled_projection [n;m;ti;tj;i;j]) (memory_write_cells instruction [i;j]) (memory_read_cells instruction [i;j]) before after).
    rewrite tiled_projection_at; exact RUN.
Qed.

Lemma memory_sequence_source_point_belongs site instruction stride n m i j :
  PL.belongs_to (memory_sequence_source_point site instruction n m i j)
    (append_memory_site_schedule 4 site (rectangle_poly_instruction instruction stride rectangle_row_schedule)) <->
  0 <= i < n /\ 0 <= j < m /\ m <= stride.
Proof.
  unfold PL.belongs_to.
  change ((in_poly [n;m;i;j] (rectangle_domain stride) = true /\
    rectangle_projection = rectangle_projection /\
    [i;j;Z.of_nat site] = affine_product (rectangle_row_schedule ++ [(repeat 0 4,Z.of_nat site)]) [n;m;i;j] /\
    instruction = instruction /\ 2%nat = 2%nat) <-> (0 <= i < n /\ 0 <= j < m /\ m <= stride)).
  rewrite memory_sequence_source_schedule, rectangle_domain_at; tauto.
Qed.
Lemma memory_sequence_tiled_point_belongs site instruction stride bi bj n m ti tj i j :
  PL.belongs_to (memory_sequence_tiled_point site instruction n m ti tj i j)
    (append_memory_site_schedule 6 site (rectangle_tiled_instruction instruction stride bi bj)) <->
  0 <= i < n /\ 0 <= j < m /\ m <= stride /\
  bi*ti <= i < bi*(ti+1) /\ bj*tj <= j < bj*(tj+1).
Proof.
  unfold PL.belongs_to.
  change ((in_poly [n;m;ti;tj;i;j] (rectangle_tiled_domain stride bi bj) = true /\
    rectangle_tiled_projection = rectangle_tiled_projection /\
    [ti;tj;i;j;Z.of_nat site] = affine_product (rectangle_tiled_schedule ++ [(repeat 0 6,Z.of_nat site)]) [n;m;ti;tj;i;j] /\
    instruction = instruction /\ 4%nat = 4%nat) <-> (0 <= i < n /\ 0 <= j < m /\ m <= stride /\ bi*ti <= i < bi*(ti+1) /\ bj*tj <= j < bj*(tj+1))).
  rewrite memory_sequence_tiled_schedule, rectangle_tiled_domain_at; tauto.
Qed.
Print Assumptions memory_sequence_source_point_belongs.
Print Assumptions memory_sequence_tiled_point_belongs.

Fixpoint memory_site_points {A} base (emit : nat -> GuardMemoryInstr.t -> A) instructions : list A :=
  match instructions with
  | [] => []
  | instruction::rest => emit base instruction :: memory_site_points (S base) emit rest
  end.
Lemma memory_site_points_members {A} (emit : nat -> GuardMemoryInstr.t -> A) instructions : forall base point,
  In point (memory_site_points base emit instructions) <->
  exists position instruction, nth_error instructions position = Some instruction /\ point = emit (base+position)%nat instruction.
Proof.
  induction instructions as [|instruction instructions IH]; intros base point; cbn; split.
  - contradiction.
  - intros [position [inst [ABSENT _]]]; rewrite nth_error_nil in ABSENT; discriminate.
  - intros [FIRST|REST].
    + exists O,instruction; split; [reflexivity|]; rewrite Nat.add_0_r; symmetry; exact FIRST.
    + apply IH in REST as [position [inst [NTH ->]]].
      exists (S position),inst; split; [exact NTH|f_equal; lia].
  - intros [position [inst [NTH ->]]]; destruct position.
    + inversion NTH; subst inst; left; rewrite Nat.add_0_r; reflexivity.
    + right; apply IH; exists position,inst; split; [exact NTH|f_equal; lia].
Qed.
Definition memory_sequence_source_points instructions n m :=
  flat_map (fun i => flat_map (fun j =>
    memory_site_points O (fun site instruction => memory_sequence_source_point site instruction n m i j) instructions)
    (Zrange 0 m)) (Zrange 0 n).
Definition memory_sequence_tiled_j_points instructions n m ti tj i bj :=
  flat_map (fun j => memory_site_points O
    (fun site instruction => memory_sequence_tiled_point site instruction n m ti tj i j) instructions)
    (filter (rectangle_tiled_keep n m i) (Zrange (bj*tj) (bj*(tj+1)))).
Definition memory_sequence_tiled_i_points instructions n m ti tj bi bj :=
  flat_map (fun i => memory_sequence_tiled_j_points instructions n m ti tj i bj)
    (Zrange (bi*ti) (bi*(ti+1))).
Definition memory_sequence_tiled_tj_points instructions n m ti bi bj :=
  flat_map (fun tj => memory_sequence_tiled_i_points instructions n m ti tj bi bj)
    (Zrange 0 (rectangle_tile_count m bj)).
Definition memory_sequence_tiled_points instructions n m bi bj :=
  flat_map (fun ti => memory_sequence_tiled_tj_points instructions n m ti bi bj)
    (Zrange 0 (rectangle_tile_count n bi)).
Lemma memory_sequence_source_points_members instructions n m point :
  In point (memory_sequence_source_points instructions n m) <->
  exists site instruction i j, nth_error instructions site = Some instruction /\
    point = memory_sequence_source_point site instruction n m i j /\ 0 <= i < n /\ 0 <= j < m.
Proof.
  unfold memory_sequence_source_points; split.
  - intro MEMBER; apply in_flat_map in MEMBER as [i [I MEMBER]].
    apply in_flat_map in MEMBER as [j [J MEMBER]].
    apply memory_site_points_members in MEMBER as [site [instruction [NTH ->]]].
    exists site,instruction,i,j; repeat split; auto; apply Zrange_in in I,J; lia.
  - intros [site [instruction [i [j [NTH [-> [I J]]]]]]].
    apply in_flat_map; exists i; split; [apply Zrange_in; exact I|].
    apply in_flat_map; exists j; split; [apply Zrange_in; exact J|].
    apply memory_site_points_members; exists site,instruction; auto.
Qed.
Lemma memory_sequence_tiled_j_members instructions n m ti tj i bj point :
  In point (memory_sequence_tiled_j_points instructions n m ti tj i bj) <->
  exists site instruction j, nth_error instructions site = Some instruction /\
    point = memory_sequence_tiled_point site instruction n m ti tj i j /\
    bj*tj <= j < bj*(tj+1) /\ i < n /\ j < m.
Proof.
  unfold memory_sequence_tiled_j_points; split.
  - intro MEMBER; apply in_flat_map in MEMBER as [j [J MEMBER]].
    apply filter_In in J as [RANGE KEEP]; apply Zrange_in in RANGE.
    unfold rectangle_tiled_keep in KEEP; apply andb_true_iff in KEEP as [I J]; rewrite Z.leb_le in I,J.
    apply memory_site_points_members in MEMBER as [site [instruction [NTH ->]]].
    exists site,instruction,j; repeat split; auto; lia.
  - intros [site [instruction [j [NTH [-> [RANGE [I J]]]]]]].
    apply in_flat_map; exists j; split.
    + apply filter_In; split; [apply Zrange_in; exact RANGE|].
      unfold rectangle_tiled_keep; apply andb_true_iff; split; apply Z.leb_le; lia.
    + apply memory_site_points_members; exists site,instruction; auto.
Qed.
Lemma memory_sequence_tiled_i_members instructions n m ti tj bi bj point :
  In point (memory_sequence_tiled_i_points instructions n m ti tj bi bj) <->
  exists site instruction i j, nth_error instructions site = Some instruction /\
    point = memory_sequence_tiled_point site instruction n m ti tj i j /\
    bi*ti <= i < bi*(ti+1) /\ bj*tj <= j < bj*(tj+1) /\ i < n /\ j < m.
Proof.
  unfold memory_sequence_tiled_i_points; split.
  - intro MEMBER; apply in_flat_map in MEMBER as [i [I MEMBER]]; apply Zrange_in in I.
    apply memory_sequence_tiled_j_members in MEMBER as [site [instruction [j [NTH [-> BOUNDS]]]]].
    exists site,instruction,i,j; auto.
  - intros [site [instruction [i [j [NTH [-> [I BOUNDS]]]]]]].
    apply in_flat_map; exists i; split; [apply Zrange_in; exact I|].
    apply memory_sequence_tiled_j_members; exists site,instruction,j; auto.
Qed.
Lemma memory_sequence_tiled_tj_members instructions n m ti bi bj point :
  In point (memory_sequence_tiled_tj_points instructions n m ti bi bj) <->
  exists site instruction tj i j, nth_error instructions site = Some instruction /\
    point = memory_sequence_tiled_point site instruction n m ti tj i j /\
    0 <= tj < rectangle_tile_count m bj /\
    bi*ti <= i < bi*(ti+1) /\ bj*tj <= j < bj*(tj+1) /\ i < n /\ j < m.
Proof.
  unfold memory_sequence_tiled_tj_points; split.
  - intro MEMBER; apply in_flat_map in MEMBER as [tj [TJ MEMBER]]; apply Zrange_in in TJ.
    apply memory_sequence_tiled_i_members in MEMBER as [site [instruction [i [j [NTH [-> BOUNDS]]]]]].
    exists site,instruction,tj,i,j; auto.
  - intros [site [instruction [tj [i [j [NTH [-> [TJ BOUNDS]]]]]]]].
    apply in_flat_map; exists tj; split; [apply Zrange_in; exact TJ|].
    apply memory_sequence_tiled_i_members; exists site,instruction,i,j; auto.
Qed.
Lemma memory_sequence_tiled_members instructions n m bi bj point :
  In point (memory_sequence_tiled_points instructions n m bi bj) <->
  exists site instruction ti tj i j, nth_error instructions site = Some instruction /\
    point = memory_sequence_tiled_point site instruction n m ti tj i j /\
    0 <= ti < rectangle_tile_count n bi /\ 0 <= tj < rectangle_tile_count m bj /\
    bi*ti <= i < bi*(ti+1) /\ bj*tj <= j < bj*(tj+1) /\ i < n /\ j < m.
Proof.
  unfold memory_sequence_tiled_points; split.
  - intro MEMBER; apply in_flat_map in MEMBER as [ti [TI MEMBER]]; apply Zrange_in in TI.
    apply memory_sequence_tiled_tj_members in MEMBER as [site [instruction [tj [i [j [NTH [-> BOUNDS]]]]]]].
    exists site,instruction,ti,tj,i,j; auto.
  - intros [site [instruction [ti [tj [i [j [NTH [-> [TI BOUNDS]]]]]]]]].
    apply in_flat_map; exists ti; split; [apply Zrange_in; exact TI|].
    apply memory_sequence_tiled_tj_members; exists site,instruction,tj,i,j; auto.
Qed.
Lemma memory_sequence_tiled_domain_members instructions stride n m bi bj point :
  0 < bi -> 0 < bj -> m <= stride ->
  In point (memory_sequence_tiled_points instructions n m bi bj) <->
  exists site instruction ti tj i j, nth_error instructions site = Some instruction /\
    point = memory_sequence_tiled_point site instruction n m ti tj i j /\
    0 <= i < n /\ 0 <= j < m /\ bi*ti <= i < bi*(ti+1) /\ bj*tj <= j < bj*(tj+1).
Proof.
  intros BI BJ STRIDE; rewrite memory_sequence_tiled_members; split.
  - intros [site [instruction [ti [tj [i [j [NTH [-> [TI [TJ [I [J [N M]]]]]]]]]]]]];
      exists site,instruction,ti,tj,i,j; repeat split; auto; nia.
  - intros [site [instruction [ti [tj [i [j [NTH [-> [I [J [TILEI TILEJ]]]]]]]]]]];
      exists site,instruction,ti,tj,i,j; split; [exact NTH|]; split; [reflexivity|].
    assert (TI : ti = i / bi).
    { apply Z.div_unique with (r := i-bi*ti); [left; nia|ring]. }
    assert (TJ : tj = j / bj).
    { apply Z.div_unique with (r := j-bj*tj); [left; nia|ring]. }
    split; [rewrite TI; apply rectangle_tile_parent_in_range; assumption|].
    split; [rewrite TJ; apply rectangle_tile_parent_in_range; assumption|].
    tauto.
Qed.

Lemma memory_sequence_source_instruction_length instructions : forall base stride,
  length (memory_sequence_source_instructions base instructions stride) = length instructions.
Proof. induction instructions; cbn; auto. Qed.
Lemma memory_sequence_tiled_instruction_length instructions : forall base stride bi bj,
  length (memory_sequence_tiled_instructions base instructions stride bi bj) = length instructions.
Proof. induction instructions; cbn; auto. Qed.
Lemma memory_sequence_source_instruction_lookup instructions stride site pi :
  nth_error (memory_sequence_source_instructions O instructions stride) site = Some pi ->
  exists instruction, nth_error instructions site = Some instruction /\
    pi = append_memory_site_schedule 4 site (rectangle_poly_instruction instruction stride rectangle_row_schedule).
Proof.
  intro NTH.
  assert (BOUND : (site < length instructions)%nat).
  { rewrite <- (memory_sequence_source_instruction_length instructions O stride).
    apply nth_error_Some; rewrite NTH; discriminate. }
  destruct (nth_error instructions site) as [instruction|] eqn:INSTRUCTION.
  - exists instruction; split; [reflexivity|].
    rewrite (@memory_sequence_source_instruction_nth instructions O stride site instruction INSTRUCTION) in NTH.
    inversion NTH; reflexivity.
  - apply nth_error_None in INSTRUCTION; lia.
Qed.
Lemma memory_sequence_tiled_instruction_lookup instructions stride bi bj site pi :
  nth_error (memory_sequence_tiled_instructions O instructions stride bi bj) site = Some pi ->
  exists instruction, nth_error instructions site = Some instruction /\
    pi = append_memory_site_schedule 6 site (rectangle_tiled_instruction instruction stride bi bj).
Proof.
  intro NTH.
  assert (BOUND : (site < length instructions)%nat).
  { rewrite <- (memory_sequence_tiled_instruction_length instructions O stride bi bj).
    apply nth_error_Some; rewrite NTH; discriminate. }
  destruct (nth_error instructions site) as [instruction|] eqn:INSTRUCTION.
  - exists instruction; split; [reflexivity|].
    rewrite (@memory_sequence_tiled_instruction_nth instructions O stride bi bj site instruction INSTRUCTION) in NTH.
    inversion NTH; reflexivity.
  - apply nth_error_None in INSTRUCTION; lia.
Qed.
Definition memory_sequence_valid_point parameters instructions (point : PL.InstrPoint) :=
  exists instruction, nth_error instructions (PL.ILSema.ip_nth point) = Some instruction /\
    firstn (length parameters) (PL.ILSema.ip_index point) = parameters /\
    PL.belongs_to point instruction /\
    length (PL.ILSema.ip_index point) = (length parameters + PL.pi_depth instruction)%nat.

Lemma memory_sequence_source_coverage instructions stride n m point : m <= stride ->
  In point (memory_sequence_source_points instructions n m) <->
  memory_sequence_valid_point [n;m] (memory_sequence_source_instructions O instructions stride) point.
Proof.
  intro STRIDE; split.
  - intro MEMBER; apply memory_sequence_source_points_members in MEMBER
      as [site [instruction [i [j [NTH [-> [I J]]]]]]].
    exists (append_memory_site_schedule 4 site (rectangle_poly_instruction instruction stride rectangle_row_schedule)).
    split; [apply memory_sequence_source_instruction_nth; exact NTH|].
    split; [reflexivity|].
    split; [apply memory_sequence_source_point_belongs; tauto|].
    reflexivity.
  - intros [pi [NTH [PREFIX [BELONG LENGTH]]]].
    apply memory_sequence_source_instruction_lookup in NTH as [instruction [NTH ->]].
    destruct point as [site index transformation timestamp operation depth]; cbn in PREFIX,LENGTH,NTH,BELONG.
    destruct index as [|n' [|m' [|i [|j rest]]]]; cbn in PREFIX,LENGTH; try discriminate; try lia.
    inversion PREFIX; subst n' m'; clear PREFIX.
    assert (REST : rest = []) by (apply length_zero_iff_nil; cbn in LENGTH; lia); subst rest.
    unfold PL.belongs_to in BELONG.
    change (in_poly [n;m;i;j] (rectangle_domain stride) = true /\
      transformation = rectangle_projection /\
      timestamp = affine_product (rectangle_row_schedule ++ [(repeat 0 4,Z.of_nat site)]) [n;m;i;j] /\
      operation = instruction /\ depth = 2%nat) in BELONG.
    rewrite rectangle_domain_at,memory_sequence_source_schedule in BELONG.
    destruct BELONG as [DOMAIN [TRANS [TIME [OP DEPTH]]]]; subst transformation timestamp operation depth.
    apply memory_sequence_source_points_members; exists site,instruction,i,j; split; [exact NTH|].
    split; [reflexivity|tauto].
Qed.
Lemma memory_sequence_tiled_coverage instructions stride n m bi bj point :
  0 < bi -> 0 < bj -> m <= stride ->
  In point (memory_sequence_tiled_points instructions n m bi bj) <->
  memory_sequence_valid_point [n;m] (memory_sequence_tiled_instructions O instructions stride bi bj) point.
Proof.
  intros BI BJ STRIDE; split.
  - intro MEMBER; apply (@memory_sequence_tiled_domain_members instructions stride n m bi bj point BI BJ STRIDE)
      in MEMBER as [site [instruction [ti [tj [i [j [NTH [-> BOUNDS]]]]]]]].
    exists (append_memory_site_schedule 6 site (rectangle_tiled_instruction instruction stride bi bj)).
    split; [apply memory_sequence_tiled_instruction_nth; exact NTH|].
    split; [reflexivity|].
    split; [apply memory_sequence_tiled_point_belongs; tauto|].
    reflexivity.
  - intros [pi [NTH [PREFIX [BELONG LENGTH]]]].
    apply memory_sequence_tiled_instruction_lookup in NTH as [instruction [NTH ->]].
    destruct point as [site index transformation timestamp operation depth]; cbn in PREFIX,LENGTH,NTH,BELONG.
    destruct index as [|n' [|m' [|ti [|tj [|i [|j rest]]]]]]; cbn in PREFIX,LENGTH; try discriminate; try lia.
    inversion PREFIX; subst n' m'; clear PREFIX.
    assert (REST : rest = []) by (apply length_zero_iff_nil; cbn in LENGTH; lia); subst rest.
    unfold PL.belongs_to in BELONG.
    change (in_poly [n;m;ti;tj;i;j] (rectangle_tiled_domain stride bi bj) = true /\
      transformation = rectangle_tiled_projection /\
      timestamp = affine_product (rectangle_tiled_schedule ++ [(repeat 0 6,Z.of_nat site)]) [n;m;ti;tj;i;j] /\
      operation = instruction /\ depth = 4%nat) in BELONG.
    rewrite rectangle_tiled_domain_at,memory_sequence_tiled_schedule in BELONG.
    destruct BELONG as [DOMAIN [TRANS [TIME [OP DEPTH]]]]; subst transformation timestamp operation depth.
    apply (@memory_sequence_tiled_domain_members instructions stride n m bi bj
      (memory_sequence_tiled_point site instruction n m ti tj i j) BI BJ STRIDE).
    exists site,instruction,ti,tj,i,j; split; [exact NTH|]; split; [reflexivity|tauto].
Qed.
Print Assumptions memory_sequence_source_coverage.
Print Assumptions memory_sequence_tiled_coverage.
