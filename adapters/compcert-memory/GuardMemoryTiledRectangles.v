From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation.
From polcert.lib Require Import Linalg LinalgExt ListExt Misc ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness Base.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryRectangles GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles GuardMemoryTilingProgress
  GuardMemoryLoopTrace.
From Guard Require Import RectangularSchedule.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition rectangle_tiling_witness row_width column_width : statement_tiling_witness :=
  {| stw_point_dim := 2; stw_links :=
      [{| tl_expr := {| ae_var_coeffs := [1;0]; ae_param_coeffs := [0;0]; ae_const := 0 |};
          tl_tile_size := row_width |};
       {| tl_expr := {| ae_var_coeffs := [0;0;1]; ae_param_coeffs := [0;0]; ae_const := 0 |};
          tl_tile_size := column_width |}] |}.
Definition rectangle_tiled_projection := [([0;0;0;0;1;0],0);([0;0;0;0;0;1],0)].
Definition rectangle_tiled_schedule :=
  [([0;0;1;0;0;0],0);([0;0;0;1;0;0],0);([0;0;0;0;1;0],0);([0;0;0;0;0;1],0)].
Definition rectangle_tiled_domain stride row_width column_width :=
  [([0;0;row_width;0;-1;0],0);([0;0;-row_width;0;1;0],row_width-1);
   ([0;0;0;column_width;0;-1],0);([0;0;0;-column_width;0;1],column_width-1);
   ([0;0;0;0;-1;0],0);([-1;0;0;0;1;0],-1);
   ([0;0;0;0;0;-1],0);([0;-1;0;0;0;1],-1);([0;1;0;0;0;0],stride)].
Definition rectangle_tiled_instruction instruction stride row_width column_width : PL.PolyInstr :=
  {| PL.pi_depth := 4; PL.pi_instr := instruction;
     PL.pi_poly := rectangle_tiled_domain stride row_width column_width;
     PL.pi_schedule := rectangle_tiled_schedule;
     PL.pi_point_witness := PSWTiling (rectangle_tiling_witness row_width column_width);
     PL.pi_transformation := rectangle_projection; PL.pi_access_transformation := rectangle_projection;
     PL.pi_waccess := [instruction_write instruction]; PL.pi_raccess := instruction_reads instruction |}.
Definition rectangle_tiled_program instruction stride row_width column_width : PL.t :=
  ([rectangle_tiled_instruction instruction stride row_width column_width], [1%positive;2%positive],
   [(1%positive,tt);(2%positive,tt);(fst (instruction_write instruction),tt)]).
Definition rectangle_tiled_point instruction n m ti tj i j : PL.InstrPoint :=
  {| PL.ILSema.ip_nth := 0; PL.ILSema.ip_index := [n;m;ti;tj;i;j];
     PL.ILSema.ip_transformation := rectangle_tiled_projection;
     PL.ILSema.ip_time_stamp := [ti;tj;i;j]; PL.ILSema.ip_instruction := instruction;
     PL.ILSema.ip_depth := 4 |}.

Lemma tiled_projection_at n m ti tj i j :
  affine_product rectangle_tiled_projection [n;m;ti;tj;i;j] = [i;j].
Proof. unfold affine_product, rectangle_tiled_projection; cbn; repeat f_equal; ring. Qed.
Lemma tiled_schedule_at n m ti tj i j :
  affine_product rectangle_tiled_schedule [n;m;ti;tj;i;j] = [ti;tj;i;j].
Proof. unfold affine_product, rectangle_tiled_schedule; cbn; repeat f_equal; ring. Qed.
Lemma rectangle_tiled_current_transformation instruction stride row_width column_width n m ti tj i j :
  PL.current_transformation_of (rectangle_tiled_instruction instruction stride row_width column_width)
    [n;m;ti;tj;i;j] = rectangle_tiled_projection.
Proof. reflexivity. Qed.
Lemma rectangle_tiled_domain_at stride row_width column_width n m ti tj i j :
  in_poly [n;m;ti;tj;i;j] (rectangle_tiled_domain stride row_width column_width) = true <->
  0 <= i < n /\ 0 <= j < m /\ m <= stride /\
  row_width * ti <= i < row_width * (ti + 1) /\
  column_width * tj <= j < column_width * (tj + 1).
Proof.
  unfold in_poly,rectangle_tiled_domain,satisfies_constraint.
  cbn -[Z.add Z.mul Z.sub Z.opp Z.leb].
  repeat rewrite andb_true_iff; repeat rewrite Z.leb_le; nia.
Qed.

Lemma rectangle_tiled_point_exec instruction n m ti tj i j before after :
  PL.instr_point_sema (rectangle_tiled_point instruction n m ti tj i j) before after <->
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
    change (GuardMemoryInstr.instr_semantics instruction
      (affine_product rectangle_tiled_projection [n;m;ti;tj;i;j])
      (memory_write_cells instruction [i;j]) (memory_read_cells instruction [i;j]) before after).
    rewrite tiled_projection_at; exact RUN.
Qed.

Definition rectangle_tile_count bound width := (bound + width - 1) / width.
Lemma rectangle_tile_parent_in_range bound width x :
  0 < width -> 0 <= x < bound ->
  0 <= x / width < rectangle_tile_count bound width.
Proof.
  intros WIDTH X; unfold rectangle_tile_count.
  split; [apply Z.div_pos; lia|].
  pose proof (Z.div_mod x width ltac:(lia)) as DECOMPOSE.
  pose proof (Z.mod_pos_bound x width WIDTH) as REMAINDER.
  assert (STEP : x / width + 1 <= (bound + width - 1) / width).
  { apply Z.div_le_lower_bound; [lia|nia]. }
  lia.
Qed.

Print Assumptions rectangle_tiled_domain_at.
Print Assumptions rectangle_tiled_point_exec.

Definition rectangle_tiled_tail :=
  L.And (L.LE (L.Var 1) (L.Sum (L.Var 4) (L.Constant (-1))))
    (L.LE (L.Var 0) (L.Sum (L.Var 5) (L.Constant (-1)))).
Definition rectangle_tiled_body instruction :=
  L.Guard rectangle_tiled_tail (L.Instr instruction [L.Var 1;L.Var 0]).
Definition rectangle_tiled_j_loop instruction column_width :=
  L.Loop (L.Mult column_width (L.Var 1))
    (L.Sum (L.Mult column_width (L.Var 1)) (L.Constant column_width))
    (rectangle_tiled_body instruction).
Definition rectangle_tiled_i_loop instruction row_width column_width :=
  L.Loop (L.Mult row_width (L.Var 1))
    (L.Sum (L.Mult row_width (L.Var 1)) (L.Constant row_width))
    (rectangle_tiled_j_loop instruction column_width).
Definition rectangle_tiled_tj_loop instruction row_width column_width :=
  L.Loop (L.Constant 0)
    (L.Div (L.Sum (L.Var 2) (L.Constant (column_width-1))) column_width)
    (rectangle_tiled_i_loop instruction row_width column_width).
Definition rectangle_tiled_loop instruction row_width column_width :=
  L.Loop (L.Constant 0)
    (L.Div (L.Sum (L.Var 0) (L.Constant (row_width-1))) row_width)
    (rectangle_tiled_tj_loop instruction row_width column_width).
Definition rectangle_tiled_keep n m i j := (i <=? n-1) && (j <=? m-1).
Definition rectangle_tiled_j_points instruction n m ti tj i column_width :=
  map (rectangle_tiled_point instruction n m ti tj i)
    (filter (rectangle_tiled_keep n m i)
      (Zrange (column_width*tj) (column_width*(tj+1)))).
Definition rectangle_tiled_i_points instruction n m ti tj row_width column_width :=
  flat_map (fun i => rectangle_tiled_j_points instruction n m ti tj i column_width)
    (Zrange (row_width*ti) (row_width*(ti+1))).
Definition rectangle_tiled_tj_points instruction n m ti row_width column_width :=
  flat_map (fun tj => rectangle_tiled_i_points instruction n m ti tj row_width column_width)
    (Zrange 0 (rectangle_tile_count m column_width)).
Definition rectangle_tiled_points instruction n m row_width column_width :=
  flat_map (fun ti => rectangle_tiled_tj_points instruction n m ti row_width column_width)
    (Zrange 0 (rectangle_tile_count n row_width)).

Lemma rectangle_tiled_j_members instruction n m ti tj i width point :
  In point (rectangle_tiled_j_points instruction n m ti tj i width) <->
  exists j, point = rectangle_tiled_point instruction n m ti tj i j /\
    width*tj <= j < width*(tj+1) /\ i < n /\ j < m.
Proof.
  unfold rectangle_tiled_j_points; rewrite in_map_iff; split.
  - intros [j [EQ MEMBER]]; apply filter_In in MEMBER as [RANGE KEEP].
    apply Zrange_in in RANGE; unfold rectangle_tiled_keep in KEEP.
    apply andb_true_iff in KEEP as [I J]; rewrite Z.leb_le in I,J.
    exists j; split; [symmetry; exact EQ|lia].
  - intros [j [-> [RANGE [I J]]]]; exists j; split; [reflexivity|].
    apply filter_In; split; [apply Zrange_in; exact RANGE|].
    unfold rectangle_tiled_keep; apply andb_true_iff; split; apply Z.leb_le; lia.
Qed.
Lemma rectangle_tiled_i_members instruction n m ti tj bi bj point :
  In point (rectangle_tiled_i_points instruction n m ti tj bi bj) <->
  exists i j, point = rectangle_tiled_point instruction n m ti tj i j /\
    bi*ti <= i < bi*(ti+1) /\ bj*tj <= j < bj*(tj+1) /\ i < n /\ j < m.
Proof.
  unfold rectangle_tiled_i_points; rewrite in_flat_map; split.
  - intros [i [RANGE MEMBER]]; apply Zrange_in in RANGE.
    apply rectangle_tiled_j_members in MEMBER as [j [-> BOUNDS]]; exists i,j; auto.
  - intros [i [j [-> [I BOUNDS]]]]; exists i; split; [apply Zrange_in; exact I|].
    apply rectangle_tiled_j_members; exists j; auto.
Qed.
Lemma rectangle_tiled_tj_members instruction n m ti bi bj point :
  In point (rectangle_tiled_tj_points instruction n m ti bi bj) <->
  exists tj i j, point = rectangle_tiled_point instruction n m ti tj i j /\
    0 <= tj < rectangle_tile_count m bj /\
    bi*ti <= i < bi*(ti+1) /\ bj*tj <= j < bj*(tj+1) /\ i < n /\ j < m.
Proof.
  unfold rectangle_tiled_tj_points; rewrite in_flat_map; split.
  - intros [tj [RANGE MEMBER]]; apply Zrange_in in RANGE.
    apply rectangle_tiled_i_members in MEMBER as [i [j [-> BOUNDS]]]; exists tj,i,j; auto.
  - intros [tj [i [j [-> [TJ BOUNDS]]]]]; exists tj; split; [apply Zrange_in; exact TJ|].
    apply rectangle_tiled_i_members; exists i,j; auto.
Qed.
Lemma rectangle_tiled_members instruction n m bi bj point :
  In point (rectangle_tiled_points instruction n m bi bj) <->
  exists ti tj i j, point = rectangle_tiled_point instruction n m ti tj i j /\
    0 <= ti < rectangle_tile_count n bi /\ 0 <= tj < rectangle_tile_count m bj /\
    bi*ti <= i < bi*(ti+1) /\ bj*tj <= j < bj*(tj+1) /\ i < n /\ j < m.
Proof.
  unfold rectangle_tiled_points; rewrite in_flat_map; split.
  - intros [ti [RANGE MEMBER]]; apply Zrange_in in RANGE.
    apply rectangle_tiled_tj_members in MEMBER as [tj [i [j [-> BOUNDS]]]]; exists ti,tj,i,j; auto.
  - intros [ti [tj [i [j [-> [TI BOUNDS]]]]]]; exists ti; split; [apply Zrange_in; exact TI|].
    apply rectangle_tiled_tj_members; exists tj,i,j; auto.
Qed.

Lemma rectangle_tiled_domain_members instruction stride n m bi bj point :
  0 < bi -> 0 < bj -> m <= stride ->
  In point (rectangle_tiled_points instruction n m bi bj) <->
  exists ti tj i j, point = rectangle_tiled_point instruction n m ti tj i j /\
    0 <= i < n /\ 0 <= j < m /\ bi*ti <= i < bi*(ti+1) /\ bj*tj <= j < bj*(tj+1).
Proof.
  intros BI BJ STRIDE; rewrite rectangle_tiled_members; split.
  - intros [ti [tj [i [j [-> [TI [TJ [I [J [N M]]]]]]]]]];
      exists ti,tj,i,j; split; [reflexivity|nia].
  - intros [ti [tj [i [j [-> [I [J [TILEI TILEJ]]]]]]]]; exists ti,tj,i,j; split; [reflexivity|].
    assert (TI : ti = i / bi).
    { apply Z.div_unique with (r := i-bi*ti); [left; nia|ring]. }
    assert (TJ : tj = j / bj).
    { apply Z.div_unique with (r := j-bj*tj); [left; nia|ring]. }
    split; [rewrite TI; apply rectangle_tile_parent_in_range; assumption|].
    split; [rewrite TJ; apply rectangle_tile_parent_in_range; assumption|].
    tauto.
Qed.

Lemma memory_range_zseq count : forall lower upper,
  upper = lower + Z.of_nat count -> Zrange lower upper = zseq lower count.
Proof.
  induction count; intros lower upper LENGTH; cbn.
  - rewrite Zrange_empty by lia; reflexivity.
  - rewrite Zrange_begin by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    f_equal; apply IHcount; rewrite Nat2Z.inj_succ in LENGTH; lia.
Qed.
Lemma memory_strongly_sorted_range {A} (R : A -> A -> Prop) (f : Z -> A) lower upper :
  (forall x y, x < y -> R (f x) (f y)) -> StronglySorted R (map f (Zrange lower upper)).
Proof.
  intro ORDER; destruct (Z_lt_ge_dec lower upper) as [LT|EMPTY].
  - rewrite (@memory_range_zseq (Z.to_nat (upper-lower)) lower upper)
      by (rewrite Z2Nat.id by lia; lia).
    apply memory_strongly_sorted_zseq; exact ORDER.
  - rewrite Zrange_empty by lia; constructor.
Qed.
Lemma memory_strongly_sorted_filter {A} (R : A -> A -> Prop) keep points :
  StronglySorted R points -> StronglySorted R (filter keep points).
Proof.
  intro ORDER; induction ORDER; cbn; [constructor|].
  destruct (keep a); [constructor; [exact IHORDER|]|exact IHORDER].
  apply Forall_forall; intros point MEMBER; apply filter_In in MEMBER as [MEMBER _].
  eapply Forall_forall; eauto.
Qed.
Lemma memory_strongly_sorted_map_filter {A B} (R : B -> B -> Prop) (f : A -> B) keep xs :
  StronglySorted R (map f xs) -> StronglySorted R (map f (filter keep xs)).
Proof.
  induction xs as [|x xs IH]; cbn; intro ORDER; [constructor|].
  inversion ORDER; subst; destruct (keep x); cbn; [constructor|]; auto.
  apply Forall_forall; intros point MEMBER; apply in_map_iff in MEMBER as [y [<- MEMBER]].
  apply filter_In in MEMBER as [MEMBER _].
  eapply Forall_forall; [eassumption|apply in_map; exact MEMBER].
Qed.
Lemma memory_strongly_sorted_flat_range {A} (R : A -> A -> Prop) (f : Z -> list A) lower upper :
  (forall x, StronglySorted R (f x)) ->
  (forall x y a b, x < y -> In a (f x) -> In b (f y) -> R a b) ->
  StronglySorted R (flat_map f (Zrange lower upper)).
Proof.
  intros INNER CROSS; destruct (Z_lt_ge_dec lower upper) as [LT|EMPTY].
  - rewrite (@memory_range_zseq (Z.to_nat (upper-lower)) lower upper)
      by (rewrite Z2Nat.id by lia; lia).
    assert (ORDER : forall count start, StronglySorted R (flat_map f (zseq start count))).
    { induction count; intro start; cbn; [constructor|].
      apply memory_strongly_sorted_append; [apply INNER|apply IHcount|].
      intros a b MEMBER_A MEMBER_B; apply in_flat_map in MEMBER_B as [y [Y MEMBER_B]].
      apply CROSS with (x := start) (y := y); auto.
      pose proof (@zseq_bounds (start+1) count y Y); lia. }
    apply ORDER.
  - rewrite Zrange_empty by lia; constructor.
Qed.

Lemma memory_strongly_sorted_project {A} (R Q : A -> A -> Prop) xs :
  (forall x y, R x y -> Q x y) -> StronglySorted R xs -> StronglySorted Q xs.
Proof.
  intros IMPL SORTED; induction SORTED; constructor; auto.
  apply Forall_forall; intros x MEMBER; apply IMPL; eapply Forall_forall; eauto.
Qed.
Definition rectangle_tiled_order first second := PL.np_lt first second /\ PL.instr_point_sched_le first second.
Lemma rectangle_tiled_points_order instruction n m ti tj i j ti' tj' i' j' :
  ti < ti' \/ (ti=ti' /\ (tj<tj' \/ (tj=tj' /\ (i<i' \/ (i=i' /\ j<j'))))) ->
  rectangle_tiled_order (rectangle_tiled_point instruction n m ti tj i j)
    (rectangle_tiled_point instruction n m ti' tj' i' j').
Proof.
  intro ORDER.
  assert (LEX : lex_compare [ti;tj;i;j] [ti';tj';i';j'] = Lt).
  { unfold lex_compare; destruct ORDER as [TI|[TI [TJ|[TJ [I|[I J]]]]]].
    - rewrite (proj2 (Z.compare_lt_iff _ _) TI); reflexivity.
    - subst ti'; rewrite Z.compare_refl, (proj2 (Z.compare_lt_iff _ _) TJ); reflexivity.
    - subst ti' tj'; rewrite !Z.compare_refl, (proj2 (Z.compare_lt_iff _ _) I); reflexivity.
    - subst ti' tj' i'; rewrite !Z.compare_refl, (proj2 (Z.compare_lt_iff _ _) J); reflexivity. }
  split.
  - right; split; [reflexivity|].
    change (lex_compare [n;m;ti;tj;i;j] [n;m;ti';tj';i';j'] = Lt).
    cbn [lex_compare]; rewrite !Z.compare_refl; exact LEX.
  - left; exact LEX.
Qed.
Lemma rectangle_tiled_points_strongly_sorted instruction n m bi bj :
  StronglySorted rectangle_tiled_order (rectangle_tiled_points instruction n m bi bj).
Proof.
  unfold rectangle_tiled_points; apply memory_strongly_sorted_flat_range.
  - intro ti; unfold rectangle_tiled_tj_points; apply memory_strongly_sorted_flat_range.
    + intro tj; unfold rectangle_tiled_i_points; apply memory_strongly_sorted_flat_range.
      * intro i; unfold rectangle_tiled_j_points.
        apply memory_strongly_sorted_map_filter; apply memory_strongly_sorted_range.
        intros; apply rectangle_tiled_points_order; tauto.
      * intros i i' a b LT A B.
        apply rectangle_tiled_j_members in A as [j [-> _]].
        apply rectangle_tiled_j_members in B as [j' [-> _]].
        apply rectangle_tiled_points_order; tauto.
    + intros tj tj' a b LT A B.
      apply rectangle_tiled_i_members in A as [i [j [-> _]]].
      apply rectangle_tiled_i_members in B as [i' [j' [-> _]]].
      apply rectangle_tiled_points_order; tauto.
  - intros ti ti' a b LT A B.
    apply rectangle_tiled_tj_members in A as [tj [i [j [-> _]]]].
    apply rectangle_tiled_tj_members in B as [tj' [i' [j' [-> _]]]].
    apply rectangle_tiled_points_order; tauto.
Qed.

Lemma rectangle_tiled_points_sorted instruction n m bi bj :
  NoDup (rectangle_tiled_points instruction n m bi bj) /\
  Sorted PL.np_lt (rectangle_tiled_points instruction n m bi bj) /\
  Sorted PL.instr_point_sched_le (rectangle_tiled_points instruction n m bi bj).
Proof.
  pose proof (@rectangle_tiled_points_strongly_sorted instruction n m bi bj) as ORDER.
  assert (NP : StronglySorted PL.np_lt (rectangle_tiled_points instruction n m bi bj)).
  { eapply memory_strongly_sorted_project; [|exact ORDER]; intros x y [NP SCHED]; exact NP. }
  split.
  - apply memory_strongly_sorted_nodup with (R := PL.np_lt); [apply PL.np_lt_irrefl|exact NP].
  - split; apply StronglySorted_Sorted; [exact NP|].
    eapply memory_strongly_sorted_project; [|exact ORDER]; intros x y [NP' SCHED]; exact SCHED.
Qed.

Theorem rectangle_tiled_flatten instruction stride n m bi bj :
  0 < bi -> 0 < bj -> m <= stride ->
  PL.flatten_instrs [n;m] [rectangle_tiled_instruction instruction stride bi bj]
    (rectangle_tiled_points instruction n m bi bj).
Proof.
  intros BI BJ STRIDE; unfold PL.flatten_instrs; split.
  - intros ip MEMBER; apply rectangle_tiled_members in MEMBER as [ti [tj [i [j [-> _]]]]]; reflexivity.
  - split.
    + intro ip; split.
      * intro MEMBER; apply (@rectangle_tiled_domain_members instruction stride n m bi bj ip BI BJ STRIDE)
          in MEMBER as [ti [tj [i [j [-> BOUNDS]]]]].
        exists (rectangle_tiled_instruction instruction stride bi bj); split; [reflexivity|].
        split; [reflexivity|]; split; [|reflexivity].
        unfold PL.belongs_to; cbn -[in_poly affine_product PL.current_transformation_of].
        split; [apply rectangle_tiled_domain_at; tauto|].
        split; [reflexivity|]; split; [symmetry; apply tiled_schedule_at|]; split; reflexivity.
      * intros [pi [NTH [PREFIX [BELONG LENGTH]]]].
        assert (NTH_BOUND : (PL.ip_nth ip < 1)%nat).
        { assert (PRESENT : nth_error [rectangle_tiled_instruction instruction stride bi bj]
            (PL.ip_nth ip) <> None) by (rewrite NTH; discriminate).
          apply nth_error_Some in PRESENT; exact PRESENT. }
        assert (ZERO : PL.ip_nth ip = 0%nat) by lia.
        rewrite ZERO in NTH; cbn in NTH; inversion NTH; subst pi; clear NTH.
        destruct ip as [k index transformation timestamp operation depth]; cbn in ZERO,PREFIX,LENGTH; subst k.
        destruct index as [|n' [|m' [|ti [|tj [|i [|j rest]]]]]];
          cbn in PREFIX,LENGTH; try discriminate; try lia.
        inversion PREFIX; subst n' m'; clear PREFIX.
        assert (REST : rest = []) by (apply length_zero_iff_nil; cbn in LENGTH; lia); subst rest.
        unfold PL.belongs_to in BELONG; cbn -[in_poly affine_product PL.current_transformation_of] in BELONG.
        destruct BELONG as [DOMAIN [TRANSFORM [TIME [OPERATION DEPTH]]]].
        change (transformation = rectangle_tiled_projection) in TRANSFORM.
        rewrite tiled_schedule_at in TIME.
        subst transformation timestamp operation depth.
        apply (@rectangle_tiled_domain_members instruction stride n m bi bj
          (rectangle_tiled_point instruction n m ti tj i j) BI BJ STRIDE).
        exists ti,tj,i,j; split; [reflexivity|].
        apply rectangle_tiled_domain_at in DOMAIN; tauto.
    + pose proof (@rectangle_tiled_points_sorted instruction n m bi bj); tauto.
Qed.
