From Stdlib Require Import List ZArith Lia Sorting.Sorted Sorting.Permutation Sorting.SetoidList.
From polcert.lib Require Import Linalg LinalgExt Misc ListExt.
From polcert.src Require Import SelectionSort Base.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryPolyhedralRectangles
  GuardMemoryTiledRectangles GuardMemoryTilingMultipleProgress GuardMemorySequencePolyhedral.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_sequence_sched_lt (first second : PL.InstrPoint) :=
  lex_compare (PL.ILSema.ip_time_stamp first) (PL.ILSema.ip_time_stamp second) = Lt.
Lemma memory_sequence_sched_irrefl point : ~ memory_sequence_sched_lt point point.
Proof. unfold memory_sequence_sched_lt; rewrite lex_compare_reflexive; discriminate. Qed.
Lemma memory_site_points_strongly_sorted {A} (R : A -> A -> Prop) emit instructions :
  (forall k l instruction other, (k < l)%nat -> R (emit k instruction) (emit l other)) ->
  forall base, StronglySorted R (memory_site_points base emit instructions).
Proof.
  intro ORDER; induction instructions; intro base; cbn; constructor; auto.
  apply Forall_forall; intros point MEMBER.
  apply memory_site_points_members in MEMBER as [position [instruction [NTH ->]]].
  apply ORDER; lia.
Qed.
Lemma memory_strongly_sorted_flat_map {A B} (R : B -> B -> Prop) (Q : A -> A -> Prop) f xs :
  StronglySorted Q xs -> (forall x, StronglySorted R (f x)) ->
  (forall x y first second, Q x y -> In first (f x) -> In second (f y) -> R first second) ->
  StronglySorted R (flat_map f xs).
Proof.
  intros ORDER INNER CROSS; induction ORDER; cbn; [constructor|].
  apply memory_strongly_sorted_append; [apply INNER|exact IHORDER|].
  intros first second FIRST SECOND; apply in_flat_map in SECOND as [y [Y SECOND]].
  eapply CROSS; [eapply Forall_forall; eauto|exact FIRST|exact SECOND].
Qed.
Lemma memory_strongly_sorted_flat_filter_range {A} (R : A -> A -> Prop) f keep lower upper :
  (forall x, StronglySorted R (f x)) ->
  (forall x y first second, x < y -> In first (f x) -> In second (f y) -> R first second) ->
  StronglySorted R (flat_map f (filter keep (Zrange lower upper))).
Proof.
  intros INNER CROSS; eapply memory_strongly_sorted_flat_map with (Q := Z.lt); [|exact INNER|exact CROSS].
  apply memory_strongly_sorted_filter.
  rewrite <- (map_id (Zrange lower upper)).
  apply memory_strongly_sorted_range; auto.
Qed.
Lemma memory_sequence_source_site_order site other instruction operation n m i j :
  (site < other)%nat -> memory_sequence_sched_lt
    (memory_sequence_source_point site instruction n m i j)
    (memory_sequence_source_point other operation n m i j).
Proof.
  intro ORDER; unfold memory_sequence_sched_lt; cbn [PL.ILSema.ip_time_stamp memory_sequence_source_point].
  cbn [lex_compare]; rewrite !Z.compare_refl.
  rewrite (proj2 (Z.compare_lt_iff (Z.of_nat site) (Z.of_nat other)) ltac:(lia)); reflexivity.
Qed.
Lemma memory_sequence_source_coordinate_order site other instruction operation n m i j i' j' :
  i < i' \/ (i=i' /\ j<j') -> memory_sequence_sched_lt
    (memory_sequence_source_point site instruction n m i j)
    (memory_sequence_source_point other operation n m i' j').
Proof.
  intro ORDER; unfold memory_sequence_sched_lt; cbn [PL.ILSema.ip_time_stamp memory_sequence_source_point].
  unfold lex_compare; destruct ORDER as [I|[-> J]];
    [rewrite (proj2 (Z.compare_lt_iff _ _) I)|rewrite Z.compare_refl,(proj2 (Z.compare_lt_iff _ _) J)]; reflexivity.
Qed.
Lemma memory_sequence_tiled_site_order site other instruction operation n m ti tj i j :
  (site < other)%nat -> memory_sequence_sched_lt
    (memory_sequence_tiled_point site instruction n m ti tj i j)
    (memory_sequence_tiled_point other operation n m ti tj i j).
Proof.
  intro ORDER; unfold memory_sequence_sched_lt; cbn [PL.ILSema.ip_time_stamp memory_sequence_tiled_point].
  cbn [lex_compare]; rewrite !Z.compare_refl.
  rewrite (proj2 (Z.compare_lt_iff (Z.of_nat site) (Z.of_nat other)) ltac:(lia)); reflexivity.
Qed.
Lemma memory_sequence_tiled_coordinate_order site other instruction operation n m ti tj i j ti' tj' i' j' :
  ti < ti' \/ (ti=ti' /\ (tj<tj' \/ (tj=tj' /\ (i<i' \/ (i=i' /\ j<j'))))) ->
  memory_sequence_sched_lt (memory_sequence_tiled_point site instruction n m ti tj i j)
    (memory_sequence_tiled_point other operation n m ti' tj' i' j').
Proof.
  intro ORDER; unfold memory_sequence_sched_lt; cbn [PL.ILSema.ip_time_stamp memory_sequence_tiled_point].
  unfold lex_compare; destruct ORDER as [TI|[TI [TJ|[TJ [I|[I J]]]]]].
  - rewrite (proj2 (Z.compare_lt_iff _ _) TI); reflexivity.
  - subst ti'; rewrite Z.compare_refl,(proj2 (Z.compare_lt_iff _ _) TJ); reflexivity.
  - subst ti' tj'; rewrite !Z.compare_refl,(proj2 (Z.compare_lt_iff _ _) I); reflexivity.
  - subst ti' tj' i'; rewrite !Z.compare_refl,(proj2 (Z.compare_lt_iff _ _) J); reflexivity.
Qed.
Lemma memory_sequence_source_points_strongly_sorted instructions n m :
  StronglySorted memory_sequence_sched_lt (memory_sequence_source_points instructions n m).
Proof.
  unfold memory_sequence_source_points; apply memory_strongly_sorted_flat_range.
  - intro i; apply memory_strongly_sorted_flat_range.
    + intro j; apply memory_site_points_strongly_sorted; intros; apply memory_sequence_source_site_order; assumption.
    + intros j j' first second ORDER FIRST SECOND.
      apply memory_site_points_members in FIRST as [site [instruction [NTH ->]]].
      apply memory_site_points_members in SECOND as [other [operation [NTH' ->]]].
      apply memory_sequence_source_coordinate_order; tauto.
  - intros i i' first second ORDER FIRST SECOND.
    apply in_flat_map in FIRST as [j [_ FIRST]].
    apply in_flat_map in SECOND as [j' [_ SECOND]].
    apply memory_site_points_members in FIRST as [site [instruction [NTH ->]]].
    apply memory_site_points_members in SECOND as [other [operation [NTH' ->]]].
    apply memory_sequence_source_coordinate_order; tauto.
Qed.
Lemma memory_sequence_tiled_points_strongly_sorted instructions n m bi bj :
  StronglySorted memory_sequence_sched_lt (memory_sequence_tiled_points instructions n m bi bj).
Proof.
  unfold memory_sequence_tiled_points; apply memory_strongly_sorted_flat_range.
  - intro ti; unfold memory_sequence_tiled_tj_points; apply memory_strongly_sorted_flat_range.
    + intro tj; unfold memory_sequence_tiled_i_points; apply memory_strongly_sorted_flat_range.
      * intro i; unfold memory_sequence_tiled_j_points; apply memory_strongly_sorted_flat_filter_range.
        -- intro j; apply memory_site_points_strongly_sorted; intros; apply memory_sequence_tiled_site_order; assumption.
        -- intros j j' first second ORDER FIRST SECOND.
           apply memory_site_points_members in FIRST as [site [instruction [NTH ->]]].
           apply memory_site_points_members in SECOND as [other [operation [NTH' ->]]].
           apply memory_sequence_tiled_coordinate_order; tauto.
      * intros i i' first second ORDER FIRST SECOND.
        apply memory_sequence_tiled_j_members in FIRST as [site [instruction [j [NTH [-> _]]]]].
        apply memory_sequence_tiled_j_members in SECOND as [other [operation [j' [NTH' [-> _]]]]].
        apply memory_sequence_tiled_coordinate_order; tauto.
    + intros tj tj' first second ORDER FIRST SECOND.
      apply memory_sequence_tiled_i_members in FIRST as [site [instruction [i [j [NTH [-> _]]]]]].
      apply memory_sequence_tiled_i_members in SECOND as [other [operation [i' [j' [NTH' [-> _]]]]]].
      apply memory_sequence_tiled_coordinate_order; tauto.
  - intros ti ti' first second ORDER FIRST SECOND.
    apply memory_sequence_tiled_tj_members in FIRST as [site [instruction [tj [i [j [NTH [-> _]]]]]]].
    apply memory_sequence_tiled_tj_members in SECOND as [other [operation [tj' [i' [j' [NTH' [-> _]]]]]]].
    apply memory_sequence_tiled_coordinate_order; tauto.
Qed.
Lemma memory_sequence_strict_order_properties points : StronglySorted memory_sequence_sched_lt points ->
  NoDup points /\ Sorted PL.instr_point_sched_le points /\
  (forall first second, In first points -> In second points ->
    PL.ILSema.instr_point_sched_eq first second -> first = second).
Proof.
  intro ORDER; split.
  - apply memory_strongly_sorted_nodup with (R := memory_sequence_sched_lt);
      [apply memory_sequence_sched_irrefl|exact ORDER].
  - split.
    + apply StronglySorted_Sorted; eapply memory_strongly_sorted_project; [|exact ORDER].
      intros first second LT; left; exact LT.
    + induction ORDER as [|point points ORDER IH NEXT]; intros first second FIRST SECOND EQUAL;
        [contradiction|].
      destruct FIRST as [<-|FIRST]; destruct SECOND as [<-|SECOND]; auto.
      * pose proof (proj1 (Forall_forall _ _) NEXT _ SECOND) as LT.
        unfold memory_sequence_sched_lt in LT.
        unfold PL.ILSema.instr_point_sched_eq,PL.ILSema.instr_point_sched_eqb in EQUAL.
        apply comparison_eqb_iff_eq in EQUAL; congruence.
      * pose proof (proj1 (Forall_forall _ _) NEXT _ FIRST) as LT.
        unfold memory_sequence_sched_lt in LT.
        unfold PL.ILSema.instr_point_sched_eq,PL.ILSema.instr_point_sched_eqb in EQUAL.
        apply comparison_eqb_iff_eq in EQUAL.
        rewrite lex_compare_antisym in EQUAL; rewrite LT in EQUAL; discriminate.
Qed.

Lemma memory_sequence_valid_conversion parameters instructions point :
  multiple_program_point parameters (map TV.outer_to_tiling_pinstr instructions) (TV.outer_to_tiling_ip point) <->
  memory_sequence_valid_point parameters instructions point.
Proof.
  unfold multiple_program_point,indexed_valid_point,memory_sequence_valid_point; split.
  - intros [instruction [NTH [PREFIX [BELONG [_ LENGTH]]]]].
    apply TV.nth_error_map_inv in NTH as [source [NTH ->]].
    apply TV.outer_to_tiling_belongs_to_iff in BELONG.
    exists source; cbn in PREFIX,LENGTH,NTH; auto.
  - intros [instruction [NTH [PREFIX [BELONG LENGTH]]]].
    exists (TV.outer_to_tiling_pinstr instruction); split.
    + rewrite List.nth_error_map; cbn; rewrite NTH; reflexivity.
    + split; [exact PREFIX|]; split; [apply TV.outer_to_tiling_belongs_to_iff; exact BELONG|].
      split; [reflexivity|exact LENGTH].
Qed.
Lemma memory_sequence_inner_point_inverse point :
  TV.outer_to_tiling_ip (TV.tiling_to_outer_ip point) = point.
Proof. destruct point; reflexivity. Qed.
Lemma memory_sequence_outer_point_inverse point :
  TV.tiling_to_outer_ip (TV.outer_to_tiling_ip point) = point.
Proof. destruct point; reflexivity. Qed.
Theorem memory_sequence_ordered_flatten parameters instructions points :
  (forall point, In point points <-> memory_sequence_valid_point parameters instructions point) ->
  NoDup points ->
  exists flattened, PL.flatten_instrs parameters instructions flattened /\ Permutation flattened points.
Proof.
  intros MEMBERS NODUP.
  set (raw := TV.outer_to_tiling_ipl points).
  set (ordered := SelectionSort T.instr_point_np_ltb T.instr_point_np_eqb raw).
  assert (PERM : Permutation raw ordered) by apply selection_sort_perm.
  assert (RAW_MEMBERS : forall point, In point raw <->
    multiple_program_point parameters (map TV.outer_to_tiling_pinstr instructions) point).
  { intro point; unfold raw,TV.outer_to_tiling_ipl; split.
    - intro MEMBER; apply in_map_iff in MEMBER as [original [<- MEMBER]].
      apply memory_sequence_valid_conversion; apply MEMBERS; exact MEMBER.
    - intro VALID; apply in_map_iff; exists (TV.tiling_to_outer_ip point); split.
      + apply memory_sequence_inner_point_inverse.
      + apply MEMBERS; apply memory_sequence_valid_conversion.
        rewrite memory_sequence_inner_point_inverse; exact VALID. }
  assert (ORDERED_MEMBERS : forall point, In point ordered <->
    multiple_program_point parameters (map TV.outer_to_tiling_pinstr instructions) point).
  { intro point; rewrite <- RAW_MEMBERS; split; eapply Permutation_in;
      [symmetry; exact PERM|exact PERM]. }
  assert (ORDERED_NODUP : NoDup ordered).
  { eapply Permutation_NoDup; [exact PERM|apply TV.NoDup_outer_to_tiling_ipl; exact NODUP]. }
  assert (ORDERED_NODUPA : NoDupA TP.np_eq ordered).
  { eapply multiple_program_nodupA; [|exact ORDERED_NODUP].
    intros point MEMBER; apply ORDERED_MEMBERS; exact MEMBER. }
  assert (FLAT : TP.flatten_instrs parameters (map TV.outer_to_tiling_pinstr instructions) ordered).
  { apply multiple_flatten_spec; split; [exact ORDERED_MEMBERS|]; split; [exact ORDERED_NODUP|].
    apply T.sortedb_instr_point_np_implies_sorted_np; [|exact ORDERED_NODUPA].
    apply selection_sort_sorted; apply T.instr_point_np_ltb_trans ||
      apply T.instr_point_np_eqb_trans || apply T.instr_point_np_eqb_refl ||
      apply T.instr_point_np_eqb_symm || apply T.instr_point_np_cmp_total ||
      apply T.instr_point_np_eqb_ltb_implies_ltb || apply T.instr_point_np_ltb_eqb_implies_ltb. }
  exists (TV.tiling_to_outer_ipl ordered); split.
  - apply TV.outer_to_tiling_flatten_instrs_iff.
    unfold TV.tiling_to_outer_ipl; rewrite TV.outer_to_tiling_ipl_tiling_to_outer; exact FLAT.
  - rewrite <- (TV.tiling_to_outer_ipl_outer_to_tiling points).
    apply Permutation_map; symmetry; exact PERM.
Qed.
Print Assumptions memory_sequence_ordered_flatten.
