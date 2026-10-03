From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation.
From polcert.lib Require Import Linalg LinalgExt ListExt ImpureAlarmConfig.
From polcert.src Require Import PointWitness Base.
From Vpl Require Import Impure.
From Guard Require Import RectangularSchedule RectangularIteration ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles
  GuardMemoryLoops GuardMemoryPolyhedral.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Module PL := GuardMemoryIRs.PolyLang.

Definition rectangle_projection := [([0;0;1;0],0);([0;0;0;1],0)].
Definition rectangle_row_schedule := rectangle_projection.
Definition rectangle_column_schedule := [([0;0;0;1],0);([0;0;1;0],0)].
Definition rectangle_domain stride :=
  [([0;0;-1;0],0);([-1;0;1;0],-1);
   ([0;0;0;-1],0);([0;-1;0;1],-1);([0;1;0;0],stride)].
Definition rectangle_poly_instruction instruction stride schedule : PL.PolyInstr :=
  {| PL.pi_depth := 2; PL.pi_instr := instruction;
     PL.pi_poly := rectangle_domain stride; PL.pi_schedule := schedule;
     PL.pi_point_witness := PSWIdentity 2;
     PL.pi_transformation := rectangle_projection;
     PL.pi_access_transformation := rectangle_projection;
     PL.pi_waccess := [instruction_write instruction];
     PL.pi_raccess := instruction_reads instruction |}.
Definition rectangle_poly_program instruction stride schedule : PL.t :=
  ([rectangle_poly_instruction instruction stride schedule], [1%positive;2%positive],
   [(1%positive,tt);(2%positive,tt);(fst (instruction_write instruction),tt)]).
Definition rectangle_poly_point instruction schedule n m i j : PL.InstrPoint :=
  {| PL.ILSema.ip_nth := 0; PL.ILSema.ip_index := [n;m;i;j];
     PL.ILSema.ip_transformation := rectangle_projection;
     PL.ILSema.ip_time_stamp := affine_product schedule [n;m;i;j];
     PL.ILSema.ip_instruction := instruction; PL.ILSema.ip_depth := 2 |}.
Definition rectangle_poly_points instruction schedule n m rows columns :=
  map (fun p => rectangle_poly_point instruction schedule n m (fst p) (snd p))
    (rectangle_rows rows columns).

Lemma projection_at n m i j : affine_product rectangle_projection [n;m;i;j] = [i;j].
Proof. unfold affine_product, rectangle_projection; cbn; repeat f_equal; ring. Qed.
Lemma row_schedule_at n m i j : affine_product rectangle_row_schedule [n;m;i;j] = [i;j].
Proof. apply projection_at. Qed.
Lemma column_schedule_at n m i j : affine_product rectangle_column_schedule [n;m;i;j] = [j;i].
Proof. unfold affine_product, rectangle_column_schedule; cbn; repeat f_equal; ring. Qed.
Lemma rectangle_domain_at stride n m i j :
  in_poly [n;m;i;j] (rectangle_domain stride) = true <->
  0 <= i < n /\ 0 <= j < m /\ m <= stride.
Proof.
  unfold in_poly, rectangle_domain, satisfies_constraint.
  cbn -[Z.add Z.mul Z.sub Z.opp Z.leb].
  repeat rewrite andb_true_iff; repeat rewrite Z.leb_le; lia.
Qed.

Lemma memory_zseq_member start count x :
  In x (zseq start count) <-> start <= x < start + Z.of_nat count.
Proof.
  split; [apply zseq_bounds|].
  revert start; induction count; intros start BOUND; cbn; [lia|].
  rewrite Nat2Z.inj_succ in BOUND.
  destruct (Z.eq_dec x start); [left; congruence|right; apply IHcount; lia].
Qed.
Lemma memory_rectangle_member rows columns i j :
  In (i,j) (rectangle_rows rows columns) <->
  0 <= i < Z.of_nat rows /\ 0 <= j < Z.of_nat columns.
Proof.
  split; [apply rectangle_member|].
  intros [I J]; apply in_flat_map; exists i; split.
  - apply memory_zseq_member; lia.
  - apply in_map_iff; exists j; split; [reflexivity|apply memory_zseq_member; lia].
Qed.

Lemma memory_strongly_sorted_append {A} (R : A -> A -> Prop) first second :
  StronglySorted R first -> StronglySorted R second ->
  (forall a b, In a first -> In b second -> R a b) ->
  StronglySorted R (first ++ second).
Proof.
  intros FIRST SECOND; induction FIRST; intro CROSS; cbn; [exact SECOND|].
  constructor.
  - apply IHFIRST; intros; apply CROSS; cbn; auto.
  - apply Forall_app; split; [exact H|].
    apply Forall_forall; intros; apply CROSS; cbn; auto.
Qed.
Lemma memory_strongly_sorted_zseq {A} (R : A -> A -> Prop) (f : Z -> A) :
  (forall x y, x < y -> R (f x) (f y)) ->
  forall count start, StronglySorted R (map f (zseq start count)).
Proof.
  intros MONOTONE count; induction count; intro start; cbn; constructor.
  - apply IHcount.
  - apply Forall_forall; intros value MEMBER.
    apply in_map_iff in MEMBER as [x [<- MEMBER]].
    apply MONOTONE; pose proof (@zseq_bounds _ _ _ MEMBER); lia.
Qed.
Lemma rectangle_points_np_order instruction schedule n m i j i' j' :
  i < i' \/ (i = i' /\ j < j') ->
  PL.np_lt (rectangle_poly_point instruction schedule n m i j)
    (rectangle_poly_point instruction schedule n m i' j').
Proof.
  intro ORDER; right; split; [reflexivity|].
  change (lex_compare [n;m;i;j] [n;m;i';j'] = Lt).
  unfold lex_compare; rewrite !Z.compare_refl.
  destruct ORDER as [LT|[SAME LT]].
  - rewrite (proj2 (Z.compare_lt_iff _ _) LT); reflexivity.
  - subst i'; rewrite Z.compare_refl; rewrite (proj2 (Z.compare_lt_iff _ _) LT); reflexivity.
Qed.
Lemma rectangle_points_strongly_sorted instruction schedule n m : forall rows start columns,
  StronglySorted PL.np_lt
    (flat_map (fun i => map (rectangle_poly_point instruction schedule n m i) (zseq 0 columns))
      (zseq start rows)).
Proof.
  induction rows; intros start columns; cbn; [constructor|].
  apply memory_strongly_sorted_append.
  - apply memory_strongly_sorted_zseq; intros; apply rectangle_points_np_order; right; auto.
  - apply IHrows.
  - intros a b A B.
    apply in_map_iff in A as [j [<- J]].
    apply in_flat_map in B as [i [I B]].
    apply in_map_iff in B as [j' [<- J']].
    apply rectangle_points_np_order; left; pose proof (@zseq_bounds _ _ _ I); lia.
Qed.
Lemma rectangle_points_expand instruction schedule n m rows columns :
  rectangle_poly_points instruction schedule n m rows columns =
  flat_map (fun i => map (rectangle_poly_point instruction schedule n m i) (zseq 0 columns)) (zseq 0 rows).
Proof.
  unfold rectangle_poly_points, rectangle_rows.
  induction (zseq 0 rows) as [|i rest IH]; cbn; [reflexivity|].
  rewrite map_app, IH, map_map; reflexivity.
Qed.
Lemma memory_strongly_sorted_nodup {A} (R : A -> A -> Prop) xs :
  (forall x, ~ R x x) -> StronglySorted R xs -> NoDup xs.
Proof.
  intros IRREFLEXIVE SORTED; induction SORTED; constructor; auto.
  intro MEMBER; apply Forall_forall with (x := a) in H; [apply (IRREFLEXIVE a H)|exact MEMBER].
Qed.
Lemma rectangle_poly_points_sorted instruction schedule n m rows columns :
  NoDup (rectangle_poly_points instruction schedule n m rows columns) /\
  Sorted PL.np_lt (rectangle_poly_points instruction schedule n m rows columns).
Proof.
  rewrite rectangle_points_expand.
  pose proof (@rectangle_points_strongly_sorted instruction schedule n m rows 0 columns) as SORTED.
  split; [apply memory_strongly_sorted_nodup with (R := PL.np_lt); [apply PL.np_lt_irrefl|exact SORTED]
    |apply StronglySorted_Sorted; exact SORTED].
Qed.

Print Assumptions rectangle_poly_points_sorted.

Lemma rectangle_poly_points_members instruction schedule n m rows columns ip :
  In ip (rectangle_poly_points instruction schedule n m rows columns) <->
  exists i j, ip = rectangle_poly_point instruction schedule n m i j /\
    0 <= i < Z.of_nat rows /\ 0 <= j < Z.of_nat columns.
Proof.
  unfold rectangle_poly_points; rewrite in_map_iff.
  split.
  - intros [[i j] [EQ MEMBER]]; exists i,j; cbn in EQ; split; [symmetry; exact EQ|].
    apply memory_rectangle_member; exact MEMBER.
  - intros [i [j [-> BOUND]]]; exists (i,j); split; [reflexivity|].
    apply memory_rectangle_member; exact BOUND.
Qed.

Lemma rectangle_poly_point_exec instruction schedule n m i j before after :
  PL.instr_point_sema (rectangle_poly_point instruction schedule n m i j) before after <->
  memory_point instruction i j before after.
Proof.
  split.
  - intro EXEC; inversion EXEC as [writes reads RUN].
    change (GuardMemoryInstr.instr_semantics instruction
      (affine_product rectangle_projection [n;m;i;j]) writes reads before after) in RUN.
    rewrite projection_at in RUN.
    destruct RUN as [WRITES [READS RUN]]; subst writes reads; repeat split; assumption || reflexivity.
  - intro EXEC; apply PL.ILSema.ip_sema_intro with
      (wcs := memory_write_cells instruction [i;j]) (rcs := memory_read_cells instruction [i;j]).
    change (GuardMemoryInstr.instr_semantics instruction
      (affine_product rectangle_projection [n;m;i;j])
      (memory_write_cells instruction [i;j]) (memory_read_cells instruction [i;j]) before after).
    rewrite projection_at; exact EXEC.
Qed.
Lemma memory_poly_list_append first second before middle after :
  PL.instr_point_list_semantics first before middle ->
  PL.instr_point_list_semantics second middle after ->
  PL.instr_point_list_semantics (first ++ second) before after.
Proof.
  intros FIRST SECOND; induction FIRST; cbn.
  - unfold GuardMemoryInstr.State.eq in H; subst; exact SECOND.
  - econstructor; eauto.
Qed.
Lemma memory_poly_row_exec instruction schedule n m i count : forall start before after,
  counted_iterations (memory_point instruction i) count start before after <->
  PL.instr_point_list_semantics
    (map (rectangle_poly_point instruction schedule n m i) (zseq start count)) before after.
Proof.
  induction count; intros start before after; cbn; split; intro EXEC.
  - inversion EXEC; subst; constructor; reflexivity.
  - inversion EXEC; subst; unfold GuardMemoryInstr.State.eq in *; subst; constructor.
  - inversion EXEC; subst; econstructor.
    + apply rectangle_poly_point_exec; eassumption.
    + apply IHcount; eassumption.
  - inversion EXEC as [|first middle last point tail HEAD TAIL]; subst.
    eapply iterations_next with (s1 := middle).
    + exact (proj1 (@rectangle_poly_point_exec instruction schedule n m i start before middle) HEAD).
    + apply IHcount; exact TAIL.
Qed.
Lemma memory_poly_rectangle_exec instruction schedule n m columns count : forall start before after,
  counted_iterations (fun i => counted_iterations (memory_point instruction i) columns 0)
    count start before after <->
  PL.instr_point_list_semantics
    (flat_map (fun i => map (rectangle_poly_point instruction schedule n m i) (zseq 0 columns))
      (zseq start count)) before after.
Proof.
  induction count; intros start before after; cbn; split; intro EXEC.
  - inversion EXEC; subst; constructor; reflexivity.
  - inversion EXEC; subst; unfold GuardMemoryInstr.State.eq in *; subst; constructor.
  - inversion EXEC; subst; eapply memory_poly_list_append.
    + apply memory_poly_row_exec; eassumption.
    + apply IHcount; eassumption.
  - destruct (PL.ILSema.instr_point_list_semantics_app_inv _ _ _ _ EXEC)
      as [middle [HEAD TAIL]].
    eapply iterations_next with (s1 := middle).
    + exact (proj2 (@memory_poly_row_exec instruction schedule n m start columns 0 before middle) HEAD).
    + exact (proj2 (IHcount (start + 1) middle after) TAIL).
Qed.

Theorem rectangle_poly_flatten instruction stride schedule rows columns :
  Z.of_nat columns <= stride ->
  PL.flatten_instrs [Z.of_nat rows;Z.of_nat columns]
    [rectangle_poly_instruction instruction stride schedule]
    (rectangle_poly_points instruction schedule (Z.of_nat rows) (Z.of_nat columns) rows columns).
Proof.
  intro STRIDE; unfold PL.flatten_instrs.
  split.
  - intros ip MEMBER; apply rectangle_poly_points_members in MEMBER as [i [j [-> BOUNDS]]]; reflexivity.
  - split.
    + intro ip; split.
      * intro MEMBER; apply rectangle_poly_points_members in MEMBER as [i [j [-> [I J]]]].
        exists (rectangle_poly_instruction instruction stride schedule); split; [reflexivity|].
        split; [reflexivity|]; split; [|reflexivity].
        unfold PL.belongs_to; cbn.
        split; [apply rectangle_domain_at; auto|]; repeat split; reflexivity.
      * intros [pi [NTH [PREFIX [BELONG LENGTH]]]].
        assert (NTH_BOUND : (PL.ip_nth ip < 1)%nat).
        { assert (PRESENT : nth_error [rectangle_poly_instruction instruction stride schedule]
            (PL.ip_nth ip) <> None) by (rewrite NTH; discriminate).
          apply nth_error_Some in PRESENT; exact PRESENT. }
        assert (NTH_ZERO : PL.ip_nth ip = 0%nat) by lia.
        rewrite NTH_ZERO in NTH; cbn in NTH; inversion NTH; subst pi; clear NTH.
        destruct ip as [k index transformation timestamp operation depth].
        cbn in NTH_ZERO, PREFIX, LENGTH; subst k.
        destruct index as [|n [|m [|i [|j rest]]]]; cbn in PREFIX, LENGTH; try discriminate; try lia.
        inversion PREFIX; subst n m; clear PREFIX.
        assert (REST : rest = []).
        { apply length_zero_iff_nil; cbn in LENGTH; lia. }
        subst rest; unfold PL.belongs_to in BELONG; cbn in BELONG.
        destruct BELONG as [DOMAIN [TRANSFORM [TIME [OPERATION DEPTH]]]].
        subst transformation timestamp operation depth.
        apply rectangle_poly_points_members; exists i,j; split; [reflexivity|].
        apply rectangle_domain_at in DOMAIN; tauto.
    + apply rectangle_poly_points_sorted.
Qed.

Lemma rectangle_row_points_sched_order instruction n m i j i' j' :
  i < i' \/ (i = i' /\ j < j') ->
  PL.instr_point_sched_le (rectangle_poly_point instruction rectangle_row_schedule n m i j)
    (rectangle_poly_point instruction rectangle_row_schedule n m i' j').
Proof.
  intro ORDER; left.
  change (lex_compare (affine_product rectangle_row_schedule [n;m;i;j])
    (affine_product rectangle_row_schedule [n;m;i';j']) = Lt).
  rewrite !row_schedule_at.
  unfold lex_compare; destruct ORDER as [LT|[SAME LT]].
  - rewrite (proj2 (Z.compare_lt_iff _ _) LT); reflexivity.
  - subst i'; rewrite Z.compare_refl; rewrite (proj2 (Z.compare_lt_iff _ _) LT); reflexivity.
Qed.
Lemma rectangle_row_points_sorted instruction n m rows columns :
  Sorted PL.instr_point_sched_le
    (rectangle_poly_points instruction rectangle_row_schedule n m rows columns).
Proof.
  rewrite rectangle_points_expand; apply StronglySorted_Sorted.
  assert (ORDER : forall count start,
    StronglySorted PL.instr_point_sched_le
      (flat_map (fun i => map (rectangle_poly_point instruction rectangle_row_schedule n m i)
        (zseq 0 columns)) (zseq start count))).
  { induction count; intro start; cbn; [constructor|].
    apply memory_strongly_sorted_append.
    - apply memory_strongly_sorted_zseq; intros; apply rectangle_row_points_sched_order; auto.
    - apply IHcount.
    - intros a b A B; apply in_map_iff in A as [j [<- J]].
      apply in_flat_map in B as [i [I B]]; apply in_map_iff in B as [j' [<- J']].
      apply rectangle_row_points_sched_order; left; pose proof (@zseq_bounds _ _ _ I); lia. }
  apply ORDER.
Qed.

(** This constructs a genuine PolyLang execution from the source execution,
    keeping the same concrete parameters and the same final memory. *)
Theorem memory_rectangle_loop_to_poly instruction stride rows columns before after :
  Z.of_nat columns <= stride ->
  L.loop_semantics (memory_rectangle_loop instruction) [Z.of_nat rows;Z.of_nat columns] before after ->
  PL.poly_instance_list_semantics [Z.of_nat rows;Z.of_nat columns]
    (rectangle_poly_program instruction stride rectangle_row_schedule) before after.
Proof.
  intros STRIDE EXEC; apply memory_rectangle_loop_iterations in EXEC.
  eapply PL.PolyPointListSema with
    (ipl := rectangle_poly_points instruction rectangle_row_schedule (Z.of_nat rows) (Z.of_nat columns) rows columns)
    (sorted_ipl := rectangle_poly_points instruction rectangle_row_schedule (Z.of_nat rows) (Z.of_nat columns) rows columns).
  - reflexivity.
  - apply rectangle_poly_flatten; exact STRIDE.
  - reflexivity.
  - apply rectangle_row_points_sorted.
  - rewrite rectangle_points_expand; apply memory_poly_rectangle_exec; exact EXEC.
Qed.
Print Assumptions rectangle_poly_flatten.
Print Assumptions memory_rectangle_loop_to_poly.

Lemma memory_sorted_permutation_unique original ordered :
  Sorted PL.instr_point_sched_le original -> NoDup original ->
  (forall first second, In first original -> In second original ->
    PL.ILSema.instr_point_sched_eq first second -> first = second) ->
  Permutation original ordered -> Sorted PL.instr_point_sched_le ordered ->
  original = ordered.
Proof.
  intros SORTED NODUP UNIQUE PERM ORDERED.
  assert (MEMBERS : forall ip, In ip original <-> In ip ordered).
  { intro ip; split; intro MEMBER; eapply Permutation_in; [exact PERM|exact MEMBER|symmetry; exact PERM|exact MEMBER]. }
  apply PL.ILSema.Sorted_incl_eq; auto.
  - apply NoDup_relation_unique_implies_NoDupA; auto.
  - apply NoDup_relation_unique_implies_NoDupA.
    + eapply Permutation_NoDup; eauto.
    + intros first second FIRST SECOND EQ.
      apply UNIQUE; auto; apply MEMBERS; assumption.
Qed.

Lemma memory_pair_timestamp_eq i j i' j' :
  lex_compare [i;j] [i';j'] = Eq -> i = i' /\ j = j'.
Proof.
  unfold lex_compare; destruct (Z.compare i i') eqn:FIRST; try discriminate.
  destruct (Z.compare j j') eqn:SECOND; try discriminate.
  intros _; split; apply Z.compare_eq_iff; assumption.
Qed.
Lemma rectangle_row_timestamp_unique instruction n m rows columns first second :
  In first (rectangle_poly_points instruction rectangle_row_schedule n m rows columns) ->
  In second (rectangle_poly_points instruction rectangle_row_schedule n m rows columns) ->
  PL.ILSema.instr_point_sched_eq first second -> first = second.
Proof.
  intros FIRST SECOND EQ.
  apply rectangle_poly_points_members in FIRST as [i [j [-> BOUNDS]]].
  apply rectangle_poly_points_members in SECOND as [i' [j' [-> BOUNDS']]].
  unfold PL.ILSema.instr_point_sched_eq, PL.ILSema.instr_point_sched_eqb in EQ.
  apply comparison_eqb_iff_eq in EQ.
  change (lex_compare (affine_product rectangle_row_schedule [n;m;i;j])
    (affine_product rectangle_row_schedule [n;m;i';j']) = Eq) in EQ.
  rewrite !row_schedule_at in EQ.
  apply memory_pair_timestamp_eq in EQ as [-> ->]; reflexivity.
Qed.

Theorem memory_rectangle_poly_to_loop instruction stride rows columns before after :
  Z.of_nat columns <= stride ->
  PL.poly_instance_list_semantics [Z.of_nat rows;Z.of_nat columns]
    (rectangle_poly_program instruction stride rectangle_row_schedule) before after ->
  L.loop_semantics (memory_rectangle_loop instruction) [Z.of_nat rows;Z.of_nat columns] before after.
Proof.
  intros STRIDE EXEC.
  inversion EXEC as [params program pis context vars initial final flattened ordered PROGRAM FLAT PERM SORTED RUN]; subst.
  unfold rectangle_poly_program in PROGRAM; inversion PROGRAM; subst pis context vars; clear PROGRAM.
  assert (CANONICAL : flattened = rectangle_poly_points instruction rectangle_row_schedule
    (Z.of_nat rows) (Z.of_nat columns) rows columns).
  { eapply PL.flatten_instrs_det; [exact FLAT|apply rectangle_poly_flatten; exact STRIDE]. }
  subst flattened.
  assert (ORDER : rectangle_poly_points instruction rectangle_row_schedule
    (Z.of_nat rows) (Z.of_nat columns) rows columns = ordered).
  { apply memory_sorted_permutation_unique.
    - apply rectangle_row_points_sorted.
    - exact (proj1 (@rectangle_poly_points_sorted instruction rectangle_row_schedule
        (Z.of_nat rows) (Z.of_nat columns) rows columns)).
    - intros; eapply rectangle_row_timestamp_unique; eauto.
    - exact PERM.
    - exact SORTED. }
  subst ordered; apply memory_rectangle_loop_iterations.
  rewrite rectangle_points_expand in RUN.
  exact (proj2 (@memory_poly_rectangle_exec instruction rectangle_row_schedule
    (Z.of_nat rows) (Z.of_nat columns) columns rows 0 before after) RUN).
Qed.
Print Assumptions memory_rectangle_poly_to_loop.

Definition rectangle_poly_column_points instruction n m rows columns :=
  map (fun p => rectangle_poly_point instruction rectangle_column_schedule n m (fst p) (snd p))
    (rectangle_columns rows columns).
Lemma rectangle_poly_column_permutation instruction n m rows columns :
  Permutation (rectangle_poly_points instruction rectangle_column_schedule n m rows columns)
    (rectangle_poly_column_points instruction n m rows columns).
Proof. apply Permutation_map; apply rectangle_permutation. Qed.
Lemma rectangle_column_points_expand instruction n m rows columns :
  rectangle_poly_column_points instruction n m rows columns =
  flat_map (fun j => map (fun i => rectangle_poly_point instruction rectangle_column_schedule n m i j)
    (zseq 0 rows)) (zseq 0 columns).
Proof.
  unfold rectangle_poly_column_points, rectangle_columns.
  induction (zseq 0 columns) as [|j rest IH]; cbn; [reflexivity|].
  rewrite map_app, IH, map_map; reflexivity.
Qed.
Lemma rectangle_column_points_sched_order instruction n m i j i' j' :
  j < j' \/ (j = j' /\ i < i') ->
  PL.instr_point_sched_le (rectangle_poly_point instruction rectangle_column_schedule n m i j)
    (rectangle_poly_point instruction rectangle_column_schedule n m i' j').
Proof.
  intro ORDER; left.
  change (lex_compare (affine_product rectangle_column_schedule [n;m;i;j])
    (affine_product rectangle_column_schedule [n;m;i';j']) = Lt).
  rewrite !column_schedule_at; unfold lex_compare.
  destruct ORDER as [LT|[SAME LT]].
  - rewrite (proj2 (Z.compare_lt_iff _ _) LT); reflexivity.
  - subst j'; rewrite Z.compare_refl; rewrite (proj2 (Z.compare_lt_iff _ _) LT); reflexivity.
Qed.
Lemma rectangle_column_points_sorted instruction n m rows columns :
  Sorted PL.instr_point_sched_le (rectangle_poly_column_points instruction n m rows columns).
Proof.
  rewrite rectangle_column_points_expand; apply StronglySorted_Sorted.
  assert (ORDER : forall count start, StronglySorted PL.instr_point_sched_le
    (flat_map (fun j => map (fun i => rectangle_poly_point instruction rectangle_column_schedule n m i j)
      (zseq 0 rows)) (zseq start count))).
  { induction count; intro start; cbn; [constructor|].
    apply memory_strongly_sorted_append.
    - apply memory_strongly_sorted_zseq; intros; apply rectangle_column_points_sched_order; auto.
    - apply IHcount.
    - intros a b A B; apply in_map_iff in A as [i [<- I]].
      apply in_flat_map in B as [j [J B]]; apply in_map_iff in B as [i' [<- I']].
      apply rectangle_column_points_sched_order; left; pose proof (@zseq_bounds _ _ _ J); lia. }
  apply ORDER.
Qed.
Lemma rectangle_column_timestamp_unique instruction n m rows columns first second :
  In first (rectangle_poly_column_points instruction n m rows columns) ->
  In second (rectangle_poly_column_points instruction n m rows columns) ->
  PL.ILSema.instr_point_sched_eq first second -> first = second.
Proof.
  intros FIRST SECOND EQ.
  assert (PERM := @rectangle_poly_column_permutation instruction n m rows columns).
  assert (FIRST' : In first (rectangle_poly_points instruction rectangle_column_schedule n m rows columns))
    by (eapply Permutation_in; [symmetry; exact PERM|exact FIRST]).
  assert (SECOND' : In second (rectangle_poly_points instruction rectangle_column_schedule n m rows columns))
    by (eapply Permutation_in; [symmetry; exact PERM|exact SECOND]).
  apply rectangle_poly_points_members in FIRST' as [i [j [-> BOUNDS]]].
  apply rectangle_poly_points_members in SECOND' as [i' [j' [-> BOUNDS']]].
  unfold PL.ILSema.instr_point_sched_eq, PL.ILSema.instr_point_sched_eqb in EQ.
  apply comparison_eqb_iff_eq in EQ.
  change (lex_compare (affine_product rectangle_column_schedule [n;m;i;j])
    (affine_product rectangle_column_schedule [n;m;i';j']) = Eq) in EQ.
  rewrite !column_schedule_at in EQ.
  apply memory_pair_timestamp_eq in EQ as [-> ->]; reflexivity.
Qed.

Lemma memory_poly_counted_exec (point : Z -> PL.InstrPoint) (logical : Z -> runtime_state -> runtime_state -> Prop) :
  (forall x before after, logical x before after <-> PL.instr_point_sema (point x) before after) ->
  forall count start before after, counted_iterations logical count start before after <->
    PL.instr_point_list_semantics (map point (zseq start count)) before after.
Proof.
  intros POINT count; induction count; intros start before after; cbn; split; intro EXEC.
  - inversion EXEC; subst; constructor; reflexivity.
  - inversion EXEC; subst; unfold GuardMemoryInstr.State.eq in *; subst; constructor.
  - inversion EXEC; subst; econstructor; [apply POINT; eassumption|apply IHcount; eassumption].
  - inversion EXEC as [|first middle last operation tail HEAD TAIL]; subst.
    eapply iterations_next with (s1 := middle).
    + exact (proj2 (POINT start before middle) HEAD).
    + exact (proj2 (IHcount (start + 1) middle after) TAIL).
Qed.
Lemma memory_poly_flat_counted_exec (points : Z -> list PL.InstrPoint) (logical : Z -> runtime_state -> runtime_state -> Prop) :
  (forall x before after, logical x before after <-> PL.instr_point_list_semantics (points x) before after) ->
  forall count start before after, counted_iterations logical count start before after <->
    PL.instr_point_list_semantics (flat_map points (zseq start count)) before after.
Proof.
  intros POINT count; induction count; intros start before after; cbn; split; intro EXEC.
  - inversion EXEC; subst; constructor; reflexivity.
  - inversion EXEC; subst; unfold GuardMemoryInstr.State.eq in *; subst; constructor.
  - inversion EXEC; subst; eapply memory_poly_list_append; [apply POINT; eassumption|apply IHcount; eassumption].
  - destruct (PL.ILSema.instr_point_list_semantics_app_inv _ _ _ _ EXEC)
      as [middle [HEAD TAIL]].
    eapply iterations_next with (s1 := middle).
    + exact (proj2 (POINT start before middle) HEAD).
    + exact (proj2 (IHcount (start + 1) middle after) TAIL).
Qed.

Theorem memory_rectangle_poly_to_columns instruction stride rows columns before after :
  Z.of_nat columns <= stride ->
  PL.poly_instance_list_semantics [Z.of_nat rows;Z.of_nat columns]
    (rectangle_poly_program instruction stride rectangle_column_schedule) before after ->
  rectangular_iterations (fun j i => memory_point instruction i j) columns rows before after.
Proof.
  intros STRIDE EXEC.
  inversion EXEC as [params program pis context vars initial final flattened ordered PROGRAM FLAT PERM SORTED RUN]; subst.
  unfold rectangle_poly_program in PROGRAM; inversion PROGRAM; subst pis context vars; clear PROGRAM.
  assert (CANONICAL : flattened = rectangle_poly_points instruction rectangle_column_schedule
    (Z.of_nat rows) (Z.of_nat columns) rows columns).
  { eapply PL.flatten_instrs_det; [exact FLAT|apply rectangle_poly_flatten; exact STRIDE]. }
  subst flattened.
  assert (PERM_COL := @rectangle_poly_column_permutation instruction (Z.of_nat rows) (Z.of_nat columns) rows columns).
  assert (ORDER : rectangle_poly_column_points instruction (Z.of_nat rows) (Z.of_nat columns) rows columns = ordered).
  { apply memory_sorted_permutation_unique.
    - apply rectangle_column_points_sorted.
    - eapply Permutation_NoDup; [exact PERM_COL|].
      exact (proj1 (@rectangle_poly_points_sorted instruction rectangle_column_schedule
        (Z.of_nat rows) (Z.of_nat columns) rows columns)).
    - intros; eapply rectangle_column_timestamp_unique; eauto.
    - eapply Permutation_trans; [symmetry; exact PERM_COL|exact PERM].
    - exact SORTED. }
  subst ordered; rewrite rectangle_column_points_expand in RUN.
  unfold rectangular_iterations; apply (proj2 (@memory_poly_flat_counted_exec
    (fun j => map (fun i => rectangle_poly_point instruction rectangle_column_schedule
      (Z.of_nat rows) (Z.of_nat columns) i j) (zseq 0 rows))
    (fun j => counted_iterations (fun i => memory_point instruction i j) rows 0)
    ltac:(intros j first last; apply memory_poly_counted_exec; intros;
      symmetry; apply rectangle_poly_point_exec) columns 0 before after)); exact RUN.
Qed.

Theorem validated_memory_rectangle_interchange instruction stride rows columns before after :
  Z.of_nat columns <= stride -> GuardMemoryInstr.NonAlias before ->
  mayReturn (validate_memory_equivalence
    (rectangle_poly_program instruction stride rectangle_row_schedule)
    (rectangle_poly_program instruction stride rectangle_column_schedule)) true ->
  L.loop_semantics (memory_rectangle_loop instruction) [Z.of_nat rows;Z.of_nat columns] before after ->
  rectangular_iterations (fun j i => memory_point instruction i j) columns rows before after.
Proof.
  intros STRIDE NONALIAS VALID EXEC; apply memory_rectangle_poly_to_columns with (stride := stride); [exact STRIDE|].
  apply (proj1 (@validated_memory_equivalence_at
    (rectangle_poly_program instruction stride rectangle_row_schedule)
    (rectangle_poly_program instruction stride rectangle_column_schedule)
    [Z.of_nat rows;Z.of_nat columns] before after eq_refl eq_refl NONALIAS VALID)).
  apply memory_rectangle_loop_to_poly; assumption.
Qed.
Print Assumptions memory_rectangle_poly_to_columns.
Print Assumptions validated_memory_rectangle_interchange.
