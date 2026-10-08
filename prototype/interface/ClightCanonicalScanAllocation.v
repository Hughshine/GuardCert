From Stdlib Require Import List Bool Arith Lia.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Clight.
From Guard Require Import ClightTempFootprint.
From GuardInterface Require Import ClightTensorRegionPackage ClightMultiTensorScanAllocation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope nat_scope.

(** Reuse the checked allocator at twice the source rank, partitioning its
    two vectors into four. Candidate scratch excludes the entire allocation. *)
Definition canonical_scan_allocation source live pool rank :=
  multi_tensor_scan_allocation source live pool (rank+rank).
Definition allocate_canonical_scan source live pool rank :=
  allocate_multi_tensor_scan source live pool (rank+rank).
Definition mcas_positions source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) := firstn rank (mtas_left allocation).
Definition mcas_limits source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) := skipn rank (mtas_left allocation).
Definition mcas_left source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) := firstn rank (mtas_right allocation).
Definition mcas_right source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) := skipn rank (mtas_right allocation).
Definition mcas_private source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) :=
  mcas_positions allocation++mcas_limits allocation++mcas_left allocation++mcas_right allocation++[mtas_flag allocation].

Lemma canonical_scan_partition_exact source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) :
  mcas_private allocation = multi_tensor_scan_private allocation.
Proof.
  unfold mcas_private,mcas_positions,mcas_limits,mcas_left,mcas_right,multi_tensor_scan_private.
  rewrite (app_assoc (firstn rank (mtas_left allocation)) (skipn rank (mtas_left allocation))
    (firstn rank (mtas_right allocation)++skipn rank (mtas_right allocation)++[mtas_flag allocation])).
  rewrite firstn_skipn.
  rewrite (app_assoc (firstn rank (mtas_right allocation)) (skipn rank (mtas_right allocation))
    [mtas_flag allocation]),firstn_skipn; reflexivity.
Qed.

Lemma canonical_scan_split_lengths (names : list ident) (rank : nat) :
  length names = rank+rank -> length (firstn rank names)=rank /\ length (skipn rank names)=rank.
Proof. intro LENGTH; rewrite length_firstn,length_skipn,LENGTH,Nat.min_l by lia; split; lia. Qed.

Theorem canonical_scan_lengths source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) :
  length (mcas_positions allocation)=rank /\ length (mcas_limits allocation)=rank /\
  length (mcas_left allocation)=rank /\ length (mcas_right allocation)=rank.
Proof.
  destruct (@canonical_scan_split_lengths (mtas_left allocation) rank (mtas_left_length allocation)) as [POS LIM].
  destruct (@canonical_scan_split_lengths (mtas_right allocation) rank (mtas_right_length allocation)) as [LEFT RIGHT].
  unfold mcas_positions,mcas_limits,mcas_left,mcas_right; auto.
Qed.

Theorem canonical_scan_private_unique source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) : NoDup (mcas_private allocation).
Proof. rewrite canonical_scan_partition_exact; exact (mtas_unique allocation). Qed.
Theorem canonical_scan_allocated_int32 source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) identifier :
  In identifier (mcas_private allocation) -> In (identifier,type_int32s) pool.
Proof. rewrite canonical_scan_partition_exact; apply multi_tensor_scan_allocated_int32. Qed.
Theorem canonical_scan_allocation_fresh source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) identifier :
  In identifier (statement_temps source++live) -> ~ In identifier (mcas_private allocation).
Proof. rewrite canonical_scan_partition_exact; apply multi_tensor_scan_allocation_fresh. Qed.
Theorem canonical_scan_candidate_pool_private source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) identifier ty :
  In (identifier,ty) (multi_tensor_scan_candidate_pool allocation) -> ~ In identifier (mcas_private allocation).
Proof. rewrite canonical_scan_partition_exact; apply multi_tensor_scan_candidate_pool_private. Qed.

Lemma canonical_unique_groups (first second : list ident) :
  NoDup (first++second) -> forall identifier, In identifier first -> ~ In identifier second.
Proof.
  induction first as [|head first IH]; cbn; intros UNIQUE identifier MEMBER; [contradiction|].
  inversion UNIQUE as [|h tail FRESH REST]; subst.
  destruct MEMBER as [<-|MEMBER].
  - intro BAD; apply FRESH; apply in_or_app; right; exact BAD.
  - eapply IH; eassumption.
Qed.

Theorem canonical_scan_groups source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) :
  NoDup (mcas_positions allocation) /\ NoDup (mcas_limits allocation) /\
  NoDup (mcas_left allocation++mcas_right allocation) /\
  (forall id, In id (mcas_positions allocation) -> ~ In id (mcas_limits allocation++[mtas_flag allocation])) /\
  (forall id, In id (mcas_limits allocation) -> id <> mtas_flag allocation) /\
  (forall id, In id (mcas_left allocation++mcas_right allocation) ->
    ~ In id (mcas_positions allocation++mcas_limits allocation++[mtas_flag allocation])) /\
  ~ In (mtas_flag allocation)
    (mcas_positions allocation++mcas_limits allocation++mcas_left allocation++mcas_right allocation).
Proof.
  pose proof (canonical_scan_private_unique allocation) as UNIQUE.
  unfold mcas_private in UNIQUE.
  assert (TAIL : NoDup (mcas_limits allocation++mcas_left allocation++mcas_right allocation++[mtas_flag allocation]))
    by (eapply NoDup_app_remove_l; exact UNIQUE).
  assert (COORDS : NoDup ((mcas_left allocation++mcas_right allocation)++[mtas_flag allocation])).
  { rewrite <-app_assoc; eapply NoDup_app_remove_l; exact TAIL. }
  pose proof (@canonical_unique_groups (mcas_positions allocation) _ UNIQUE) as POS_FRESH.
  pose proof (@canonical_unique_groups (mcas_limits allocation) _ TAIL) as LIM_FRESH.
  pose proof (@canonical_unique_groups (mcas_left allocation++mcas_right allocation) _ COORDS) as COORD_FRESH.
  repeat split.
  - eapply NoDup_app_remove_r; exact UNIQUE.
  - eapply NoDup_app_remove_r; exact TAIL.
  - eapply NoDup_app_remove_r; exact COORDS.
  - intros id MEMBER BAD; apply (POS_FRESH id MEMBER);
      repeat rewrite in_app_iff in *; tauto.
  - intros id MEMBER SAME; subst id; apply (LIM_FRESH _ MEMBER);
      repeat rewrite in_app_iff; cbn; tauto.
  - intros id MEMBER BAD; repeat rewrite in_app_iff in BAD; destruct BAD as [BAD|[BAD|BAD]].
    + apply (POS_FRESH id BAD); repeat rewrite in_app_iff in *; tauto.
    + apply (LIM_FRESH id BAD); repeat rewrite in_app_iff in *; tauto.
    + apply (COORD_FRESH id MEMBER); exact BAD.
  - intro BAD; repeat rewrite in_app_iff in BAD; destruct BAD as [BAD|[BAD|[BAD|BAD]]].
    + apply (POS_FRESH _ BAD); repeat rewrite in_app_iff; cbn; tauto.
    + apply (LIM_FRESH _ BAD); repeat rewrite in_app_iff; cbn; tauto.
    + apply (COORD_FRESH _ ltac:(apply in_or_app; left; exact BAD)); cbn; auto.
    + apply (COORD_FRESH _ ltac:(apply in_or_app; right; exact BAD)); cbn; auto.
Qed.

(** Ineligible static templates use the old scanner on the coordinate vectors;
    all four vectors remain reserved from candidate code. *)
Lemma canonical_scan_coordinate_private source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) id :
  In id (mcas_left allocation++mcas_right allocation++[mtas_flag allocation]) -> In id (mcas_private allocation).
Proof. unfold mcas_private; intro MEMBER; apply in_or_app; right; apply in_or_app; right; exact MEMBER. Qed.

Definition canonical_scan_fallback_allocation source live pool rank
    (allocation : canonical_scan_allocation source live pool rank) :
    multi_tensor_scan_allocation source live pool rank.
Proof.
  refine {|mtas_left:=mcas_left allocation;mtas_right:=mcas_right allocation;
    mtas_flag:=mtas_flag allocation|}.
  - exact (proj1 (proj2 (proj2 (canonical_scan_lengths allocation)))).
  - exact (proj2 (proj2 (proj2 (canonical_scan_lengths allocation)))).
  - apply (@NoDup_app_remove_l _ (mcas_positions allocation++mcas_limits allocation)
      (mcas_left allocation++mcas_right allocation++[mtas_flag allocation])).
    rewrite <-app_assoc; exact (canonical_scan_private_unique allocation).
  - unfold tensor_disjoint; apply forallb_forall; intros id PUBLIC; apply negb_true_iff.
    destruct (tensor_member id (mcas_left allocation++mcas_right allocation++[mtas_flag allocation])) eqn:MEMBER;
      [|reflexivity].
    exfalso; apply tensor_member_true in MEMBER;
      eapply canonical_scan_allocation_fresh; [exact PUBLIC|apply canonical_scan_coordinate_private; exact MEMBER].
  - unfold tensor_subset; apply forallb_forall; intros id MEMBER; apply tensor_member_true.
    eapply tensor_subset_sound; [exact (mtas_typed allocation)|].
    change (In id (multi_tensor_scan_private allocation)).
    rewrite <-canonical_scan_partition_exact; apply canonical_scan_coordinate_private; exact MEMBER.
Defined.

Print Assumptions canonical_scan_partition_exact.
Print Assumptions canonical_scan_lengths.
Print Assumptions canonical_scan_private_unique.
Print Assumptions canonical_scan_allocated_int32.
Print Assumptions canonical_scan_allocation_fresh.
Print Assumptions canonical_scan_candidate_pool_private.
Print Assumptions canonical_scan_groups.
Print Assumptions canonical_scan_fallback_allocation.
