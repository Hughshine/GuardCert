From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightTempFrame ClightCountedLoop.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryRecursiveSource GuardMemoryMultiPointerCells GuardMemoryMultiPointerSyntax
  GuardMemoryMultiPointerProjectedCandidate GuardMemoryLinearPointerSyntax GuardMemoryNaryAffineAccess
  GuardMemoryLoopGuardFrame GuardMemoryFootprintCapabilities.
From GuardMemory Require Import GuardMemoryAffinePointerSyntax GuardMemoryAffinePointerPairs GuardMemoryAffinePointerScan.
Import ListNotations.
Set Implicit Arguments.

Definition memory_affine_pointer_guard_protected source (package : memory_affine_pointer_package source) live :=
  memory_nest_iterators (multi_pointer_region_nest (affine_pointer_region package)) ++
  memory_multi_pointer_runtime_context (affine_pointer_region package) ++
  multi_pointer_region_pointers (affine_pointer_region package) ++ live.
Lemma memory_affine_pointer_protected_pointer source (package : memory_affine_pointer_package source) live pointer :
  In pointer (multi_pointer_region_pointers (affine_pointer_region package)) ->
  In pointer (memory_affine_pointer_guard_protected package live).
Proof. intro MEMBER; unfold memory_affine_pointer_guard_protected; apply in_or_app; right;
  apply in_or_app; right; apply in_or_app; left; exact MEMBER. Qed.
Lemma memory_affine_pointer_protected_bound source (package : memory_affine_pointer_package source) live :
  In (affine_pointer_bound package) (memory_affine_pointer_guard_protected package live).
Proof.
  unfold memory_affine_pointer_guard_protected; apply in_or_app; right; apply in_or_app; left.
  unfold memory_multi_pointer_runtime_context; apply in_or_app; left; rewrite (affine_pointer_one_bound package); cbn; auto.
Qed.

Lemma memory_affine_pointer_capabilities_frame source (package : memory_affine_pointer_package source)
  original current memory count live :
  original ! (affine_pointer_bound package) = Some (Vint (Int.repr count)) -> signed_range count ->
  temp_agree (memory_affine_pointer_guard_protected package live) original current ->
  Forall (memory_cell_capable (memory_multi_pointer_locations original (multi_pointer_region_window (affine_pointer_region package))) memory)
    (memory_multi_pointer_runtime_footprint (affine_pointer_region package) original) ->
  Forall (memory_cell_capable (memory_multi_pointer_locations current (multi_pointer_region_window (affine_pointer_region package))) memory)
    (memory_multi_pointer_runtime_footprint (affine_pointer_region package) current).
Proof.
  intros BOUND RANGE FRAME CELLS.
  assert (CONTEXT : temp_agree (memory_multi_pointer_runtime_context (affine_pointer_region package)) original current).
  { eapply temp_agree_weaken; [|exact FRAME]; intros identifier MEMBER; unfold memory_affine_pointer_guard_protected;
    apply in_or_app; right; apply in_or_app; left; exact MEMBER. }
  rewrite (@memory_multi_pointer_runtime_footprint_temp_frame _ _ original current CONTEXT).
  apply Forall_forall; intros cell MEMBER.
  pose proof MEMBER as ACCESS; apply (proj1 (@memory_affine_pointer_footprint_member source package original count cell BOUND RANGE))
    in ACCESS as [access [index [ACCESS [INDEX ->]]]].
  apply Forall_forall with (x := memory_affine_pointer_access_cell access index) in CELLS; [|exact MEMBER].
  destruct CELLS as [location [RESOLVE REST]]; exists location; split; [|exact REST].
  unfold memory_affine_pointer_access_cell,memory_multi_pointer_locations in *; cbn [point_cell arr_id] in *.
  rewrite FRAME; [exact RESOLVE|].
  apply memory_affine_pointer_protected_pointer; pose proof (memory_affine_pointer_accesses_covered package) as COVER.
  apply Forall_forall with (x := access) in COVER; assumption.
Qed.

Lemma memory_affine_pointer_pairs_check_frame source (package : memory_affine_pointer_package source)
  original current count :
  temp_agree (multi_pointer_region_pointers (affine_pointer_region package)) original current ->
  memory_affine_pointer_pairs_check package
    (memory_multi_pointer_locations current (multi_pointer_region_window (affine_pointer_region package))) count =
  memory_affine_pointer_pairs_check package
    (memory_multi_pointer_locations original (multi_pointer_region_window (affine_pointer_region package))) count.
Proof.
  intro FRAME; unfold memory_affine_pointer_pairs_check.
  assert (VALID : memory_affine_pointer_pairs_valid package
    (memory_affine_access_pairs (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package))))).
  { apply Forall_forall; intros [first second] MEMBER; apply memory_affine_access_pair_member in MEMBER; exact MEMBER. }
  unfold memory_affine_pointer_pairs_valid in VALID.
  induction VALID as [|[first second] rest [FIRST [SECOND DISTINCT]] VALID IH]; cbn [forallb]; [reflexivity|].
  rewrite IH; f_equal; apply memory_affine_access_pair_check_frame.
  pose proof (memory_affine_pointer_accesses_covered package) as COVER.
  assert (FIRST_ID : In (memory_nary_access_array first) (multi_pointer_region_pointers (affine_pointer_region package)))
    by (apply Forall_forall with (x := first) in COVER; assumption).
  assert (SECOND_ID : In (memory_nary_access_array second) (multi_pointer_region_pointers (affine_pointer_region package)))
    by (apply Forall_forall with (x := second) in COVER; assumption).
  intros identifier MEMBER; apply FRAME; cbn in MEMBER; destruct MEMBER as [<-|[<-|[]]]; assumption.
Qed.
Print Assumptions memory_affine_pointer_capabilities_frame.
Print Assumptions memory_affine_pointer_pairs_check_frame.
