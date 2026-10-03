From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate GuardMemoryLinearPointerSyntax
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryBooleanScan GuardMemoryFiniteFootprint
  GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities GuardMemoryFootprintRestriction GuardMemoryCrossPointerSeparation.
From GuardMemory Require Import GuardMemoryAffinePointerSyntax GuardMemoryAffinePairScan GuardMemoryAffinePairChoice.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_access_pairs accesses :=
  flat_map (fun first => map (fun second => (first,second))
    (filter (fun second => negb (Pos.eqb (memory_nary_access_array first) (memory_nary_access_array second))) accesses)) accesses.
Lemma memory_affine_access_pair_member accesses first second :
  In (first,second) (memory_affine_access_pairs accesses) <->
  In first accesses /\ In second accesses /\ memory_nary_access_array first <> memory_nary_access_array second.
Proof.
  unfold memory_affine_access_pairs; rewrite in_flat_map; split.
  - intros [left [LEFT RIGHT]]; apply in_map_iff in RIGHT as [right [SAME FILTER]].
    inversion SAME; subst left right; apply filter_In in FILTER as [MEMBER DIFFERENT].
    apply negb_true_iff in DIFFERENT; apply Pos.eqb_neq in DIFFERENT; auto.
  - intros [FIRST [SECOND DIFFERENT]]; exists first; split; [exact FIRST|].
    apply in_map_iff; exists second; split; [reflexivity|].
    apply filter_In; split; [exact SECOND|apply negb_true_iff,Pos.eqb_neq; exact DIFFERENT].
Qed.
Definition memory_affine_access_pair_check locations count pair :=
  memory_affine_pair_choice_check locations count
    (memory_nary_access_array (fst pair)) (memory_nary_access_array (snd pair))
    (memory_nary_access_index (fst pair)) (memory_nary_access_index (snd pair)).
Definition memory_affine_pointer_pairs_check source (package : memory_affine_pointer_package source) locations count :=
  forallb (memory_affine_access_pair_check locations count)
    (memory_affine_access_pairs (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package)))).

Theorem memory_affine_pointer_access_capability source (package : memory_affine_pointer_package source) temps memory count :
  temps ! (affine_pointer_bound package) = Some (Vint (Int.repr count)) -> signed_range count ->
  Forall (memory_cell_capable (memory_multi_pointer_locations temps
    (multi_pointer_region_window (affine_pointer_region package))) memory)
    (memory_multi_pointer_runtime_footprint (affine_pointer_region package) temps) ->
  forall access index,
    In access (memory_linear_pointer_accesses (multi_pointer_region_code (affine_pointer_region package))) ->
    0 <= index < count ->
    memory_cell_capable (memory_multi_pointer_locations temps (multi_pointer_region_window (affine_pointer_region package))) memory
      (memory_affine_pointer_access_cell access index).
Proof.
  intros BOUND RANGE CELLS access index MEMBER INDEX.
  apply Forall_forall with (x := memory_affine_pointer_access_cell access index) in CELLS; [exact CELLS|].
  apply (proj2 (@memory_affine_pointer_footprint_member source package temps count _ BOUND RANGE)).
  exists access,index; auto.
Qed.

Theorem memory_affine_pointer_pairs_separation source (package : memory_affine_pointer_package source)
  (ge : genv) (locals : env) temps memory count :
  0 <= count -> signed_range count ->
  temps ! (affine_pointer_bound package) = Some (Vint (Int.repr count)) ->
  Forall (memory_cell_capable (memory_multi_pointer_locations temps
    (multi_pointer_region_window (affine_pointer_region package))) memory)
    (memory_multi_pointer_runtime_footprint (affine_pointer_region package) temps) ->
  memory_affine_pointer_pairs_check package
    (memory_multi_pointer_locations temps (multi_pointer_region_window (affine_pointer_region package))) count = true ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_multi_pointer_runtime_footprint (affine_pointer_region package) temps))
    (memory_multi_pointer_locations temps (multi_pointer_region_window (affine_pointer_region package)))).
Proof.
  intros POS RANGE BOUND CELLS CHECK.
  apply memory_cross_pointer_separation_suffices.
  - exact (proj2 (proj2 (multi_pointer_region_extent (multi_pointer_region_syntax (affine_pointer_region package))))).
  - intros first second left right FIRST_MEMBER SECOND_MEMBER DISTINCT FIRST SECOND.
    apply memory_footprint_allowed_exact in FIRST_MEMBER,SECOND_MEMBER.
    pose proof FIRST_MEMBER as FIRST_FOOTPRINT; pose proof SECOND_MEMBER as SECOND_FOOTPRINT.
    apply (proj1 (@memory_affine_pointer_footprint_member source package temps count first BOUND RANGE))
      in FIRST_MEMBER as [first_access [i [FIRST_ACCESS [I ->]]]].
    apply (proj1 (@memory_affine_pointer_footprint_member source package temps count second BOUND RANGE))
      in SECOND_MEMBER as [second_access [j [SECOND_ACCESS [J ->]]]].
    unfold memory_affine_pointer_pairs_check in CHECK.
    apply forallb_forall with (x := (first_access,second_access)) in CHECK.
    2: { apply memory_affine_access_pair_member; repeat split; assumption. }
    unfold memory_affine_access_pair_check in CHECK; cbn [fst snd] in CHECK.
    assert (FULL : memory_affine_range_pair_check
      (memory_multi_pointer_locations temps (multi_pointer_region_window (affine_pointer_region package))) count
      (memory_nary_access_array first_access) (memory_nary_access_array second_access)
      (memory_nary_access_index first_access) (memory_nary_access_index second_access) = true).
    { eapply memory_affine_pair_choice_complete; [exact DISTINCT|exact POS| |exact CHECK].
      intros index INDEX; split; eapply memory_affine_pointer_access_capability; eassumption. }
    clear CHECK; rename FULL into CHECK; unfold memory_affine_range_pair_check in CHECK.
    rewrite memory_boolean_scan_member in CHECK; rewrite Z2Nat.id in CHECK by exact POS.
    specialize (CHECK i ltac:(lia)); rewrite memory_boolean_scan_member in CHECK;
      rewrite Z2Nat.id in CHECK by exact POS; specialize (CHECK j ltac:(lia)).
    assert (FIRST_CAP : memory_cell_address_binding memory_multi_pointer_cell_code
      (memory_multi_pointer_locations temps (multi_pointer_region_window (affine_pointer_region package)))
      (Entry ge locals temps memory) (memory_affine_pointer_access_cell first_access i)).
    { apply memory_multi_pointer_cell_encoding;
      [exact (proj1 (proj2 (multi_pointer_region_extent (multi_pointer_region_syntax (affine_pointer_region package)))))|].
      apply Forall_forall with (x := memory_affine_pointer_access_cell first_access i) in CELLS; assumption. }
    assert (SECOND_CAP : memory_cell_address_binding memory_multi_pointer_cell_code
      (memory_multi_pointer_locations temps (multi_pointer_region_window (affine_pointer_region package)))
      (Entry ge locals temps memory) (memory_affine_pointer_access_cell second_access j)).
    { apply memory_multi_pointer_cell_encoding;
      [exact (proj1 (proj2 (multi_pointer_region_extent (multi_pointer_region_syntax (affine_pointer_region package)))))|].
      apply Forall_forall with (x := memory_affine_pointer_access_cell second_access j) in CELLS; assumption. }
    eapply memory_cell_pair_address_separated; [exact FIRST_CAP|exact SECOND_CAP|exact FIRST|exact SECOND| |exact CHECK].
    left; exact DISTINCT.
Qed.

Lemma memory_affine_access_pair_check_frame original current extent count first second :
  temp_agree [memory_nary_access_array first;memory_nary_access_array second] original current ->
  memory_affine_access_pair_check (memory_multi_pointer_locations current extent) count (first,second) =
  memory_affine_access_pair_check (memory_multi_pointer_locations original extent) count (first,second).
Proof.
  intro FRAME; unfold memory_affine_access_pair_check; cbn [fst snd].
  apply memory_affine_pair_choice_frame; exact FRAME.
Qed.

Print Assumptions memory_affine_pointer_access_capability.
Print Assumptions memory_affine_pointer_pairs_separation.
Print Assumptions memory_affine_access_pair_check_frame.
