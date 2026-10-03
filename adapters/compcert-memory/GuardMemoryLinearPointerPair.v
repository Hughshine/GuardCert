From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Coqlib Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryMultiPointerCells
  GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerProjectedCandidate GuardMemoryLinearPointerSyntax
  GuardMemoryPointerRangeScan GuardMemoryBooleanScan GuardMemoryFiniteFootprint GuardMemoryFiniteAliasCondition
  GuardMemoryFootprintCapabilities GuardMemoryFootprintRestriction GuardMemoryCrossPointerSeparation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record memory_linear_pointer_pair_package source := MemoryLinearPointerPairPackage {
  linear_pointer_pair_region : memory_linear_pointer_package source;
  linear_pointer_pair_first : ident;
  linear_pointer_pair_second : ident;
  linear_pointer_pair_distinct : linear_pointer_pair_first <> linear_pointer_pair_second;
  linear_pointer_pair_identifiers : nodup peq (memory_linear_pointer_identifiers
    (multi_pointer_region_code (linear_pointer_region linear_pointer_pair_region))) =
    [linear_pointer_pair_first;linear_pointer_pair_second]
}.

Definition check_memory_linear_pointer_pair source (package : memory_linear_pointer_package source)
  : option (memory_linear_pointer_pair_package source).
Proof.
  destruct (nodup peq (memory_linear_pointer_identifiers (multi_pointer_region_code (linear_pointer_region package))))
    as [|first [|second [|third rest]]] eqn:IDS; [exact None|exact None| |exact None].
  destruct (peq first second) as [SAME|DISTINCT]; [exact None|].
  exact (Some (@MemoryLinearPointerPairPackage source package first second DISTINCT IDS)).
Defined.
Definition describe_memory_linear_pointer_pair source :=
  match describe_memory_linear_pointer_region source with
  | Some package => check_memory_linear_pointer_pair package | None => None end.

Lemma memory_linear_pointer_pair_identifier_member source (package : memory_linear_pointer_pair_package source) identifier :
  In identifier (memory_linear_pointer_identifiers
    (multi_pointer_region_code (linear_pointer_region (linear_pointer_pair_region package)))) <->
  identifier = linear_pointer_pair_first package \/ identifier = linear_pointer_pair_second package.
Proof.
  rewrite <- (nodup_In peq),(linear_pointer_pair_identifiers package); cbn; intuition congruence.
Qed.

Theorem memory_linear_pointer_pair_capabilities source (package : memory_linear_pointer_pair_package source)
  temps memory count :
  temps ! (linear_pointer_bound (linear_pointer_pair_region package)) = Some (Vint (Int.repr count)) ->
  signed_range count ->
  Forall (memory_cell_capable (memory_multi_pointer_locations temps
    (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package)))) memory)
    (memory_multi_pointer_runtime_footprint (linear_pointer_region (linear_pointer_pair_region package)) temps) ->
  forall index, 0 <= index < count ->
    memory_cell_capable (memory_multi_pointer_locations temps
      (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package)))) memory
      (point_cell (linear_pointer_pair_first package) index) /\
    memory_cell_capable (memory_multi_pointer_locations temps
      (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package)))) memory
      (point_cell (linear_pointer_pair_second package) index).
Proof.
  intros BOUND RANGE CELLS index INDEX.
  assert (ALL : forall identifier, identifier = linear_pointer_pair_first package \/ identifier = linear_pointer_pair_second package ->
    memory_cell_capable (memory_multi_pointer_locations temps
      (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package)))) memory
      (point_cell identifier index)).
  { intros identifier MEMBER; apply Forall_forall with (x := point_cell identifier index) in CELLS; [exact CELLS|].
    apply (proj2 (@memory_linear_pointer_footprint_member source (linear_pointer_pair_region package) temps count _ BOUND RANGE)).
    exists identifier,index; split; [apply memory_linear_pointer_pair_identifier_member; exact MEMBER|auto]. }
  split; apply ALL; auto.

Qed.

Theorem memory_linear_pointer_pair_separation source (package : memory_linear_pointer_pair_package source)
  (ge : genv) (locals : env) temps memory count :
  0 <= count -> signed_range count ->
  temps ! (linear_pointer_bound (linear_pointer_pair_region package)) = Some (Vint (Int.repr count)) ->
  Forall (memory_cell_capable (memory_multi_pointer_locations temps
    (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package)))) memory)
    (memory_multi_pointer_runtime_footprint (linear_pointer_region (linear_pointer_pair_region package)) temps) ->
  memory_pointer_range_pair_check (memory_multi_pointer_locations temps
    (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package)))) count
    (linear_pointer_pair_first package) (linear_pointer_pair_second package) = true ->
  locations_nonalias (memory_restrict_locations
    (memory_footprint_allowed (memory_multi_pointer_runtime_footprint
      (linear_pointer_region (linear_pointer_pair_region package)) temps))
    (memory_multi_pointer_locations temps
      (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package))))).
Proof.
  intros POS RANGE BOUND CELLS CHECK.
  apply memory_cross_pointer_separation_suffices.
  - exact (proj2 (proj2 (multi_pointer_region_extent
      (multi_pointer_region_syntax (linear_pointer_region (linear_pointer_pair_region package)))))).
  - intros first second left right FIRST_MEMBER SECOND_MEMBER DISTINCT FIRST SECOND.
    apply memory_footprint_allowed_exact in FIRST_MEMBER,SECOND_MEMBER.
    pose proof FIRST_MEMBER as FIRST_FOOTPRINT; pose proof SECOND_MEMBER as SECOND_FOOTPRINT.
    apply (proj1 (@memory_linear_pointer_footprint_member source (linear_pointer_pair_region package) temps count first BOUND RANGE))
      in FIRST_MEMBER as [first_id [i [FIRST_ID [I ->]]]].
    apply (proj1 (@memory_linear_pointer_footprint_member source (linear_pointer_pair_region package) temps count second BOUND RANGE))
      in SECOND_MEMBER as [second_id [j [SECOND_ID [J ->]]]].
    apply memory_linear_pointer_pair_identifier_member in FIRST_ID,SECOND_ID.
    unfold memory_pointer_range_pair_check in CHECK; rewrite memory_boolean_scan_member in CHECK.
    rewrite Z2Nat.id in CHECK by exact POS.
    assert (PAIR : forall i j, 0 <= i < count -> 0 <= j < count ->
      memory_cell_pair_address_check (memory_multi_pointer_locations temps
        (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package))))
        (point_cell (linear_pointer_pair_first package) i) (point_cell (linear_pointer_pair_second package) j) = true).
    { intros a b A B; specialize (CHECK a ltac:(lia)); rewrite memory_boolean_scan_member in CHECK;
      rewrite Z2Nat.id in CHECK by exact POS; apply CHECK; lia. }
    assert (FIRST_CAP : memory_cell_address_binding memory_multi_pointer_cell_code
      (memory_multi_pointer_locations temps (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package))))
      (Entry ge locals temps memory) (point_cell first_id i)).
    { apply memory_multi_pointer_cell_encoding;
      [exact (proj1 (proj2 (multi_pointer_region_extent (multi_pointer_region_syntax (linear_pointer_region (linear_pointer_pair_region package))))))|].
      apply Forall_forall with (x := point_cell first_id i) in CELLS; assumption. }
    assert (SECOND_CAP : memory_cell_address_binding memory_multi_pointer_cell_code
      (memory_multi_pointer_locations temps (multi_pointer_region_window (linear_pointer_region (linear_pointer_pair_region package))))
      (Entry ge locals temps memory) (point_cell second_id j)).
    { apply memory_multi_pointer_cell_encoding;
      [exact (proj1 (proj2 (multi_pointer_region_extent (multi_pointer_region_syntax (linear_pointer_region (linear_pointer_pair_region package))))))|].
      apply Forall_forall with (x := point_cell second_id j) in CELLS; assumption. }
    cbn [arr_id point_cell] in DISTINCT.
    destruct FIRST_ID as [FIRST_ID | FIRST_ID]; destruct SECOND_ID as [SECOND_ID | SECOND_ID];
      subst first_id second_id; try contradiction.
    + eapply memory_cell_pair_address_separated; [exact FIRST_CAP|exact SECOND_CAP|exact FIRST|exact SECOND| |apply PAIR; assumption].
      left; cbn [arr_id point_cell]; exact (linear_pointer_pair_distinct package).
    + apply location_disjoint_symmetric.
      eapply memory_cell_pair_address_separated; [exact SECOND_CAP|exact FIRST_CAP|exact SECOND|exact FIRST| |apply PAIR; assumption].
      left; cbn [arr_id point_cell]; exact (linear_pointer_pair_distinct package).
Qed.

Print Assumptions memory_linear_pointer_pair_capabilities.
Print Assumptions memory_linear_pointer_pair_separation.
