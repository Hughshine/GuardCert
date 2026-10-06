From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryNaryAffineAccess
  GuardMemoryNaryAffineExpressions GuardMemoryAffinePointerPairs GuardMemoryFiniteFootprint
  GuardMemoryFootprintRestriction GuardMemoryCrossPointerSeparation GuardMemoryMultiPointerCells
  GuardMemoryPointerAccessFootprint.
From GuardInterface Require Import AffineBoxEnvelope ClightAffineEnvelope ClightAffinePointerEnvelope ClightParametricEnvelope
  ClightSourceObservation ClightReadonlyLoadedTreeSynthesis ClightConditionComposition.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A sufficient condition over a covering box. The caller proves coverage
    by actual source accesses and supplies source observation receipts. *)
Fixpoint compile_pointer_envelope_pairs dimensions registers limits pairs : option decision_tree :=
  match pairs with
  | [] => Some (Decision true)
  | (first,second)::rest =>
    match compile_observed_affine_separation dimensions registers limits
      (memory_nary_access_array first) (memory_nary_access_array second)
      (memory_nary_access_index first) (memory_nary_access_index second),
      compile_pointer_envelope_pairs dimensions registers limits rest with
    | Some first,Some rest => Some (decision_bind first rest (Decision false))
    | _,_ => None end
  end.

Definition pointer_envelope_pair_separated temps counts parameters (pair : memory_nary_access * memory_nary_access) :=
  exists block base,
    temps ! (memory_nary_access_array (fst pair)) = Some (Vptr block base) /\
    temps ! (memory_nary_access_array (snd pair)) = Some (Vptr block base) /\
    forall left right,
      Forall2 (fun coordinate count => 0 <= coordinate < count) left counts ->
      Forall2 (fun coordinate count => 0 <= coordinate < count) right counts ->
      memory_nary_index_value (memory_nary_access_index (fst pair)) (left++parameters) <>
        memory_nary_index_value (memory_nary_access_index (snd pair)) (right++parameters).

Theorem compiled_pointer_envelope_pairs_sound dimensions registers limits pairs tree
  ge locals temps memory counts parameters :
  compile_pointer_envelope_pairs dimensions registers limits pairs = Some tree ->
  length counts = dimensions ->
  affine_registers_view registers (counts++parameters) temps ->
  Forall2 (fun value limit => 0 <= value < limit) (counts++parameters) limits ->
  (forall pair, In pair pairs -> observed_pointer_domain
    [memory_nary_access_array (fst pair);memory_nary_access_array (snd pair)] (Entry ge locals temps memory)) ->
  (exists answer, decision_run (Entry ge locals temps memory) tree answer) /\
  (decision_run (Entry ge locals temps memory) tree true ->
    Forall (pointer_envelope_pair_separated temps counts parameters) pairs).
Proof.
  revert tree; induction pairs as [|[first second] rest IH]; intros tree ENCODE DIMENSIONS WORDS RANGES OBSERVED.
  - injection ENCODE as <-; split; [exists true; constructor|intros; constructor].
  - cbn [compile_pointer_envelope_pairs] in ENCODE.
    destruct (compile_observed_affine_separation dimensions registers limits
      (memory_nary_access_array first) (memory_nary_access_array second)
      (memory_nary_access_index first) (memory_nary_access_index second)) as [head|] eqn:HEAD; [|discriminate].
    destruct (compile_pointer_envelope_pairs dimensions registers limits rest) as [tail|] eqn:TAIL; [|discriminate].
    injection ENCODE as <-.
    destruct (@compiled_observed_affine_separation_sound dimensions registers limits
      (memory_nary_access_array first) (memory_nary_access_array second)
      (memory_nary_access_index first) (memory_nary_access_index second) head
      ge locals temps memory counts parameters HEAD (OBSERVED (first,second) ltac:(left; reflexivity))
      DIMENSIONS WORDS RANGES) as [[choice RUN] SOUND].
    destruct (IH tail eq_refl DIMENSIONS WORDS RANGES
      ltac:(intros pair MEMBER; apply OBSERVED; right; exact MEMBER)) as [[last LAST] REST].
    split.
    + destruct choice; [exists last|exists false]; eapply decision_bind_run;
        [exact RUN|exact LAST|exact RUN|constructor].
    + intro ACCEPT; apply decision_bind_inv in ACCEPT as [[|] [FIRST SECOND]]; [|inversion SECOND].
      constructor; [|apply REST; exact SECOND].
      destruct (SOUND FIRST) as [block [base [P1 [P2 DIFFERENT]]]].
      exists block,base; split; [exact P1|split; [exact P2|]].
      intros left right LEFT RIGHT; rewrite <- !affine_value_source; apply DIFFERENT; assumption.
Qed.

Print Assumptions compiled_pointer_envelope_pairs_sound.

Theorem pointer_envelope_pairs_nonalias temps extent selected accesses counts parameters :
  4*extent <= Ptrofs.modulus ->
  (forall cell, In cell selected -> exists access coordinates,
    In access accesses /\
    Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts /\
    cell = memory_param_axis_pointer_access_cell access (coordinates++parameters)) ->
  Forall (pointer_envelope_pair_separated temps counts parameters)
    (memory_affine_access_pairs accesses) ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed selected)
    (memory_multi_pointer_locations temps extent)).
Proof.
  intros EXTENT COVERAGE PAIRS; apply memory_cross_pointer_separation_suffices; [exact EXTENT|].
  intros first second left right FIRST_MEMBER SECOND_MEMBER DISTINCT FIRST SECOND.
  apply memory_footprint_allowed_exact in FIRST_MEMBER,SECOND_MEMBER.
  apply COVERAGE in FIRST_MEMBER as [first_access [first_coordinates [FIRST_ACCESS [FIRST_RANGE ->]]]].
  apply COVERAGE in SECOND_MEMBER as [second_access [second_coordinates [SECOND_ACCESS [SECOND_RANGE ->]]]].
  apply Forall_forall with (x:=(first_access,second_access)) in PAIRS.
  2: { apply memory_affine_access_pair_member; repeat split; assumption. }
  destruct PAIRS as [block [base [P1 [P2 DIFFERENT]]]].
  destruct (@memory_multi_pointer_location_inverse temps extent _ left FIRST)
    as [b1 [o1 [i1 [PTR1 [IDX1 [RANGE1 LOC1]]]]]].
  destruct (@memory_multi_pointer_location_inverse temps extent _ right SECOND)
    as [b2 [o2 [i2 [PTR2 [IDX2 [RANGE2 LOC2]]]]]].
  cbn [memory_param_axis_pointer_access_cell point_cell arr_id arr_index] in PTR1,PTR2,IDX1,IDX2.
  injection IDX1 as <-; injection IDX2 as <-.
  eapply common_base_envelope_cell_separation;
    [exact EXTENT|exact P1|exact P2|exact RANGE1|exact RANGE2|
     apply DIFFERENT; assumption|exact FIRST|exact SECOND].
Qed.
Print Assumptions pointer_envelope_pairs_nonalias.
