From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRuntimeReceipts GuardMemoryFiniteFootprint
  GuardMemoryFootprintRestriction GuardMemoryFiniteAliasCondition
  GuardMemoryBufferOffsets GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend
  GuardMemoryMultiTensorBackend GuardMemoryMultiTensorAddressReceipts GuardMemoryMultiTensorAffineFootprint
  GuardMemoryLoops GuardMemoryScalarLoops GuardMemoryBooleanRectangle GuardMemoryCanonicalDifference.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A deliberately checked subset: all templates share exactly the same affine
    coordinate map. Pointer roots are arbitrary, including slices of one block.
    This service is above the language-independent certificate kernel. *)
Definition canonical_alias_templates_check (accesses : list AccessFunction) :=
  match accesses with
  | [] => true
  | first::rest => forallb (fun access => listzzs_strict_eqb (snd first) (snd access)) rest
  end.

Theorem canonical_alias_templates_sound accesses :
  canonical_alias_templates_check accesses = true ->
  forall first second, In first accesses -> In second accesses -> snd first = snd second.
Proof.
  destruct accesses as [|head rest]; cbn [canonical_alias_templates_check];
    intros CHECK first second FIRST SECOND; [contradiction|].
  assert (SAME : forall access, In access (head::rest) -> snd head = snd access).
  { intros access [HEAD|MEMBER]; [subst; reflexivity|].
    apply listzzs_strict_eqb_eq; apply forallb_forall with (x:=access) in CHECK; assumption. }
  rewrite <- (SAME first FIRST), <- (SAME second SECOND); reflexivity.
Qed.

Fixpoint canonical_tensor_strides sizes : list Z :=
  match sizes with
  | [] => []
  | _::rest => tensor_volume rest :: canonical_tensor_strides rest
  end.

Lemma canonical_tensor_index_dot sizes coordinates index :
  tensor_index sizes coordinates = Some index ->
  index = dot_product (canonical_tensor_strides sizes) coordinates.
Proof.
  revert coordinates index; induction sizes as [|dimension rest IH];
    intros [|coordinate tail] index INDEX; cbn [tensor_index] in INDEX; try discriminate.
  - inversion INDEX; reflexivity.
  - destruct ((0 <=? coordinate) && (coordinate <? dimension)); [|discriminate].
    destruct (tensor_index rest tail) as [suffix|] eqn:SUFFIX; [|discriminate].
    inversion INDEX; subst index; cbn [canonical_tensor_strides dot_product].
    rewrite <- (IH _ _ SUFFIX); ring.
Qed.

Lemma canonical_tensor_index_difference sizes first second other_first other_second a b c d :
  tensor_index sizes first = Some a -> tensor_index sizes second = Some b ->
  tensor_index sizes other_first = Some c -> tensor_index sizes other_second = Some d ->
  canonical_coordinate_difference first second =
    canonical_coordinate_difference other_first other_second ->
  a-b = c-d.
Proof.
  intros A B C D DIFFERENCE.
  rewrite (@canonical_tensor_index_dot sizes first a A),(@canonical_tensor_index_dot sizes second b B),
    (@canonical_tensor_index_dot sizes other_first c C),(@canonical_tensor_index_dot sizes other_second d D).
  rewrite !canonical_dot_difference.
  - rewrite DIFFERENCE; reflexivity.
  - pose proof (@tensor_index_rank sizes other_first c C); pose proof (@tensor_index_rank sizes other_second d D); lia.
  - pose proof (@tensor_index_rank sizes first a A); pose proof (@tensor_index_rank sizes second b B); lia.
Qed.

Lemma canonical_modulo_pair_equal modulus a b c d :
  modulus <> 0 -> a-b = c-d ->
  (a mod modulus = b mod modulus <-> c mod modulus = d mod modulus).
Proof.
  intros NONZERO DIFFERENCE; split; intro SAME.
  - replace c with (d+(a-b)) by lia.
    rewrite Z.add_mod,Zminus_mod,SAME,Z.sub_diag,Z.mod_0_l,Z.add_0_r,Z.mod_mod by exact NONZERO;
      reflexivity.
  - replace a with (b+(c-d)) by lia.
    rewrite Z.add_mod,Zminus_mod,SAME,Z.sub_diag,Z.mod_0_l,Z.add_0_r,Z.mod_mod by exact NONZERO;
      reflexivity.
Qed.

Lemma canonical_pointer_offsets_equal first_base second_base a b c d :
  a-b = c-d ->
  Z.eqb (memory_pointer_buffer_offset first_base a) (memory_pointer_buffer_offset second_base b) =
    Z.eqb (memory_pointer_buffer_offset first_base c) (memory_pointer_buffer_offset second_base d).
Proof.
  intro DIFFERENCE; apply Bool.eq_true_iff_eq; rewrite !Z.eqb_eq.
  unfold memory_pointer_buffer_offset,memory_buffer_offset.
  apply canonical_modulo_pair_equal; [pose proof Ptrofs.modulus_pos; lia|lia].
Qed.

Lemma canonical_alias_resolved_check locations first second a b first_location second_location :
  fst first <> fst second ->
  locations (exact_cell first a) = Some first_location ->
  locations (exact_cell second b) = Some second_location ->
  multi_tensor_affine_access_check locations first second a b =
    negb (Pos.eqb (location_block first_location) (location_block second_location) &&
      Z.eqb (location_offset first_location) (location_offset second_location)).
Proof.
  intros DISTINCT FIRST SECOND; unfold multi_tensor_affine_access_check.
  assert (IDS : Pos.eqb (fst first) (fst second) = false) by (apply Pos.eqb_neq; exact DISTINCT).
  rewrite IDS; unfold memory_cell_pair_address_check.
  destruct memory_cell_identity_dec as [SAME|OTHER].
  - apply (f_equal arr_id) in SAME; destruct first,second; cbn in SAME,DISTINCT; contradiction.
  - rewrite FIRST,SECOND; reflexivity.
Qed.

Theorem canonical_alias_difference_exact sizes original first second a b c d :
  snd first = snd second ->
  length a = length b -> length c = length d ->
  canonical_coordinate_difference a b = canonical_coordinate_difference c d ->
  (exists location, multi_tensor_locations original sizes (exact_cell first a) = Some location) ->
  (exists location, multi_tensor_locations original sizes (exact_cell second b) = Some location) ->
  (exists location, multi_tensor_locations original sizes (exact_cell first c) = Some location) ->
  (exists location, multi_tensor_locations original sizes (exact_cell second d) = Some location) ->
  multi_tensor_affine_access_check (multi_tensor_locations original sizes) first second a b =
    multi_tensor_affine_access_check (multi_tensor_locations original sizes) first second c d.
Proof.
  intros MAP LENGTH OTHER_LENGTH DIFFERENCE [la A] [lb B] [lc C] [ld D].
  destruct (Pos.eq_dec (fst first) (fst second)) as [SAME|DISTINCT].
  - unfold multi_tensor_affine_access_check; rewrite SAME,Pos.eqb_refl; reflexivity.
  - destruct (@multi_tensor_location_inverse original sizes _ _ A)
      as [block_a [base_a [index_a [POINTER_A [INDEX_A LOCATION_A]]]]].
    destruct (@multi_tensor_location_inverse original sizes _ _ B)
      as [block_b [base_b [index_b [POINTER_B [INDEX_B LOCATION_B]]]]].
    destruct (@multi_tensor_location_inverse original sizes _ _ C)
      as [block_c [base_c [index_c [POINTER_C [INDEX_C LOCATION_C]]]]].
    destruct (@multi_tensor_location_inverse original sizes _ _ D)
      as [block_d [base_d [index_d [POINTER_D [INDEX_D LOCATION_D]]]]].
    destruct first as [first_id first_terms], second as [second_id second_terms]; cbn in MAP; subst second_terms.
    cbn [exact_cell arr_id arr_index] in POINTER_A,POINTER_B,POINTER_C,POINTER_D,INDEX_A,INDEX_B,INDEX_C,INDEX_D.
    rewrite POINTER_A in POINTER_C; inversion POINTER_C; subst block_c base_c.
    rewrite POINTER_B in POINTER_D; inversion POINTER_D; subst block_d base_d.
    assert (INDEX_DIFFERENCE : index_a-index_b = index_c-index_d).
    { eapply canonical_tensor_index_difference; [exact INDEX_A|exact INDEX_B|exact INDEX_C|exact INDEX_D|].
      apply canonical_affine_difference; assumption. }
    rewrite (@canonical_alias_resolved_check (multi_tensor_locations original sizes)
      (first_id,first_terms) (second_id,first_terms) a b la lb DISTINCT A B),
      (@canonical_alias_resolved_check (multi_tensor_locations original sizes)
      (first_id,first_terms) (second_id,first_terms) c d lc ld DISTINCT C D).
    subst la lb lc ld; cbn [location_block location_offset].
    rewrite (@canonical_pointer_offsets_equal base_a base_b index_a index_b index_c index_d INDEX_DIFFERENCE);
      reflexivity.
Qed.

Definition canonical_alias_check locations accesses values counts :=
  memory_boolean_rectangle_result
    (fun positions => multi_tensor_affine_point_check locations accesses values
      (canonical_difference_first counts positions) (canonical_difference_second counts positions))
    (canonical_difference_bounds counts) [].

(** Resolution is available from actual source permissions. This theorem
    compares Boolean specifications; it does not lower a Clight scanner. *)
Theorem canonical_alias_check_exact sizes original accesses values counts :
  Forall (fun count => 0 <= count) counts ->
  canonical_alias_templates_check accesses = true ->
  (forall point access,
    Forall2 (fun coordinate count => 0 <= coordinate < count) point counts ->
    In access accesses ->
    exists location, multi_tensor_locations original sizes (exact_cell access (point++values)) = Some location) ->
  canonical_alias_check (multi_tensor_locations original sizes) accesses values counts =
    multi_tensor_affine_scan_check (multi_tensor_locations original sizes) accesses values counts.
Proof.
  intros COUNTS TEMPLATES RESOLVE; apply Bool.eq_true_iff_eq.
  unfold canonical_alias_check.
  rewrite memory_boolean_rectangle_member
    by (apply Forall_map; apply Forall_forall; intros; apply canonical_difference_bound_nonnegative).
  cbn [app]; rewrite multi_tensor_affine_scan_check_member by exact COUNTS.
  split.
  - intros CHECK a b first second A B FIRST SECOND.
    destruct (canonical_difference_coverage A B) as [POSITIONS DIFFERENCE].
    set (positions := canonical_difference_positions counts a b).
    fold positions in POSITIONS,DIFFERENCE.
    destruct (canonical_difference_points COUNTS POSITIONS) as [C D].
    specialize (CHECK positions POSITIONS).
    unfold multi_tensor_affine_point_check in CHECK.
    apply forallb_forall with (x:=first) in CHECK; [|exact FIRST].
    apply forallb_forall with (x:=second) in CHECK; [|exact SECOND].
    rewrite <- CHECK.
    eapply canonical_alias_difference_exact.
    + eapply canonical_alias_templates_sound; eassumption.
    + rewrite !length_app; pose proof (Forall2_length A); pose proof (Forall2_length B); lia.
    + rewrite !length_app; pose proof (Forall2_length C); pose proof (Forall2_length D); lia.
    + rewrite !canonical_coordinate_difference_app
        by (pose proof (Forall2_length A); pose proof (Forall2_length B);
            pose proof (Forall2_length C); pose proof (Forall2_length D); lia).
      rewrite DIFFERENCE; reflexivity.
    + apply RESOLVE; assumption.
    + apply RESOLVE; assumption.
    + apply RESOLVE; assumption.
    + apply RESOLVE; assumption.
  - intros CHECK positions POSITIONS.
    destruct (canonical_difference_points COUNTS POSITIONS) as [C D].
    unfold multi_tensor_affine_point_check; apply forallb_forall; intros first FIRST;
      apply forallb_forall; intros second SECOND; apply CHECK; assumption.
Qed.

Theorem canonical_alias_source_receipts counts values instructions sizes original memory final :
  Forall (fun count => 0 <= count) counts ->
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) instructions)
    (counts++values) (RuntimeState (multi_tensor_locations original sizes) memory)
    (RuntimeState (multi_tensor_locations original sizes) final) ->
  forall positions access,
    Forall2 (fun position bound => 0 <= position < bound)
      positions (canonical_difference_bounds counts) ->
    In access (multi_tensor_instruction_templates instructions) ->
    memory_cell_access (multi_tensor_locations original sizes) memory
      (exact_cell access (canonical_difference_first counts positions++values)) Readable /\
    memory_cell_access (multi_tensor_locations original sizes) memory
      (exact_cell access (canonical_difference_second counts positions++values)) Readable.
Proof.
  intros COUNTS SOURCE positions access POSITIONS ACCESS.
  destruct (canonical_difference_points COUNTS POSITIONS) as [FIRST SECOND]; split;
    eapply multi_tensor_affine_source_point_receipts; eassumption.
Qed.

Theorem canonical_alias_source_exact counts values instructions sizes original memory final :
  Forall (fun count => 0 <= count) counts ->
  canonical_alias_templates_check (multi_tensor_instruction_templates instructions) = true ->
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) instructions)
    (counts++values) (RuntimeState (multi_tensor_locations original sizes) memory)
    (RuntimeState (multi_tensor_locations original sizes) final) ->
  canonical_alias_check (multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates instructions) values counts =
  multi_tensor_affine_scan_check (multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates instructions) values counts.
Proof.
  intros COUNTS TEMPLATES SOURCE; apply canonical_alias_check_exact; [exact COUNTS|exact TEMPLATES|].
  intros point access POINT ACCESS.
  destruct (@multi_tensor_affine_source_point_receipts counts values instructions
    (multi_tensor_locations original sizes) memory final SOURCE point access POINT ACCESS)
    as [location [RESOLVE PERMISSION]].
  exists location; exact RESOLVE.
Qed.

Theorem canonical_alias_source_nonalias dimensions sizes original memory final counts values instructions
    (ge : genv) (locals : env) :
  tensor_layout_flag sizes = true -> tensor_dimension_view dimensions sizes original ->
  Forall (fun count => 0 <= count) counts ->
  canonical_alias_templates_check (multi_tensor_instruction_templates instructions) = true ->
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) instructions)
    (counts++values) (RuntimeState (multi_tensor_locations original sizes) memory)
    (RuntimeState (multi_tensor_locations original sizes) final) ->
  canonical_alias_check (multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates instructions) values counts = true ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed
    (multi_tensor_affine_source_footprint counts values instructions)) (multi_tensor_locations original sizes)).
Proof.
  intros LAYOUT DIMENSIONS COUNTS TEMPLATES SOURCE CHECK.
  rewrite (@canonical_alias_source_exact counts values instructions sizes original memory final
    COUNTS TEMPLATES SOURCE) in CHECK.
  eapply multi_tensor_affine_scan_footprint_separation with (ge:=ge) (locals:=locals); eassumption.
Qed.

Print Assumptions canonical_alias_templates_sound.
Print Assumptions canonical_tensor_index_dot.
Print Assumptions canonical_tensor_index_difference.
Print Assumptions canonical_modulo_pair_equal.
Print Assumptions canonical_pointer_offsets_equal.
Print Assumptions canonical_alias_resolved_check.
Print Assumptions canonical_alias_difference_exact.
Print Assumptions canonical_alias_check_exact.
Print Assumptions canonical_alias_source_receipts.
Print Assumptions canonical_alias_source_exact.
Print Assumptions canonical_alias_source_nonalias.
