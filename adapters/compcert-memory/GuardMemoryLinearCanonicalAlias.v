(** Canonical differences need equal loop coefficients, not equal offsets.
    Scalar parameters remain fixed during the check and may have different
    coefficients in different access templates. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRuntimeReceipts GuardMemoryFiniteFootprint
  GuardMemoryFootprintRestriction GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend
  GuardMemoryMultiTensorBackend GuardMemoryMultiTensorAffineFootprint GuardMemoryLoops GuardMemoryScalarLoops
  GuardMemoryBooleanRectangle GuardMemoryCanonicalDifference GuardMemoryCanonicalAlias.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition canonical_loop_linear_map rank (terms : AffineFunction) : AffineFunction :=
  map (fun term => (firstn rank (fst term),0)) terms.
Definition linear_alias_templates_check rank (accesses : list AccessFunction) :=
  canonical_alias_templates_check
    (map (fun access => (fst access,canonical_loop_linear_map rank (snd access))) accesses).

Theorem linear_alias_templates_sound rank accesses :
  linear_alias_templates_check rank accesses=true -> forall first second,
  In first accesses -> In second accesses ->
  canonical_loop_linear_map rank (snd first)=canonical_loop_linear_map rank (snd second).
Proof.
  intros CHECK first second FIRST SECOND.
  exact (@canonical_alias_templates_sound _ CHECK
    (fst first,canonical_loop_linear_map rank (snd first))
    (fst second,canonical_loop_linear_map rank (snd second))
    (in_map _ _ _ FIRST) (in_map _ _ _ SECOND)).
Qed.

Theorem linear_alias_templates_include_strict rank accesses :
  canonical_alias_templates_check accesses=true -> linear_alias_templates_check rank accesses=true.
Proof.
  intro CHECK; destruct accesses as [|first rest]; [reflexivity|].
  unfold linear_alias_templates_check; cbn [map canonical_alias_templates_check].
  apply forallb_forall; intros normalized MEMBER.
  apply in_map_iff in MEMBER as [second [SAME SECOND]]; subst normalized.
  apply listzzs_strict_eq_eqb; cbn [snd].
  rewrite (@canonical_alias_templates_sound (first::rest) CHECK first second
    ltac:(cbn; auto) ltac:(cbn; auto)); reflexivity.
Qed.

Lemma linear_dot_append coefficients point values :
  dot_product coefficients (point++values)=
    dot_product (firstn (length point) coefficients) point+
    dot_product (skipn (length point) coefficients) values.
Proof.
  revert coefficients; induction point as [|coordinate tail IH].
  - intro coefficients; cbn [app length firstn skipn].
    rewrite dot_product_nil_left; ring.
  - intros [|coefficient rest].
    + rewrite !dot_product_nil_left; reflexivity.
    + cbn [app length firstn skipn dot_product].
      rewrite IH; ring.
Qed.

Theorem linear_affine_difference rank first_terms second_terms a b c d values :
  canonical_loop_linear_map rank first_terms=canonical_loop_linear_map rank second_terms ->
  length a=rank -> length b=rank -> length c=rank -> length d=rank ->
  canonical_coordinate_difference a b=canonical_coordinate_difference c d ->
  canonical_coordinate_difference (affine_product first_terms (a++values))
    (affine_product second_terms (b++values))=
  canonical_coordinate_difference (affine_product first_terms (c++values))
    (affine_product second_terms (d++values)).
Proof.
  intros MAP A B C D DIFFERENCE; revert second_terms MAP.
  induction first_terms as [|[first_coeff first_constant] first_rest IH];
    intros [|[second_coeff second_constant] second_rest] MAP;
    cbn [canonical_loop_linear_map map fst snd] in MAP; try discriminate;
    cbn [affine_product map canonical_coordinate_difference fst snd]; [reflexivity|].
  assert (HEAD : firstn rank first_coeff=firstn rank second_coeff) by congruence.
  assert (TAIL : canonical_loop_linear_map rank first_rest=canonical_loop_linear_map rank second_rest)
    by exact (f_equal (@tl (list Z * Z)) MAP).
  f_equal; [|apply IH; exact TAIL].
  rewrite !linear_dot_append,A,B,C,D,<-HEAD.
  assert (DELTA : dot_product (firstn rank first_coeff) a-dot_product (firstn rank first_coeff) b=
    dot_product (firstn rank first_coeff) c-dot_product (firstn rank first_coeff) d).
  { rewrite !canonical_dot_difference by lia; rewrite DIFFERENCE; reflexivity. }
  lia.
Qed.

Theorem linear_alias_difference_exact rank sizes original first second a b c d values :
  canonical_loop_linear_map rank (snd first)=canonical_loop_linear_map rank (snd second) ->
  length a=rank -> length b=rank -> length c=rank -> length d=rank ->
  canonical_coordinate_difference a b=canonical_coordinate_difference c d ->
  (exists location, multi_tensor_locations original sizes (exact_cell first (a++values))=Some location) ->
  (exists location, multi_tensor_locations original sizes (exact_cell second (b++values))=Some location) ->
  (exists location, multi_tensor_locations original sizes (exact_cell first (c++values))=Some location) ->
  (exists location, multi_tensor_locations original sizes (exact_cell second (d++values))=Some location) ->
  multi_tensor_affine_access_check (multi_tensor_locations original sizes) first second (a++values) (b++values)=
    multi_tensor_affine_access_check (multi_tensor_locations original sizes) first second (c++values) (d++values).
Proof.
  intros MAP A_LENGTH B_LENGTH C_LENGTH D_LENGTH DIFFERENCE [la A] [lb B] [lc C] [ld D].
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
    destruct first as [first_id first_terms],second as [second_id second_terms].
    cbn [exact_cell arr_id arr_index] in POINTER_A,POINTER_B,POINTER_C,POINTER_D,INDEX_A,INDEX_B,INDEX_C,INDEX_D.
    rewrite POINTER_A in POINTER_C; inversion POINTER_C; subst block_c base_c.
    rewrite POINTER_B in POINTER_D; inversion POINTER_D; subst block_d base_d.
    assert (INDEX_DIFFERENCE : index_a-index_b=index_c-index_d).
    { eapply canonical_tensor_index_difference; [exact INDEX_A|exact INDEX_B|exact INDEX_C|exact INDEX_D|].
      eapply linear_affine_difference; eassumption. }
    rewrite (@canonical_alias_resolved_check (multi_tensor_locations original sizes)
      (first_id,first_terms) (second_id,second_terms) (a++values) (b++values) la lb DISTINCT A B),
      (@canonical_alias_resolved_check (multi_tensor_locations original sizes)
      (first_id,first_terms) (second_id,second_terms) (c++values) (d++values) lc ld DISTINCT C D).
    subst la lb lc ld; cbn [location_block location_offset].
    rewrite (@canonical_pointer_offsets_equal base_a base_b index_a index_b index_c index_d INDEX_DIFFERENCE);
      reflexivity.
Qed.

Theorem linear_alias_check_exact sizes original accesses values counts :
  Forall (fun count => 0<=count) counts ->
  linear_alias_templates_check (length counts) accesses=true ->
  (forall point access,
    Forall2 (fun coordinate count => 0<=coordinate<count) point counts -> In access accesses ->
    exists location, multi_tensor_locations original sizes (exact_cell access (point++values))=Some location) ->
  canonical_alias_check (multi_tensor_locations original sizes) accesses values counts=
    multi_tensor_affine_scan_check (multi_tensor_locations original sizes) accesses values counts.
Proof.
  intros COUNTS TEMPLATES RESOLVE; apply Bool.eq_true_iff_eq.
  unfold canonical_alias_check; rewrite memory_boolean_rectangle_member
    by (apply Forall_map; apply Forall_forall; intros; apply canonical_difference_bound_nonnegative).
  cbn [app]; rewrite multi_tensor_affine_scan_check_member by exact COUNTS; split.
  - intros CHECK a b first second A B FIRST SECOND.
    destruct (canonical_difference_coverage A B) as [POSITIONS DIFFERENCE].
    set (positions:=canonical_difference_positions counts a b).
    fold positions in POSITIONS,DIFFERENCE.
    destruct (canonical_difference_points COUNTS POSITIONS) as [C D].
    specialize (CHECK positions POSITIONS); unfold multi_tensor_affine_point_check in CHECK.
    apply forallb_forall with (x:=first) in CHECK; [|exact FIRST].
    apply forallb_forall with (x:=second) in CHECK; [|exact SECOND].
    rewrite <-CHECK; eapply linear_alias_difference_exact.
    + eapply linear_alias_templates_sound; eassumption.
    + exact (Forall2_length A).
    + exact (Forall2_length B).
    + exact (Forall2_length C).
    + exact (Forall2_length D).
    + exact DIFFERENCE.
    + apply RESOLVE; assumption.
    + apply RESOLVE; assumption.
    + apply RESOLVE; assumption.
    + apply RESOLVE; assumption.
  - intros CHECK positions POSITIONS; destruct (canonical_difference_points COUNTS POSITIONS) as [C D].
    unfold multi_tensor_affine_point_check; apply forallb_forall; intros first FIRST;
      apply forallb_forall; intros second SECOND; apply CHECK; assumption.
Qed.

Theorem linear_alias_source_exact counts values instructions sizes original memory final :
  Forall (fun count => 0<=count) counts ->
  linear_alias_templates_check (length counts) (multi_tensor_instruction_templates instructions)=true ->
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) instructions)
    (counts++values) (RuntimeState (multi_tensor_locations original sizes) memory)
      (RuntimeState (multi_tensor_locations original sizes) final) ->
  canonical_alias_check (multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates instructions) values counts=
  multi_tensor_affine_scan_check (multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates instructions) values counts.
Proof.
  intros COUNTS TEMPLATES SOURCE; apply linear_alias_check_exact; [exact COUNTS|exact TEMPLATES|].
  intros point access POINT ACCESS.
  destruct (@multi_tensor_affine_source_point_receipts counts values instructions
    (multi_tensor_locations original sizes) memory final SOURCE point access POINT ACCESS)
    as [location [RESOLVE PERMISSION]]; exists location; exact RESOLVE.
Qed.

Theorem linear_alias_source_nonalias dimensions sizes original memory final counts values instructions
    (ge : genv) (locals : env) :
  tensor_layout_flag sizes=true -> tensor_dimension_view dimensions sizes original ->
  Forall (fun count => 0<=count) counts ->
  linear_alias_templates_check (length counts) (multi_tensor_instruction_templates instructions)=true ->
  L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) instructions)
    (counts++values) (RuntimeState (multi_tensor_locations original sizes) memory)
      (RuntimeState (multi_tensor_locations original sizes) final) ->
  canonical_alias_check (multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates instructions) values counts=true ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed
    (multi_tensor_affine_source_footprint counts values instructions)) (multi_tensor_locations original sizes)).
Proof.
  intros LAYOUT DIMENSIONS COUNTS TEMPLATES SOURCE CHECK.
  rewrite (@linear_alias_source_exact counts values instructions sizes original memory final
    COUNTS TEMPLATES SOURCE) in CHECK.
  eapply multi_tensor_affine_scan_footprint_separation with (ge:=ge) (locals:=locals); eassumption.
Qed.

Example shifted_and_parameterized_templates_checked :
  let accesses : list AccessFunction :=
    [(1%positive,[([1;0;7],0);([0;1;0],0)]);
     (2%positive,[([1;0;13],4);([0;1;1],1)])] in
  canonical_alias_templates_check accesses=false /\ linear_alias_templates_check 2 accesses=true.
Proof. vm_compute; auto. Qed.
Example changed_loop_coefficient_refused :
  linear_alias_templates_check 2
    [(1%positive,[([1;0],0)]);(2%positive,[([2;0],1)])]=false.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions linear_alias_templates_sound.
Print Assumptions linear_alias_templates_include_strict.
Print Assumptions linear_dot_append.
Print Assumptions linear_affine_difference.
Print Assumptions linear_alias_difference_exact.
Print Assumptions linear_alias_check_exact.
Print Assumptions linear_alias_source_exact.
Print Assumptions linear_alias_source_nonalias.
Print Assumptions shifted_and_parameterized_templates_checked.
Print Assumptions changed_loop_coefficient_refused.
