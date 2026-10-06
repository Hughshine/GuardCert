From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightPureExpr ClightSameAddress ClightNoWrap CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRectangles GuardMemoryBufferOffsets GuardMemoryMultiPointerCells.
From GuardInterface Require Import AffineBoxEnvelope ClightAffineEnvelope ClightSourceObservation
  ClightLoadedBoundSyntax ClightReadonlyLoadedTreeSynthesis.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition observed_base_equal first second :=
  Ebinop Oeq (signed_pointer_temp first) (signed_pointer_temp second) type_int32s.
Theorem observed_base_equal_exact first second entry answer :
  observed_pointer_domain [first;second] entry ->
  (expression_test (observed_base_equal first second) entry answer <-> answer = address_accept first second entry).
Proof.
  intro OBSERVED.
  destruct (OBSERVED first ltac:(cbn; auto)) as [block [offset [FIRST VALID_FIRST]]].
  destruct (OBSERVED second ltac:(cbn; auto)) as [other [other_offset [SECOND VALID_SECOND]]].
  assert (TEST : expression_test (observed_base_equal first second) entry (address_accept first second entry)).
  { unfold address_accept; rewrite FIRST,SECOND.
    exists (Val.of_bool (address_flag block offset other other_offset)); split; [|apply bool_of_bool].
    eapply eval_Ebinop; [constructor; exact FIRST|constructor; exact SECOND|].
    change (cmp_ptr (entry_memory entry) Ceq (Vptr block offset) (Vptr other other_offset) =
      Some (Val.of_bool (address_flag block offset other other_offset))).
    apply pointer_equality_value; assumption. }
  split; [intro RUN; eapply (@pure_test_determinate (observed_base_equal first second) entry);
    [constructor; constructor|exact RUN|exact TEST]|].
  intros ->; exact TEST.
Qed.

Definition compile_affine_envelope_separation dimensions registers limits first second : option decision_tree :=
  match synthesize_affine_envelope dimensions first,synthesize_affine_envelope dimensions second with
  | Some (first_lower,first_upper),Some (second_lower,second_upper) =>
    match compile_affine_comparison registers limits first_upper second_lower,
      compile_affine_comparison registers limits second_upper first_lower with
    | Some forward,Some backward => Some (Test forward (Decision true)
        (Test backward (Decision true) (Decision false)))
    | _,_ => None end
  | _,_ => None end.

Definition affine_box_separation dimensions first second values :=
  match synthesize_affine_envelope dimensions first,synthesize_affine_envelope dimensions second with
  | Some first_bounds,Some second_bounds => affine_envelopes_disjoint first_bounds second_bounds values
  | _,_ => false end.

Theorem compiled_affine_envelope_separation_exact dimensions registers limits first second tree
  ge locals temps memory values answer :
  compile_affine_envelope_separation dimensions registers limits first second = Some tree ->
  affine_registers_view registers values temps ->
  Forall2 (fun value limit => 0 <= value < limit) values limits ->
  (decision_run (Entry ge locals temps memory) tree answer <->
    answer = affine_box_separation dimensions first second values).
Proof.
  unfold compile_affine_envelope_separation.
  destruct (synthesize_affine_envelope dimensions first) as [[first_lower first_upper]|] eqn:FIRST; [|discriminate].
  destruct (synthesize_affine_envelope dimensions second) as [[second_lower second_upper]|] eqn:SECOND; [|discriminate].
  destruct (compile_affine_comparison registers limits first_upper second_lower) as [forward|] eqn:FORWARD; [|discriminate].
  destruct (compile_affine_comparison registers limits second_upper first_lower) as [backward|] eqn:BACKWARD; [|discriminate].
  intros ENCODE WORDS RANGES; injection ENCODE as <-.
  unfold affine_box_separation; rewrite FIRST,SECOND; unfold affine_envelopes_disjoint; cbn [fst snd].
  set (up_down := affine_value first_upper values <? affine_value second_lower values).
  set (down_up := affine_value second_upper values <? affine_value first_lower values).
  assert (FWD : expression_test forward (Entry ge locals temps memory) up_down).
  { apply (proj2 (@compiled_affine_comparison_exact ge locals temps memory registers limits
      values first_upper second_lower forward up_down FORWARD WORDS RANGES)); reflexivity. }
  assert (BWD : expression_test backward (Entry ge locals temps memory) down_up).
  { apply (proj2 (@compiled_affine_comparison_exact ge locals temps memory registers limits
      values second_upper first_lower backward down_up BACKWARD WORDS RANGES)); reflexivity. }
  assert (RUN : decision_run (Entry ge locals temps memory)
    (Test forward (Decision true) (Test backward (Decision true) (Decision false))) (up_down || down_up)).
  { eapply run_test; [exact FWD|]; destruct up_down; cbn; [constructor|].
    eapply run_test; [exact BWD|]; destruct down_up; constructor. }
  split; [intro ACTUAL; eapply readonly_decision_determinate; eassumption|intros ->; exact RUN].
Qed.

(** Both comparison encodings are certified over the permitted header range.
    The derivation covers every pair of source points, not just endpoints. *)
Theorem compiled_affine_envelope_separation_sound dimensions registers limits first second tree
  ge locals temps memory counts parameters :
  compile_affine_envelope_separation dimensions registers limits first second = Some tree ->
  length counts = dimensions ->
  affine_registers_view registers (counts++parameters) temps ->
  Forall2 (fun value limit => 0 <= value < limit) (counts++parameters) limits ->
  (exists answer, decision_run (Entry ge locals temps memory) tree answer) /\
  (decision_run (Entry ge locals temps memory) tree true -> forall left right,
    Forall2 (fun coordinate count => 0 <= coordinate < count) left counts ->
    Forall2 (fun coordinate count => 0 <= coordinate < count) right counts ->
    affine_value first (left++parameters) <> affine_value second (right++parameters)).
Proof.
  unfold compile_affine_envelope_separation.
  destruct (synthesize_affine_envelope dimensions first) as [[first_lower first_upper]|] eqn:FIRST; [|discriminate].
  destruct (synthesize_affine_envelope dimensions second) as [[second_lower second_upper]|] eqn:SECOND; [|discriminate].
  destruct (compile_affine_comparison registers limits first_upper second_lower) as [forward|] eqn:FORWARD; [|discriminate].
  destruct (compile_affine_comparison registers limits second_upper first_lower) as [backward|] eqn:BACKWARD; [|discriminate].
  intros ENCODE DIMENSIONS WORDS RANGES; injection ENCODE as <-.
  set (up_down := affine_value first_upper (counts++parameters) <? affine_value second_lower (counts++parameters)).
  set (down_up := affine_value second_upper (counts++parameters) <? affine_value first_lower (counts++parameters)).
  assert (FWD : expression_test forward (Entry ge locals temps memory) up_down).
  { apply (proj2 (@compiled_affine_comparison_exact ge locals temps memory registers limits
      (counts++parameters) first_upper second_lower forward up_down FORWARD WORDS RANGES)); reflexivity. }
  assert (BWD : expression_test backward (Entry ge locals temps memory) down_up).
  { apply (proj2 (@compiled_affine_comparison_exact ge locals temps memory registers limits
      (counts++parameters) second_upper first_lower backward down_up BACKWARD WORDS RANGES)); reflexivity. }
  assert (RUN : decision_run (Entry ge locals temps memory)
    (Test forward (Decision true) (Test backward (Decision true) (Decision false))) (up_down || down_up)).
  { eapply run_test; [exact FWD|]; destruct up_down; cbn; [constructor|].
    eapply run_test; [exact BWD|]; destruct down_up; constructor. }
  split; [eexists; exact RUN|].
  intros ACCEPT left right LEFT RIGHT.
  assert (DISJOINT : up_down || down_up = true) by (eapply readonly_decision_determinate; eassumption).
  apply (@synthesized_affine_envelopes_disjoint dimensions first second
    (first_lower,first_upper) (second_lower,second_upper) counts parameters left right FIRST SECOND DIMENSIONS LEFT RIGHT).
  exact DISJOINT.
Qed.

Definition compile_observed_affine_separation dimensions registers limits first_id second_id first second :=
  option_map (fun tree => Test (observed_base_equal first_id second_id) tree (Decision false))
    (compile_affine_envelope_separation dimensions registers limits first second).

Theorem compiled_observed_affine_separation_exact dimensions registers limits first_id second_id first second tree
  ge locals temps memory values answer :
  compile_observed_affine_separation dimensions registers limits first_id second_id first second = Some tree ->
  observed_pointer_domain [first_id;second_id] (Entry ge locals temps memory) ->
  affine_registers_view registers values temps ->
  Forall2 (fun value limit => 0 <= value < limit) values limits ->
  (decision_run (Entry ge locals temps memory) tree answer <->
    answer = address_accept first_id second_id (Entry ge locals temps memory) &&
      affine_box_separation dimensions first second values).
Proof.
  unfold compile_observed_affine_separation.
  destruct (compile_affine_envelope_separation dimensions registers limits first second) as [inner|] eqn:INNER;
    cbn; [|discriminate].
  intros ENCODE OBSERVED WORDS RANGES; injection ENCODE as <-.
  pose proof (proj2 (@observed_base_equal_exact first_id second_id (Entry ge locals temps memory)
    (address_accept first_id second_id (Entry ge locals temps memory)) OBSERVED) eq_refl) as BASE.
  pose proof (proj2 (@compiled_affine_envelope_separation_exact dimensions registers limits first second inner
    ge locals temps memory values (affine_box_separation dimensions first second values) INNER WORDS RANGES) eq_refl) as RUN.
  assert (ACTUAL : decision_run (Entry ge locals temps memory)
    (Test (observed_base_equal first_id second_id) inner (Decision false))
    (address_accept first_id second_id (Entry ge locals temps memory) && affine_box_separation dimensions first second values)).
  { eapply run_test; [exact BASE|].
    destruct (address_accept first_id second_id (Entry ge locals temps memory)); [exact RUN|constructor]. }
  split; [intro TEST; eapply readonly_decision_determinate; eassumption|intros ->; exact ACTUAL].
Qed.

Theorem compiled_observed_affine_separation_sound dimensions registers limits first_id second_id first second tree
  ge locals temps memory counts parameters :
  compile_observed_affine_separation dimensions registers limits first_id second_id first second = Some tree ->
  observed_pointer_domain [first_id;second_id] (Entry ge locals temps memory) ->
  length counts = dimensions ->
  affine_registers_view registers (counts++parameters) temps ->
  Forall2 (fun value limit => 0 <= value < limit) (counts++parameters) limits ->
  (exists answer, decision_run (Entry ge locals temps memory) tree answer) /\
  (decision_run (Entry ge locals temps memory) tree true ->
    exists block base, temps ! first_id = Some (Vptr block base) /\ temps ! second_id = Some (Vptr block base) /\
    forall left right,
      Forall2 (fun coordinate count => 0 <= coordinate < count) left counts ->
      Forall2 (fun coordinate count => 0 <= coordinate < count) right counts ->
      affine_value first (left++parameters) <> affine_value second (right++parameters)).
Proof.
  unfold compile_observed_affine_separation.
  destruct (compile_affine_envelope_separation dimensions registers limits first second) as [inner|] eqn:INNER;
    cbn; [|discriminate].
  intros ENCODE OBSERVED DIMENSIONS WORDS RANGES; injection ENCODE as <-.
  destruct (@compiled_affine_envelope_separation_sound dimensions registers limits first second inner
    ge locals temps memory counts parameters INNER DIMENSIONS WORDS RANGES) as [[answer RUN] SOUND].
  pose proof (proj2 (@observed_base_equal_exact first_id second_id (Entry ge locals temps memory)
    (address_accept first_id second_id (Entry ge locals temps memory)) OBSERVED) eq_refl) as TEST.
  split.
  - destruct (address_accept first_id second_id (Entry ge locals temps memory)) eqn:ACCEPT;
      eexists; eapply run_test; [exact TEST|exact RUN|exact TEST|constructor].
  - intro ACCEPT; inversion ACCEPT; subst.
    match goal with LEAF : decision_run _ (if ?choice then inner else Decision false) true |- _ =>
      destruct choice eqn:CHOICE; [|inversion LEAF] end.
    match goal with TEST : expression_test (observed_base_equal _ _) _ true |- _ =>
      apply (proj1 (@observed_base_equal_exact _ _ _ _ OBSERVED)) in TEST;
      symmetry in TEST; apply address_accept_sound in TEST end.
    match goal with SAME : addresses_equal _ _ _ _ |- _ => destruct SAME as [pointer [FIRST SECOND]] end.
    destruct (OBSERVED first_id ltac:(cbn; auto)) as [block [base [BINDING VALID]]].
    assert (POINTER : pointer = Vptr block base) by congruence; subst pointer.
    exists block,base; split; [exact FIRST|split; [exact SECOND|apply SOUND; assumption]].
Qed.

(** Integer separation becomes physical Mint32 separation in the language
    model, including modular pointer wraparound. No pointer order is used. *)
Theorem common_base_envelope_cell_separation temps extent first_id second_id block base first second left right :
  4*extent <= Ptrofs.modulus ->
  temps ! first_id = Some (Vptr block base) -> temps ! second_id = Some (Vptr block base) ->
  0 <= first < extent -> 0 <= second < extent -> first <> second ->
  memory_multi_pointer_locations temps extent (point_cell first_id first) = Some left ->
  memory_multi_pointer_locations temps extent (point_cell second_id second) = Some right ->
  location_disjoint left right.
Proof.
  intros EXTENT FIRST SECOND FIRST_RANGE SECOND_RANGE DISTINCT LEFT RIGHT.
  destruct (@memory_multi_pointer_location_inverse temps extent (point_cell first_id first) left LEFT)
    as [b1 [o1 [i1 [P1 [I1 [R1 L1]]]]]].
  destruct (@memory_multi_pointer_location_inverse temps extent (point_cell second_id second) right RIGHT)
    as [b2 [o2 [i2 [P2 [I2 [R2 L2]]]]]].
  cbn [point_cell arr_id arr_index] in P1,P2,I1,I2.
  assert (PTR1 : Vptr b1 o1 = Vptr block base) by congruence; injection PTR1; intros; subst b1 o1.
  assert (PTR2 : Vptr b2 o2 = Vptr block base) by congruence; injection PTR2; intros; subst b2 o2.
  injection I1 as <-; injection I2 as <-; subst left right.
  right; cbn [location_block location_chunk location_offset size_chunk].
  apply memory_buffer_cell_separation with (extent:=extent);
    [pose proof Ptrofs.modulus_pos; lia|apply memory_pointer_modulus_cells|exact EXTENT|exact FIRST_RANGE|exact SECOND_RANGE|exact DISTINCT].
Qed.

Print Assumptions observed_base_equal_exact.
Print Assumptions compiled_affine_envelope_separation_exact.
Print Assumptions compiled_affine_envelope_separation_sound.
Print Assumptions compiled_observed_affine_separation_sound.
Print Assumptions compiled_observed_affine_separation_exact.
Print Assumptions common_base_envelope_cell_separation.

Example separated_parametric_slices_compile :
  exists tree, compile_observed_affine_separation 2 [11%positive;12%positive;13%positive]
    [17;17;64] 1%positive 2%positive ([16;1;1],32) ([16;1;1],128) = Some tree.
Proof. vm_compute; eexists; reflexivity. Qed.
Example separated_parametric_slices_accept :
  affine_box_separation 2 ([16;1;1],32) ([16;1;1],128) [2;2;0] = true.
Proof. reflexivity. Qed.
Example overlapping_parametric_slices_refuse :
  affine_box_separation 2 ([16;1;1],32) ([16;1;1],128) [7;7;0] = false.
Proof. reflexivity. Qed.
