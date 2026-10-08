From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.lib Require Import Linalg.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightNoWrap CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops
  GuardMemoryLoopTrace GuardMemoryScalarLoops GuardMemoryFiniteFootprint GuardMemoryRectangularFootprint
  GuardMemoryRuntimeReceipts GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend
  GuardMemoryRecursiveSource GuardMemoryMultiTensorBackend GuardMemoryMultiTensorFrame
  GuardMemoryMultiTensorSourceRegion GuardMemoryBooleanScan GuardMemoryBooleanPairRectangle
  GuardMemoryMultiTensorPairScan GuardMemoryMultiTensorPairSeparation.
From GuardInterface Require Import ClightMultiTensorExample ClightMultiTensorSourceExample ClightMultiTensorCandidates.
Import ListNotations.
Local Open Scope Z_scope.

Definition multi_tensor_demo_identity_terms :=
  [([1;0;0;0;0],0);([0;1;0;0;0],0);([0;0;1;0;0],0)].
Example multi_tensor_demo_checked_instruction_data : multi_tensor_nest_demo_instructions =
  [MemoryInstruction (9%positive,multi_tensor_demo_identity_terms)
     [(10%positive,multi_tensor_demo_identity_terms)] multi_tensor_demo_value;
   MemoryInstruction (10%positive,multi_tensor_demo_identity_terms)
     [(9%positive,multi_tensor_demo_identity_terms)] multi_tensor_demo_value].
Proof. vm_compute; reflexivity. Qed.

Lemma multi_tensor_demo_point_footprint i j k ld alpha :
  memory_point_footprint multi_tensor_nest_demo_instructions [i;j;k;ld;alpha] =
  [multi_tensor_coordinate_cell 9%positive [i;j;k]; multi_tensor_coordinate_cell 10%positive [i;j;k];
   multi_tensor_coordinate_cell 10%positive [i;j;k]; multi_tensor_coordinate_cell 9%positive [i;j;k]].
Proof.
  rewrite multi_tensor_demo_checked_instruction_data.
  cbv beta iota zeta delta [memory_point_footprint memory_instruction_footprint flat_map instruction_write instruction_reads
    exact_cell multi_tensor_demo_identity_terms affine_product map fst snd dot_product app].
  repeat rewrite Z.mul_0_l; repeat rewrite Z.mul_1_l;
    repeat rewrite Z.add_0_r; repeat rewrite Z.add_0_l; reflexivity.
Qed.

Definition multi_tensor_demo_pair_footprint counts values :=
  multi_tensor_source_footprint (length counts) (length values) multi_tensor_nest_demo_instructions
    (map Z.of_nat counts++values).

Lemma multi_tensor_demo_pair_footprint_exact counts values :
  length counts = 3%nat -> length values = 2%nat ->
  multi_tensor_demo_pair_footprint counts values = flat_map (fun coordinates =>
    [multi_tensor_coordinate_cell 9%positive coordinates;multi_tensor_coordinate_cell 10%positive coordinates;
     multi_tensor_coordinate_cell 10%positive coordinates;multi_tensor_coordinate_cell 9%positive coordinates])
    (memory_rectangular_points (map Z.of_nat counts) []).
Proof.
  intros COUNT_LENGTH VALUE_LENGTH.
  pose proof (@memory_scalar_rectangle_footprint (map Z.of_nat counts) multi_tensor_nest_demo_instructions
    values [] [] eq_refl) as FOOTPRINT.
  cbn [rev app length] in FOOTPRINT; rewrite length_map in FOOTPRINT.
  unfold multi_tensor_demo_pair_footprint,multi_tensor_source_footprint; rewrite FOOTPRINT.
  rewrite !flat_map_concat_map; f_equal; apply map_ext_in; intros coordinates MEMBER.
  apply memory_rectangular_points_origin in MEMBER.
  pose proof (Forall2_length MEMBER) as LENGTH; rewrite length_map,COUNT_LENGTH in LENGTH.
  destruct coordinates as [|i [|j [|k [|extra tail]]]]; cbn in LENGTH; try discriminate.
  destruct values as [|ld [|alpha [|extra tail]]]; cbn in VALUE_LENGTH; try discriminate.
  apply multi_tensor_demo_point_footprint.
Qed.

Lemma multi_tensor_demo_pair_footprint_covered counts values :
  length counts = 3%nat -> length values = 2%nat ->
  Forall (multi_tensor_pair_cell_covered (map Z.of_nat counts) 9%positive 10%positive)
    (multi_tensor_demo_pair_footprint counts values).
Proof.
  intros COUNT_LENGTH VALUE_LENGTH; rewrite multi_tensor_demo_pair_footprint_exact by assumption.
  apply Forall_forall; intros cell MEMBER; apply in_flat_map in MEMBER as [coordinates [POINT MEMBER]].
  apply memory_rectangular_points_origin in POINT.
  cbn in MEMBER; destruct MEMBER as [SAME|[SAME|[SAME|[SAME|[]]]]]; subst cell;
    unfold multi_tensor_pair_cell_covered; cbn; split; auto.
Qed.

Lemma multi_tensor_demo_pair_point_members counts values coordinates :
  length counts = 3%nat -> length values = 2%nat ->
  Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates (map Z.of_nat counts) ->
  In (multi_tensor_coordinate_cell 9%positive coordinates) (multi_tensor_demo_pair_footprint counts values) /\
  In (multi_tensor_coordinate_cell 10%positive coordinates) (multi_tensor_demo_pair_footprint counts values).
Proof.
  intros COUNT_LENGTH VALUE_LENGTH RANGE; rewrite multi_tensor_demo_pair_footprint_exact by assumption.
  assert (POINT : In coordinates (memory_rectangular_points (map Z.of_nat counts) [])).
  { apply memory_rectangular_points_origin; exact RANGE. }
  split; apply in_flat_map; exists coordinates; split; [exact POINT|cbn; auto|exact POINT|cbn; auto].
Qed.

(** One fixed program for every runtime count/ld/alpha value. The counters and
    flag are example private names, not specializations to a runtime footprint. *)
Definition multi_tensor_demo_pair_left := [211%positive;212%positive;213%positive].
Definition multi_tensor_demo_pair_right := [221%positive;222%positive;223%positive].
Definition multi_tensor_demo_pair_flag := 201%positive.
Definition multi_tensor_demo_pair_live := [2%positive;5%positive;6%positive;7%positive;8%positive].
Definition multi_tensor_demo_pair_public :=
  [1%positive;3%positive;4%positive]++9%positive::10%positive::
    tensor_dimension_registers multi_tensor_demo_dimensions++multi_tensor_demo_pair_live.
Definition multi_tensor_demo_pair_program := multi_tensor_pair_scan multi_tensor_demo_dimensions
  multi_tensor_demo_pair_left multi_tensor_demo_pair_right [1%positive;3%positive;4%positive]
  multi_tensor_demo_pair_flag 9%positive 10%positive.
Definition multi_tensor_demo_pair_guard := Ssequence
  (Sset multi_tensor_demo_pair_flag (Econst_int Int.one type_int32s)) multi_tensor_demo_pair_program.

Theorem multi_tensor_demo_source_licensed_pair_scan fe ge locals counts values sizes temps memory source_after final
    current :
  length counts = 3%nat -> Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  memory_nest_bindings [1%positive;3%positive;4%positive] (map Z.of_nat counts) temps ->
  temps!6%positive = Some (Vint Int.zero) ->
  tensor_layout_flag sizes = true -> tensor_dimension_view multi_tensor_demo_dimensions sizes temps ->
  memory_nest_bindings [2%positive;5%positive] values temps ->
  multi_tensor_body_box multi_tensor_nest_demo_items counts values sizes = true ->
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 source_after final Out_normal ->
  temp_agree multi_tensor_demo_pair_public temps current ->
  current!multi_tensor_demo_pair_flag = Some (memory_boolean_word true) ->
  exists checked,
    exec_stmt fe ge locals current memory multi_tensor_demo_pair_program E0 checked memory Out_normal /\
    temp_agree multi_tensor_demo_pair_public current checked /\
    checked!multi_tensor_demo_pair_flag = Some (memory_boolean_word
      (multi_tensor_pair_check (multi_tensor_locations temps sizes) (map Z.of_nat counts) 9%positive 10%positive)) /\
    (checked!multi_tensor_demo_pair_flag = Some (memory_boolean_word true) ->
      multi_tensor_separated_source (length counts) (length values) multi_tensor_nest_demo_instructions
        (map Z.of_nat counts++values) temps sizes).
Proof.
  intros LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS BOX SOURCE FRAME FLAG.
  assert (VALUE_LENGTH : length values = 2%nat).
  { pose proof (Forall2_length SCALARS) as VALUE_LENGTH; cbn [length] in VALUE_LENGTH; lia. }
  destruct (@multi_tensor_nest_demo_source_execution fe ge locals counts values sizes temps memory source_after final
    LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS BOX SOURCE) as [MODEL _].
  pose proof (@memory_loop_entry_footprint_readable _ _ _ _ MODEL) as RECEIPTS.
  change (Forall (fun cell => memory_cell_access (multi_tensor_locations temps sizes) memory cell Readable)
    (multi_tensor_demo_pair_footprint counts values)) in RECEIPTS.
  assert (POINT_RECEIPTS : forall coordinates,
    Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates (map Z.of_nat counts) ->
    memory_cell_access (multi_tensor_locations temps sizes) memory (multi_tensor_coordinate_cell 9%positive coordinates) Readable /\
    memory_cell_access (multi_tensor_locations temps sizes) memory (multi_tensor_coordinate_cell 10%positive coordinates) Readable).
  { intros coordinates RANGE; destruct (@multi_tensor_demo_pair_point_members counts values coordinates
      LENGTH VALUE_LENGTH RANGE) as [FIRST SECOND].
    rewrite Forall_forall in RECEIPTS; split; apply RECEIPTS; assumption. }
  assert (RANGES : Forall (fun count => 0 <= count /\ signed_range count) (map Z.of_nat counts)).
  { apply Forall_map; eapply Forall_impl; [|exact COUNTS]; intros count [_ RANGE]; split; [lia|exact RANGE]. }
  destruct (@multi_tensor_pair_scan_execution multi_tensor_demo_dimensions sizes temps current memory
    multi_tensor_demo_pair_left multi_tensor_demo_pair_right [1%positive;3%positive;4%positive] (map Z.of_nat counts)
    multi_tensor_demo_pair_flag 9%positive 10%positive multi_tensor_demo_pair_live fe ge locals true
    ltac:(discriminate) LAYOUT DIMENSIONS
    ltac:(repeat constructor; cbn; intuition congruence)
    ltac:(intros identifier MEMBER; split; intro BAD; vm_compute in MEMBER,BAD; intuition congruence)
    ltac:(vm_compute; intuition congruence) RANGES
    ltac:(rewrite length_map,LENGTH; reflexivity) ltac:(rewrite length_map,LENGTH; reflexivity)
    BOUNDS POINT_RECEIPTS FRAME FLAG) as [checked [RUN [PUBLIC RESULT]]].
  exists checked; split; [exact RUN|split; [exact PUBLIC|split; [exact RESULT|intro ACCEPT]]].
  assert (CHECK : multi_tensor_pair_check (multi_tensor_locations temps sizes) (map Z.of_nat counts)
    9%positive 10%positive = true).
  { rewrite RESULT in ACCEPT; destruct (multi_tensor_pair_check _ _ _ _); [reflexivity|discriminate]. }
  unfold multi_tensor_separated_source; change (locations_nonalias
    (GuardMemoryFootprintRestriction.memory_restrict_locations
      (memory_footprint_allowed (multi_tensor_demo_pair_footprint counts values)) (multi_tensor_locations temps sizes))).
  eapply multi_tensor_pair_footprint_separation with (dimensions:=multi_tensor_demo_dimensions)
    (first:=9%positive) (second:=10%positive) (counts:=map Z.of_nat counts) (ge:=ge) (locals:=locals);
    [discriminate|exact LAYOUT|exact DIMENSIONS| |apply multi_tensor_demo_pair_footprint_covered; assumption|
     exact RECEIPTS|exact CHECK].
  apply Forall_map,Forall_forall; intros; lia.
Qed.

(** The emitted guard initializes its own private flag. Source users do not
    supply a premise about a pre-existing private register value. *)
Theorem multi_tensor_demo_source_licensed_pair_guard fe ge locals counts values sizes temps memory source_after final :
  length counts = 3%nat -> Forall (fun count => count <> O /\ signed_range (Z.of_nat count)) counts ->
  memory_nest_bindings [1%positive;3%positive;4%positive] (map Z.of_nat counts) temps ->
  temps!6%positive = Some (Vint Int.zero) ->
  tensor_layout_flag sizes = true -> tensor_dimension_view multi_tensor_demo_dimensions sizes temps ->
  memory_nest_bindings [2%positive;5%positive] values temps ->
  multi_tensor_body_box multi_tensor_nest_demo_items counts values sizes = true ->
  exec_stmt fe ge locals temps memory (memory_nest_source multi_tensor_nest_demo_nest) E0 source_after final Out_normal ->
  exists checked,
    exec_stmt fe ge locals temps memory multi_tensor_demo_pair_guard E0 checked memory Out_normal /\
    temp_agree multi_tensor_demo_pair_public temps checked /\
    checked!multi_tensor_demo_pair_flag = Some (memory_boolean_word
      (multi_tensor_pair_check (multi_tensor_locations temps sizes) (map Z.of_nat counts) 9%positive 10%positive)) /\
    (checked!multi_tensor_demo_pair_flag = Some (memory_boolean_word true) ->
      multi_tensor_separated_source (length counts) (length values) multi_tensor_nest_demo_instructions
        (map Z.of_nat counts++values) temps sizes).
Proof.
  intros LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS BOX SOURCE.
  set (initialized := PTree.set multi_tensor_demo_pair_flag (Vint Int.one) temps).
  assert (FRAME : temp_agree multi_tensor_demo_pair_public temps initialized).
  { unfold initialized; apply temp_agree_set; vm_compute; intuition congruence. }
  destruct (@multi_tensor_demo_source_licensed_pair_scan fe ge locals counts values sizes temps memory
    source_after final initialized LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS BOX SOURCE
    FRAME ltac:(unfold initialized; apply PTree.gss)) as [checked [RUN [PUBLIC [FLAG SOUND]]]].
  exists checked; split.
  - unfold multi_tensor_demo_pair_guard; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
      [constructor; constructor|exact RUN].
  - split; [eapply temp_agree_trans; eassumption|split; assumption].
Qed.

Print Assumptions multi_tensor_demo_checked_instruction_data.
Print Assumptions multi_tensor_demo_point_footprint.
Print Assumptions multi_tensor_demo_pair_footprint_exact.
Print Assumptions multi_tensor_demo_pair_footprint_covered.
Print Assumptions multi_tensor_demo_pair_point_members.
Print Assumptions multi_tensor_demo_source_licensed_pair_scan.
Print Assumptions multi_tensor_demo_source_licensed_pair_guard.
