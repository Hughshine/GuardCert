From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryScalarLoops
  GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction
  GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryDynamicTensorLayout
  GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorSourceCapabilities
  GuardMemoryMultiTensorSourceRegion GuardMemoryBooleanScan GuardMemoryMultiTensorAffineFootprint
  GuardMemoryMultiTensorAffineScan.
From GuardInterface Require Import ClightTensorBackendGuard ClightMultiTensorDataPackage
  ClightMultiTensorPackageExecution ClightMultiTensorScanAllocation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition multi_tensor_affine_package_ports source (package : multi_tensor_region_package source) live :=
  memory_nest_bounds (mtr_nest package) ++
    multi_tensor_affine_scan_public (mtr_dimensions (mtr_description package))
      (mtr_scalars (mtr_description package))
      (multi_tensor_instruction_templates (map mt_instruction (mtr_items package))) (statement_temps source++live).
Definition multi_tensor_affine_package_allocate source (package : multi_tensor_region_package source) live pool :=
  allocate_multi_tensor_scan source (multi_tensor_affine_package_ports package live) pool
    (length (memory_nest_iterators (mtr_nest package))).
Definition multi_tensor_affine_package_guard source (package : multi_tensor_region_package source) live pool
    (allocation : multi_tensor_scan_allocation source (multi_tensor_affine_package_ports package live) pool
      (length (memory_nest_iterators (mtr_nest package)))) :=
  Ssequence (Sset (mtas_flag allocation) (Econst_int Int.one type_int32s))
    (multi_tensor_affine_scan_statement (mtr_dimensions (mtr_description package))
      (mtas_left allocation) (mtas_right allocation) (memory_nest_bounds (mtr_nest package))
      (mtr_scalars (mtr_description package)) (mtas_flag allocation)
      (multi_tensor_instruction_templates (map mt_instruction (mtr_items package)))).

Section SOURCE_SCAN.
Variable source : statement.
Variable package : multi_tensor_region_package source.
Variable live : list ident.
Variable pool : list (ident * type).
Let dimensions := mtr_dimensions (mtr_description package).
Let nest := mtr_nest package.
Let scalars := mtr_scalars (mtr_description package).
Let items := mtr_items package.
Let instructions := map mt_instruction items.
Let accesses := multi_tensor_instruction_templates instructions.
Let ports := multi_tensor_affine_package_ports package live.
Variable allocation : multi_tensor_scan_allocation source ports pool (length (memory_nest_iterators nest)).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.

(** The source user supplies syntax/metadata and a typed pool. Actual source
    definedness and accepted setup produce all scan permissions internally. *)
Theorem multi_tensor_affine_package_source_scan ge locals original current memory source_after final :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  decision_run (Entry ge locals original memory) (multi_tensor_package_setup_guard package) true ->
  temp_agree ports original current ->
  let counts := memory_recursive_counts (memory_nest_bounds nest) original in
  let values := memory_recursive_parameters scalars original in
  exists sizes checked,
    exec_stmt fe ge locals current memory (multi_tensor_affine_package_guard package live allocation)
      E0 checked memory Out_normal /\
    temp_agree (statement_temps source++live) current checked /\
    temp_agree ports current checked /\
    tensor_layout_flag sizes = true /\ tensor_dimension_view dimensions sizes original /\
    L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) instructions)
      (map Z.of_nat counts++values) (RuntimeState (multi_tensor_locations original sizes) memory)
      (RuntimeState (multi_tensor_locations original sizes) final) /\
    checked!(mtas_flag allocation) = Some (memory_boolean_word
      (multi_tensor_affine_scan_check (multi_tensor_locations original sizes) accesses values (map Z.of_nat counts))) /\
    (checked!(mtas_flag allocation) = Some (memory_boolean_word true) ->
      locations_nonalias (memory_restrict_locations (memory_footprint_allowed
        (multi_tensor_affine_source_footprint (map Z.of_nat counts) values instructions))
        (multi_tensor_locations original sizes))).
Proof.
  intros SOURCE SETUP FRAME counts values.
  destruct (@multi_tensor_package_setup_accept source package fe ge locals original memory source_after final SOURCE SETUP)
    as [sizes (LENGTH & COUNTS & BOUNDS & INITIAL & SCALARS & SIGNED & OBSERVE & BACKEND & BOX & WITHIN)].
  pose proof (@tensor_backend_guard_accepts (Entry ge locals original memory) dimensions sizes OBSERVE BACKEND) as LAYOUT.
  destruct (@tensor_observe_dimensions_sound dimensions original sizes OBSERVE) as [DIMENSIONS _].
  assert (MODEL : L.loop_semantics (memory_scalar_rectangle 0 (length counts) (length values) instructions)
    (map Z.of_nat counts++values) (RuntimeState (multi_tensor_locations original sizes) memory)
      (RuntimeState (multi_tensor_locations original sizes) final)).
  { destruct (@multi_tensor_source_region_decode dimensions nest scalars (multi_tensor_body_pointers items)
      items fe ge locals counts values sizes original memory source_after final
      (mtr_body package) (mtr_shapes package) (mtr_fresh package) (mtr_unique package)
      (mtr_protected package) LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS
      (multi_tensor_body_pointers_check items) BOX) as [MODEL _]; [|exact MODEL].
    eapply multi_tensor_region_source_execution; exact SOURCE. }
  assert (MODEL_Z : L.loop_semantics
    (memory_scalar_rectangle 0 (length (map Z.of_nat counts)) (length values) instructions)
    (map Z.of_nat counts++values) (RuntimeState (multi_tensor_locations original sizes) memory)
      (RuntimeState (multi_tensor_locations original sizes) final)).
  { rewrite length_map; exact MODEL. }
  assert (UNIQUE : NoDup (mtas_left allocation++mtas_right allocation)).
  { apply (@NoDup_app_remove_r _ (mtas_left allocation++mtas_right allocation) [mtas_flag allocation]).
    rewrite <-app_assoc; exact (mtas_unique allocation). }
  assert (FLAG_CURSORS : ~ In (mtas_flag allocation) (mtas_left allocation++mtas_right allocation)).
  { intro BAD; apply in_split in BAD as [prefix [suffix SAME]].
    pose proof (mtas_unique allocation) as ALL; rewrite app_assoc,SAME,<-app_assoc in ALL; cbn in ALL.
    apply NoDup_remove_2 in ALL; apply ALL; apply in_or_app; right; apply in_or_app; right; cbn; auto. }
  assert (FLAG_PUBLIC : ~ In (mtas_flag allocation) ports).
  { intro BAD; eapply multi_tensor_scan_allocation_fresh with (allocation:=allocation) (identifier:=mtas_flag allocation).
    - apply in_or_app; right; exact BAD.
    - unfold multi_tensor_scan_private; repeat rewrite in_app_iff; cbn; tauto. }
  assert (FRESH : forall id, In id (mtas_left allocation++mtas_right allocation) ->
    ~ In id ports /\ id <> mtas_flag allocation).
  { intros id PRIVATE; split.
    - intro PUBLIC; eapply multi_tensor_scan_allocation_fresh with (allocation:=allocation) (identifier:=id).
      + apply in_or_app; right; exact PUBLIC.
      + unfold multi_tensor_scan_private; rewrite app_assoc; apply in_or_app; left; exact PRIVATE.
    - intro SAME; subst id; contradiction. }
  assert (RANGES : Forall (fun count => 0 <= count /\ signed_range count) (map Z.of_nat counts)).
  { apply Forall_map; eapply Forall_impl; [|exact COUNTS]; intros count [_ RANGE]; split; [lia|exact RANGE]. }
  assert (NONNEGATIVE : Forall (fun count => 0 <= count) (map Z.of_nat counts)).
  { apply Forall_forall; intros count MEMBER; rewrite Forall_forall in RANGES; exact (proj1 (RANGES count MEMBER)). }
  set (initialized := PTree.set (mtas_flag allocation) (memory_boolean_word true) current).
  assert (INIT_FRAME : temp_agree ports current initialized) by (apply temp_agree_set; exact FLAG_PUBLIC).
  destruct (@multi_tensor_affine_scan_execution dimensions sizes original initialized memory
    (mtas_left allocation) (mtas_right allocation) (memory_nest_bounds nest) scalars (map Z.of_nat counts) values
    (mtas_flag allocation) accesses (statement_temps source++live) fe ge locals true
    LAYOUT DIMENSIONS UNIQUE FRESH FLAG_PUBLIC RANGES
    ltac:(rewrite length_map; rewrite mtas_left_length; exact (eq_sym LENGTH))
    ltac:(rewrite length_map; rewrite mtas_right_length; exact (eq_sym LENGTH))
    BOUNDS SCALARS ltac:(eapply multi_tensor_affine_source_point_receipts; exact MODEL_Z)
    ltac:(eapply temp_agree_trans; [exact FRAME|exact INIT_FRAME]) ltac:(apply PTree.gss))
    as [checked [SCAN [SCAN_FRAME RESULT]]].
  rewrite andb_true_l in RESULT.
  exists sizes,checked; split.
  - unfold multi_tensor_affine_package_guard; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + constructor; constructor.
    + exact SCAN.
  - assert (PUBLIC_EXIT : temp_agree ports current checked) by (eapply temp_agree_trans; eassumption).
    split.
    + eapply temp_agree_weaken; [|exact PUBLIC_EXIT]; intros id MEMBER.
      unfold ports,multi_tensor_affine_package_ports,multi_tensor_affine_scan_public;
        repeat rewrite in_app_iff in *; tauto.
    + split; [exact PUBLIC_EXIT|split; [exact LAYOUT|split; [exact DIMENSIONS|split; [exact MODEL|split; [exact RESULT|]]]]].
      intro ACCEPT; rewrite RESULT in ACCEPT.
      assert (CHECK : multi_tensor_affine_scan_check (multi_tensor_locations original sizes)
        accesses values (map Z.of_nat counts) = true).
      { destruct (multi_tensor_affine_scan_check (multi_tensor_locations original sizes) accesses values (map Z.of_nat counts));
          [reflexivity|discriminate]. }
      eapply multi_tensor_affine_scan_footprint_separation with (ge:=ge) (locals:=locals);
        [exact LAYOUT|exact DIMENSIONS|exact NONNEGATIVE|exact MODEL_Z|exact CHECK].
Qed.
End SOURCE_SCAN.

Print Assumptions multi_tensor_affine_package_source_scan.
