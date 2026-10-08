From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryScalarLoops
  GuardMemoryScalarChecker GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction
  GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryDynamicTensorLayout
  GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend GuardMemoryMultiTensorSequence
  GuardMemoryMultiTensorSourceCapabilities GuardMemoryMultiTensorSourceRegion GuardMemoryBooleanScan GuardMemoryMultiTensorAffineFootprint
  GuardMemoryMultiTensorAffineScan GuardMemoryCanonicalAlias GuardMemoryCanonicalPrepare
  GuardMemoryCanonicalTests GuardMemoryCanonicalScan GuardMemoryCanonicalRange.
From GuardInterface Require Import ClightTensorBackendGuard ClightMultiTensorDataPackage
  ClightMultiTensorPackageExecution ClightMultiTensorScanAllocation ClightMultiTensorAffinePackageScan ClightCanonicalScanAllocation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition canonical_package_eligible source (package : multi_tensor_region_package source) :=
  canonical_alias_templates_check (multi_tensor_instruction_templates (map mt_instruction (mtr_items package))) &&
    (2*mtr_cap (mtr_description package)-1 <=? Int.max_signed).
Definition canonical_package_allocate source (package : multi_tensor_region_package source) live pool :=
  allocate_canonical_scan source (multi_tensor_affine_package_ports package live) pool
    (length (memory_nest_iterators (mtr_nest package))).
Definition canonical_package_guard source (package : multi_tensor_region_package source) live pool
    (allocation : canonical_scan_allocation source (multi_tensor_affine_package_ports package live) pool
      (length (memory_nest_iterators (mtr_nest package)))) :=
  if canonical_package_eligible package then
    Ssequence (Sset (mtas_flag allocation) (Econst_int Int.one type_int32s))
      (canonical_affine_scan_statement (mtr_dimensions (mtr_description package))
        (mcas_positions allocation) (mcas_limits allocation) (mcas_left allocation) (mcas_right allocation)
        (memory_nest_bounds (mtr_nest package)) (mtr_scalars (mtr_description package)) (mtas_flag allocation)
        (multi_tensor_instruction_templates (map mt_instruction (mtr_items package))))
  else multi_tensor_affine_package_guard package live (canonical_scan_fallback_allocation allocation).

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
Variable allocation : canonical_scan_allocation source ports pool (length (memory_nest_iterators nest)).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.

(** The factory transports existing source/setup evidence to the real encoder.
    Eligible and old scans expose the same original Boolean specification. *)
Theorem canonical_package_source_scan ge locals original current memory source_after final :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  decision_run (Entry ge locals original memory) (multi_tensor_package_setup_guard package) true ->
  temp_agree ports original current ->
  let counts := memory_recursive_counts (memory_nest_bounds nest) original in
  let values := memory_recursive_parameters scalars original in
  exists sizes checked,
    exec_stmt fe ge locals current memory (canonical_package_guard package live allocation)
      E0 checked memory Out_normal /\
    temp_agree (statement_temps source++live) current checked /\ temp_agree ports current checked /\
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
  unfold canonical_package_guard; destruct (canonical_package_eligible package) eqn:ELIGIBLE.
  2: exact (@multi_tensor_affine_package_source_scan source package live pool
    (canonical_scan_fallback_allocation allocation) fe ge locals original current memory source_after final
    SOURCE SETUP FRAME).
  unfold canonical_package_eligible in ELIGIBLE; apply andb_true_iff in ELIGIBLE as [TEMPLATES CAP].
  apply Z.leb_le in CAP.
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
  assert (RANGES : Forall canonical_count_range (map Z.of_nat counts)).
  { apply (@canonical_static_bounds_ranges (mtr_cap (mtr_description package)) (map Z.of_nat counts) values);
      [exact CAP|rewrite length_map; exact WITHIN]. }
  assert (NONNEG : Forall (fun count => 0 <= count) (map Z.of_nat counts)).
  { eapply Forall_impl; [|exact RANGES]; intros count [NONNEG _]; exact NONNEG. }
  assert (PORTS : ports = memory_nest_bounds nest++canonical_affine_read_ports dimensions scalars accesses++
    (statement_temps source++live)).
  { unfold ports,multi_tensor_affine_package_ports,canonical_affine_read_ports,multi_tensor_affine_scan_public;
      repeat rewrite app_nil_r; repeat rewrite app_assoc; reflexivity. }
  assert (PORT_MEMBER : forall id, In id ports <->
    In id (memory_nest_bounds nest) \/ In id (canonical_affine_read_ports dimensions scalars accesses) \/
    In id (statement_temps source) \/ In id live).
  { intro id; rewrite PORTS; repeat rewrite in_app_iff; tauto. }
  destruct (canonical_scan_lengths allocation) as [POS_LENGTH [LIM_LENGTH [LEFT_LENGTH RIGHT_LENGTH]]].
  destruct (canonical_scan_groups allocation) as
    [POS_UNIQUE [LIM_UNIQUE [COORD_UNIQUE [POS_PRIVATE [LIM_FLAG [COORD_PRIVATE FLAG_PRIVATE]]]]]].
  assert (PRIVATE : forall id, In id (mcas_private allocation) -> ~ In id ports).
  { intros id MEMBER PUBLIC; eapply canonical_scan_allocation_fresh;
      [apply in_or_app; right; exact PUBLIC|exact MEMBER]. }
  assert (POS_FRESH : forall id, In id (mcas_positions allocation) ->
    ~ In id (mcas_limits allocation++ports) /\ id <> mtas_flag allocation).
  { intros id MEMBER; split.
    - intro BAD; apply in_app_iff in BAD as [BAD|BAD].
      + apply (POS_PRIVATE id MEMBER); apply in_or_app; left; exact BAD.
      + apply (PRIVATE id); [unfold mcas_private; apply in_or_app; left; exact MEMBER|exact BAD].
    - intro SAME; subst id; apply (POS_PRIVATE _ MEMBER); apply in_or_app; right; cbn; auto. }
  assert (LIM_FRESH : forall id, In id (mcas_limits allocation) -> ~ In id (ports++[mtas_flag allocation])).
  { intros id MEMBER BAD; apply in_app_iff in BAD as [BAD|BAD].
    - apply (PRIVATE id); [unfold mcas_private; apply in_or_app; right; apply in_or_app; left; exact MEMBER|exact BAD].
    - cbn in BAD; destruct BAD as [SAME|[]]; apply (LIM_FLAG id MEMBER); symmetry; exact SAME. }
  assert (COORD_FRESH : forall id, In id (mcas_left allocation++mcas_right allocation) ->
    ~ In id (mcas_positions allocation++mcas_limits allocation++ports++[mtas_flag allocation])).
  { intros id MEMBER BAD; repeat rewrite in_app_iff in BAD; destruct BAD as [BAD|[BAD|[BAD|BAD]]].
    - apply (COORD_PRIVATE id MEMBER); apply in_or_app; left; exact BAD.
    - apply (COORD_PRIVATE id MEMBER); apply in_or_app; right; apply in_or_app; left; exact BAD.
    - apply (PRIVATE id); [unfold mcas_private; repeat rewrite in_app_iff in *; tauto|exact BAD].
    - apply (COORD_PRIVATE id MEMBER); apply in_or_app; right; apply in_or_app; right; exact BAD. }
  assert (FLAG_PUBLIC : ~ In (mtas_flag allocation) ports).
  { apply (PRIVATE (mtas_flag allocation)); unfold mcas_private;
      repeat rewrite in_app_iff; cbn; tauto. }
  set (initialized := PTree.set (mtas_flag allocation) (memory_boolean_word true) current).
  assert (INIT_FRAME : temp_agree ports current initialized) by (apply temp_agree_set; exact FLAG_PUBLIC).
  destruct (@canonical_affine_scan_execution dimensions sizes original initialized memory
    (mcas_positions allocation) (mcas_limits allocation) (mcas_left allocation) (mcas_right allocation)
    (memory_nest_bounds nest) scalars (map Z.of_nat counts) values (mtas_flag allocation) accesses
    (statement_temps source++live) fe ge locals true
    LAYOUT DIMENSIONS POS_UNIQUE LIM_UNIQUE COORD_UNIQUE
    ltac:(rewrite <-PORTS; exact POS_FRESH)
    ltac:(intros id MEMBER BAD; apply (LIM_FRESH id MEMBER);
      pose proof (PORT_MEMBER id) as VIEW; repeat rewrite in_app_iff in BAD;
      repeat rewrite in_app_iff; tauto)
    ltac:(intros id MEMBER BAD; apply (COORD_FRESH id MEMBER);
      pose proof (PORT_MEMBER id) as VIEW; repeat rewrite in_app_iff in BAD;
      repeat rewrite in_app_iff; tauto)
    ltac:(rewrite <-PORTS; exact FLAG_PUBLIC)
    ltac:(rewrite length_map,POS_LENGTH; symmetry; exact LENGTH)
    ltac:(rewrite length_map,LIM_LENGTH; symmetry; exact LENGTH)
    ltac:(rewrite length_map,LEFT_LENGTH; symmetry; exact LENGTH)
    ltac:(rewrite length_map,RIGHT_LENGTH; symmetry; exact LENGTH)
    RANGES BOUNDS SCALARS ltac:(eapply multi_tensor_affine_source_point_receipts; exact MODEL_Z)
    ltac:(rewrite <-PORTS; eapply temp_agree_trans; [exact FRAME|exact INIT_FRAME]) ltac:(apply PTree.gss))
    as [checked [SCAN [SCAN_FRAME RESULT]]].
  rewrite andb_true_l in RESULT.
  pose proof (@canonical_alias_source_exact (map Z.of_nat counts) values instructions sizes original memory final
    NONNEG TEMPLATES MODEL_Z) as EXACT.
  fold accesses in EXACT; rewrite EXACT in RESULT.
  rewrite <-PORTS in SCAN_FRAME.
  exists sizes,checked; split.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|exact SCAN].
  - assert (PUBLIC_EXIT : temp_agree ports current checked) by (eapply temp_agree_trans; eassumption).
    split.
    + eapply temp_agree_weaken; [|exact PUBLIC_EXIT]; intros id MEMBER.
      rewrite PORTS; repeat rewrite in_app_iff in *; tauto.
    + split; [exact PUBLIC_EXIT|split; [exact LAYOUT|split; [exact DIMENSIONS|split; [exact MODEL|split; [exact RESULT|]]]]].
      intro ACCEPT; rewrite RESULT in ACCEPT.
      assert (CHECK : multi_tensor_affine_scan_check (multi_tensor_locations original sizes) accesses values
        (map Z.of_nat counts)=true).
      { destruct (multi_tensor_affine_scan_check (multi_tensor_locations original sizes) accesses values
          (map Z.of_nat counts)); [reflexivity|discriminate]. }
      eapply multi_tensor_affine_scan_footprint_separation with (ge:=ge) (locals:=locals);
        [exact LAYOUT|exact DIMENSIONS|exact NONNEG|exact MODEL_Z|exact CHECK].
Qed.
End SOURCE_SCAN.

Print Assumptions canonical_package_source_scan.
