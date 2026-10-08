(** A third service uses the existing language scan and checked allocator.
    Any membership-preserving template processor can use this adapter. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryScalarLoops
  GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryFiniteFootprint GuardMemoryFootprintRestriction
  GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend GuardMemoryMultiTensorBackend
  GuardMemoryMultiTensorSequence GuardMemoryMultiTensorSourceCapabilities GuardMemoryMultiTensorSourceRegion GuardMemoryMultiTensorAffineFootprint
  GuardMemoryMultiTensorAffineScan GuardMemoryCanonicalAlias GuardMemoryCanonicalPrepare
  GuardMemoryCanonicalTests GuardMemoryCanonicalScan GuardMemoryCanonicalRange GuardMemoryBooleanScan
  GuardMemoryAccessTemplateDedup.
From GuardInterface Require Import ClightSourceLicensedScan ClightMultiTensorDataPackage
  ClightTensorBackendGuard ClightMultiTensorPackageExecution ClightMultiTensorScanAllocation
  ClightMultiTensorAffinePackageScan ClightCanonicalScanAllocation ClightCanonicalPackageScan
  ClightMultiTensorScanService.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition processed_template_package_guard source (package : multi_tensor_region_package source)
    public pool (allocation : canonical_scan_allocation source
      (multi_tensor_affine_package_ports package public) pool (length (memory_nest_iterators (mtr_nest package))))
    accesses :=
  if canonical_package_eligible package then
    Ssequence (Sset (mtas_flag allocation) (Econst_int Int.one type_int32s))
      (canonical_affine_scan_statement (mtr_dimensions (mtr_description package))
        (mcas_positions allocation) (mcas_limits allocation) (mcas_left allocation) (mcas_right allocation)
        (memory_nest_bounds (mtr_nest package)) (mtr_scalars (mtr_description package))
        (mtas_flag allocation) accesses)
  else canonical_package_guard package public allocation.

Section PROCESSED.
Variable source : statement.
Variable package : multi_tensor_region_package source.
Variable public : list ident.
Variable pool : list (ident * type).
Let dimensions := mtr_dimensions (mtr_description package).
Let nest := mtr_nest package.
Let scalars := mtr_scalars (mtr_description package).
Let items := mtr_items package.
Let instructions := map mt_instruction items.
Let accesses := multi_tensor_instruction_templates instructions.
Let ports := multi_tensor_affine_package_ports package public.
Variable allocation : canonical_scan_allocation source ports pool (length (memory_nest_iterators nest)).
Variable selected : list AccessFunction.
Hypothesis EQUIVALENT : access_templates_equivalent selected accesses.

Theorem processed_template_service_execution fe ge locals original current memory source_after final :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  multi_tensor_scan_ready package (Entry ge locals original memory) -> temp_agree ports original current ->
  exists checked answer,
    exec_stmt fe ge locals current memory (processed_template_package_guard package public allocation selected)
      E0 checked memory Out_normal /\
    temp_agree (statement_temps source++public) current checked /\ temp_agree ports current checked /\
    checked!(mtas_flag allocation)=Some (memory_boolean_word answer) /\
    (answer=true -> multi_tensor_scan_entry_fact package (Entry ge locals original memory)).
Proof.
  intros SOURCE SETUP FRAME; unfold processed_template_package_guard.
  destruct (canonical_package_eligible package) eqn:ELIGIBLE.
  2: exact (@canonical_scan_service_execution source package public pool allocation
    fe ge locals original current memory source_after final SOURCE SETUP FRAME).
  unfold canonical_package_eligible in ELIGIBLE; apply andb_true_iff in ELIGIBLE as [TEMPLATES CAP].
  apply Z.leb_le in CAP.
  set (counts := memory_recursive_counts (memory_nest_bounds nest) original).
  set (values := memory_recursive_parameters scalars original).
  destruct (@multi_tensor_package_setup_accept source package fe ge locals original memory source_after final SOURCE SETUP)
    as [sizes (LENGTH & COUNTS & BOUNDS & INITIAL & SCALARS & SIGNED & OBSERVE & BACKEND & BOX & WITHIN)].
  pose proof (@tensor_backend_guard_accepts (Entry ge locals original memory) dimensions sizes OBSERVE BACKEND) as LAYOUT.
  destruct (@tensor_observe_dimensions_sound dimensions original sizes OBSERVE) as [DIMENSIONS _].
  assert (MODEL : L.loop_semantics
    (memory_scalar_rectangle 0 (length (map Z.of_nat counts)) (length values) instructions)
    (map Z.of_nat counts++values) (RuntimeState (multi_tensor_locations original sizes) memory)
      (RuntimeState (multi_tensor_locations original sizes) final)).
  { rewrite length_map.
    destruct (@multi_tensor_source_region_decode dimensions nest scalars (multi_tensor_body_pointers items)
      items fe ge locals counts values sizes original memory source_after final
      (mtr_body package) (mtr_shapes package) (mtr_fresh package) (mtr_unique package)
      (mtr_protected package) LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS
      (multi_tensor_body_pointers_check items) BOX) as [MODEL _]; [|exact MODEL].
    eapply multi_tensor_region_source_execution; exact SOURCE. }
  assert (RANGES : Forall canonical_count_range (map Z.of_nat counts)).
  { apply (@canonical_static_bounds_ranges (mtr_cap (mtr_description package)) (map Z.of_nat counts) values);
      [exact CAP|rewrite length_map; exact WITHIN]. }
  assert (NONNEG : Forall (fun count => 0<=count) (map Z.of_nat counts)).
  { eapply Forall_impl; [|exact RANGES]; intros count [NONNEG _]; exact NONNEG. }
  set (scan_ports := memory_nest_bounds nest++canonical_affine_read_ports dimensions scalars selected++
    (statement_temps source++public)).
  assert (PORT_MEMBER : forall id, In id scan_ports <-> In id ports).
  { intro id; unfold scan_ports,ports,multi_tensor_affine_package_ports,
      canonical_affine_read_ports,multi_tensor_affine_scan_public.
    repeat rewrite app_nil_r; repeat rewrite in_app_iff; rewrite (@access_template_map_membership ident
      (@fst ident AffineFunction) selected accesses EQUIVALENT id); tauto. }
  assert (PRIVATE : forall id, In id (mcas_private allocation) -> ~ In id scan_ports).
  { intros id MEMBER PUBLIC; eapply canonical_scan_allocation_fresh
      with (allocation:=allocation) (identifier:=id);
      [apply in_or_app; right; apply (PORT_MEMBER id); exact PUBLIC|exact MEMBER]. }
  destruct (canonical_scan_lengths allocation) as [POS_LENGTH [LIM_LENGTH [LEFT_LENGTH RIGHT_LENGTH]]].
  destruct (canonical_scan_groups allocation) as
    [POS_UNIQUE [LIM_UNIQUE [COORD_UNIQUE [POS_PRIVATE [LIM_FLAG [COORD_PRIVATE FLAG_PRIVATE]]]]]].
  assert (FLAG_FRESH : ~ In (mtas_flag allocation) scan_ports).
  { apply PRIVATE; unfold mcas_private; repeat rewrite in_app_iff; cbn; tauto. }
  assert (POS_FRESH : forall id, In id (mcas_positions allocation) ->
    ~ In id (mcas_limits allocation++scan_ports) /\ id<>mtas_flag allocation).
  { intros id MEMBER; split.
    - intro BAD; apply in_app_iff in BAD as [BAD|BAD].
      + apply (POS_PRIVATE id MEMBER); apply in_or_app; left; exact BAD.
      + apply (PRIVATE id); [unfold mcas_private; repeat rewrite in_app_iff; tauto|exact BAD].
    - intro SAME; subst; apply (POS_PRIVATE _ MEMBER); apply in_or_app; right; cbn; auto. }
  assert (LIM_FRESH : forall id, In id (mcas_limits allocation) -> ~ In id (scan_ports++[mtas_flag allocation])).
  { intros id MEMBER BAD; apply in_app_iff in BAD as [BAD|BAD].
    - apply (PRIVATE id); [unfold mcas_private; repeat rewrite in_app_iff; tauto|exact BAD].
    - cbn in BAD; destruct BAD as [SAME|[]]; apply (LIM_FLAG id MEMBER); symmetry; exact SAME. }
  assert (COORD_FRESH : forall id, In id (mcas_left allocation++mcas_right allocation) ->
    ~ In id (mcas_positions allocation++mcas_limits allocation++scan_ports++[mtas_flag allocation])).
  { intros id MEMBER BAD; repeat rewrite in_app_iff in BAD; destruct BAD as [BAD|[BAD|[BAD|BAD]]].
    - apply (COORD_PRIVATE id MEMBER); repeat rewrite in_app_iff; tauto.
    - apply (COORD_PRIVATE id MEMBER); repeat rewrite in_app_iff; tauto.
    - apply (PRIVATE id); [unfold mcas_private; repeat rewrite in_app_iff in *; tauto|exact BAD].
    - apply (COORD_PRIVATE id MEMBER); repeat rewrite in_app_iff; tauto. }
  set (initialized := PTree.set (mtas_flag allocation) (memory_boolean_word true) current).
  assert (INIT_FRAME : temp_agree scan_ports current initialized) by (apply temp_agree_set; exact FLAG_FRESH).
  assert (ORIGINAL_FRAME : temp_agree scan_ports original current).
  { eapply temp_agree_weaken; [|exact FRAME]; intros id MEMBER; apply PORT_MEMBER; exact MEMBER. }
  destruct (@canonical_affine_scan_execution dimensions sizes original initialized memory
    (mcas_positions allocation) (mcas_limits allocation) (mcas_left allocation) (mcas_right allocation)
    (memory_nest_bounds nest) scalars (map Z.of_nat counts) values (mtas_flag allocation) selected
    (statement_temps source++public) fe ge locals true
    LAYOUT DIMENSIONS POS_UNIQUE LIM_UNIQUE COORD_UNIQUE POS_FRESH
    ltac:(intros id MEMBER BAD; apply (LIM_FRESH id MEMBER);
      unfold scan_ports; repeat rewrite in_app_iff in *; tauto)
    ltac:(intros id MEMBER BAD; apply (COORD_FRESH id MEMBER);
      unfold scan_ports; repeat rewrite in_app_iff in *; tauto)
    FLAG_FRESH
    ltac:(rewrite length_map,POS_LENGTH; symmetry; exact LENGTH)
    ltac:(rewrite length_map,LIM_LENGTH; symmetry; exact LENGTH)
    ltac:(rewrite length_map,LEFT_LENGTH; symmetry; exact LENGTH)
    ltac:(rewrite length_map,RIGHT_LENGTH; symmetry; exact LENGTH)
    RANGES BOUNDS SCALARS
    ltac:(intros point access POINT MEMBER; eapply multi_tensor_affine_source_point_receipts;
      [exact MODEL|exact POINT|apply EQUIVALENT; exact MEMBER])
    ltac:(eapply temp_agree_trans; [exact ORIGINAL_FRAME|exact INIT_FRAME]) ltac:(apply PTree.gss))
    as [checked [SCAN [SCAN_FRAME RESULT]]].
  rewrite andb_true_l,(@access_template_canonical_check_exact (multi_tensor_locations original sizes)
    selected accesses values (map Z.of_nat counts) EQUIVALENT) in RESULT.
  pose proof (@canonical_alias_source_exact (map Z.of_nat counts) values instructions sizes original memory final
    NONNEG TEMPLATES MODEL) as EXACT.
  fold accesses in EXACT; rewrite EXACT in RESULT.
  exists checked,(multi_tensor_affine_scan_check (multi_tensor_locations original sizes) accesses values
    (map Z.of_nat counts)); split.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|exact SCAN].
  - assert (EXIT : temp_agree ports current checked).
    { eapply temp_agree_weaken; [|eapply temp_agree_trans; [exact INIT_FRAME|exact SCAN_FRAME]];
        intros id MEMBER; apply PORT_MEMBER; exact MEMBER. }
    split.
    + eapply temp_agree_weaken; [|exact EXIT]; intros id MEMBER;
        unfold ports,multi_tensor_affine_package_ports,multi_tensor_affine_scan_public;
        repeat rewrite in_app_iff in *; tauto.
    + split; [exact EXIT|split; [exact RESULT|]].
      intro ACCEPT; exists sizes; split; [exact OBSERVE|].
      eapply multi_tensor_affine_scan_footprint_separation with (ge:=ge) (locals:=locals);
        [exact LAYOUT|exact DIMENSIONS|exact NONNEG|exact MODEL|exact ACCEPT].
Qed.

Definition processed_template_prepared_scan : multi_tensor_prepared_scan package public :=
  {| prepared_scan_condition :=
      {| licensed_scan_statement:=processed_template_package_guard package public allocation selected;
         licensed_scan_result:=mtas_flag allocation;
         licensed_scan_execution:=processed_template_service_execution |};
     prepared_scan_candidate_pool:=multi_tensor_scan_candidate_pool allocation |}.
End PROCESSED.

Definition deduplicated_scan_builder : multi_tensor_scan_builder := fun source package public pool =>
  match canonical_package_allocate package public pool with
  | Some allocation=>Some (@processed_template_prepared_scan source package public pool allocation
      (deduplicate_access_templates (multi_tensor_instruction_templates (map mt_instruction (mtr_items package))))
      (deduplicate_access_templates_membership (multi_tensor_instruction_templates (map mt_instruction (mtr_items package)))))
  | None=>None end.

Print Assumptions processed_template_service_execution.
Print Assumptions processed_template_prepared_scan.
Print Assumptions deduplicated_scan_builder.
