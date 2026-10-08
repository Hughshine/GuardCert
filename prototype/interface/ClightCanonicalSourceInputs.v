(** Source-licensed canonical execution, independent of alias eligibility.
    The service supplies actual safe execution and the exact canonical Boolean;
    a domain client supplies the theorem making that Boolean sufficient. *)
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

Definition canonical_selected_package_scan source (package : multi_tensor_region_package source)
    public pool (allocation : canonical_scan_allocation source
      (multi_tensor_affine_package_ports package public) pool (length (memory_nest_iterators (mtr_nest package))))
    accesses :=
  Ssequence (Sset (mtas_flag allocation) (Econst_int Int.one type_int32s))
    (canonical_affine_scan_statement (mtr_dimensions (mtr_description package))
      (mcas_positions allocation) (mcas_limits allocation) (mcas_left allocation) (mcas_right allocation)
      (memory_nest_bounds (mtr_nest package)) (mtr_scalars (mtr_description package))
      (mtas_flag allocation) accesses).

Section INPUTS.
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

Let counts original := memory_recursive_counts (memory_nest_bounds nest) original.
Let values original := memory_recursive_parameters scalars original.

Theorem canonical_source_scan_execution fe ge locals original current memory source_after final :
  2*mtr_cap (mtr_description package)-1<=Int.max_signed ->
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  multi_tensor_scan_ready package (Entry ge locals original memory) -> temp_agree ports original current ->
  exists sizes checked,
    exec_stmt fe ge locals current memory (canonical_selected_package_scan package public allocation selected)
      E0 checked memory Out_normal /\
    temp_agree (statement_temps source++public) current checked /\ temp_agree ports current checked /\
    tensor_observe_dimensions dimensions original=Some sizes /\
    tensor_layout_flag sizes=true /\ tensor_dimension_view dimensions sizes original /\
    length (counts original)=length (memory_nest_iterators nest) /\
    Forall canonical_count_range (map Z.of_nat (counts original)) /\
    L.loop_semantics
      (memory_scalar_rectangle 0 (length (map Z.of_nat (counts original))) (length (values original)) instructions)
      (map Z.of_nat (counts original)++values original) (RuntimeState (multi_tensor_locations original sizes) memory)
        (RuntimeState (multi_tensor_locations original sizes) final) /\
    checked!(mtas_flag allocation)=Some (memory_boolean_word
      (canonical_alias_check (multi_tensor_locations original sizes) accesses (values original)
        (map Z.of_nat (counts original)))).
Proof.
  intros CAP SOURCE SETUP FRAME; unfold canonical_selected_package_scan.
  destruct (@multi_tensor_package_setup_accept source package fe ge locals original memory source_after final SOURCE SETUP)
    as [sizes (LENGTH & COUNTS & BOUNDS & INITIAL & SCALARS & SIGNED & OBSERVE & BACKEND & BOX & WITHIN)].
  pose proof (@tensor_backend_guard_accepts (Entry ge locals original memory) dimensions sizes OBSERVE BACKEND) as LAYOUT.
  destruct (@tensor_observe_dimensions_sound dimensions original sizes OBSERVE) as [DIMENSIONS _].
  assert (MODEL : L.loop_semantics
    (memory_scalar_rectangle 0 (length (map Z.of_nat (counts original))) (length (values original)) instructions)
    (map Z.of_nat (counts original)++(values original)) (RuntimeState (multi_tensor_locations original sizes) memory)
      (RuntimeState (multi_tensor_locations original sizes) final)).
  { rewrite length_map.
    destruct (@multi_tensor_source_region_decode dimensions nest scalars (multi_tensor_body_pointers items)
      items fe ge locals (counts original) (values original) sizes original memory source_after final
      (mtr_body package) (mtr_shapes package) (mtr_fresh package) (mtr_unique package)
      (mtr_protected package) LENGTH COUNTS BOUNDS INITIAL LAYOUT DIMENSIONS SCALARS
      (multi_tensor_body_pointers_check items) BOX) as [MODEL _]; [|exact MODEL].
    eapply multi_tensor_region_source_execution; exact SOURCE. }
  assert (RANGES : Forall canonical_count_range (map Z.of_nat (counts original))).
  { apply (@canonical_static_bounds_ranges (mtr_cap (mtr_description package)) (map Z.of_nat (counts original)) (values original));
      [exact CAP|rewrite length_map; exact WITHIN]. }
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
    (memory_nest_bounds nest) scalars (map Z.of_nat (counts original)) (values original) (mtas_flag allocation) selected
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
    selected accesses (values original) (map Z.of_nat (counts original)) EQUIVALENT) in RESULT.
  exists sizes,checked; split.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [constructor; constructor|exact SCAN].
  - assert (EXIT : temp_agree ports current checked).
    { eapply temp_agree_weaken; [|eapply temp_agree_trans; [exact INIT_FRAME|exact SCAN_FRAME]];
        intros id MEMBER; apply PORT_MEMBER; exact MEMBER. }
    split.
    + eapply temp_agree_weaken; [|exact EXIT]; intros id MEMBER;
        unfold ports,multi_tensor_affine_package_ports,multi_tensor_affine_scan_public;
        repeat rewrite in_app_iff in *; tauto.
    + split; [exact EXIT|split; [exact OBSERVE|split; [exact LAYOUT|split; [exact DIMENSIONS|]]]].
      split; [exact LENGTH|split; [exact RANGES|split; [exact MODEL|exact RESULT]]].
Qed.
End INPUTS.

Print Assumptions canonical_source_scan_execution.
