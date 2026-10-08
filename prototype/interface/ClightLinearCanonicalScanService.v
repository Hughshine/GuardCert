(** The domain establishes canonical coverage for templates with the same
    loop coefficients. The language service supplies safe execution, source
    observations and state transport; the shared factory supplies installation. *)
From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRecursiveSource GuardMemoryRecursiveDomain
  GuardMemoryMultiTensorSequence GuardMemoryMultiTensorBackend GuardMemoryMultiTensorAffineFootprint
  GuardMemoryFootprintRestriction GuardMemoryFiniteFootprint GuardMemoryDynamicTensorLayout
  GuardMemoryDynamicTensorBackend GuardMemoryCanonicalAlias GuardMemoryCanonicalRange
  GuardMemoryBooleanScan GuardMemoryAccessTemplateDedup GuardMemoryLinearCanonicalAlias.
From GuardInterface Require Import ClightSourceLicensedScan ClightMultiTensorDataPackage
  ClightMultiTensorScanAllocation ClightMultiTensorAffinePackageScan ClightCanonicalScanAllocation ClightCanonicalPackageScan
  ClightMultiTensorScanService ClightCanonicalSourceInputs.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition linear_canonical_package_eligible source (package : multi_tensor_region_package source) :=
  linear_alias_templates_check (length (memory_nest_iterators (mtr_nest package)))
    (multi_tensor_instruction_templates (map mt_instruction (mtr_items package))) &&
  (2*mtr_cap (mtr_description package)-1<=?Int.max_signed).

Definition linear_canonical_package_guard source (package : multi_tensor_region_package source)
    public pool (allocation : canonical_scan_allocation source
      (multi_tensor_affine_package_ports package public) pool (length (memory_nest_iterators (mtr_nest package))))
    selected :=
  if linear_canonical_package_eligible package then
    canonical_selected_package_scan package public allocation selected
  else canonical_package_guard package public allocation.

Theorem linear_canonical_package_includes_strict source (package : multi_tensor_region_package source) :
  canonical_package_eligible package=true -> linear_canonical_package_eligible package=true.
Proof.
  unfold canonical_package_eligible,linear_canonical_package_eligible.
  rewrite !andb_true_iff; intros [TEMPLATES CAP]; split; [|exact CAP].
  apply linear_alias_templates_include_strict; exact TEMPLATES.
Qed.

Section LINEAR.
Variable source : statement.
Variable package : multi_tensor_region_package source.
Variable public : list ident.
Variable pool : list (ident * type).
Let dimensions := mtr_dimensions (mtr_description package).
Let nest := mtr_nest package.
Let scalars := mtr_scalars (mtr_description package).
Let instructions := map mt_instruction (mtr_items package).
Let accesses := multi_tensor_instruction_templates instructions.
Let ports := multi_tensor_affine_package_ports package public.
Variable allocation : canonical_scan_allocation source ports pool (length (memory_nest_iterators nest)).
Variable selected : list AccessFunction.
Hypothesis EQUIVALENT : access_templates_equivalent selected accesses.

Theorem linear_canonical_scan_service_execution fe ge locals original current memory source_after final :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  multi_tensor_scan_ready package (Entry ge locals original memory) -> temp_agree ports original current ->
  exists checked answer,
    exec_stmt fe ge locals current memory (linear_canonical_package_guard package public allocation selected)
      E0 checked memory Out_normal /\
    temp_agree (statement_temps source++public) current checked /\ temp_agree ports current checked /\
    checked!(mtas_flag allocation)=Some (memory_boolean_word answer) /\
    (answer=true -> multi_tensor_scan_entry_fact package (Entry ge locals original memory)).
Proof.
  intros SOURCE SETUP FRAME; unfold linear_canonical_package_guard.
  destruct (linear_canonical_package_eligible package) eqn:ELIGIBLE.
  2: exact (@canonical_scan_service_execution source package public pool allocation
    fe ge locals original current memory source_after final SOURCE SETUP FRAME).
  unfold linear_canonical_package_eligible in ELIGIBLE; apply andb_true_iff in ELIGIBLE as [TEMPLATES CAP].
  apply Z.leb_le in CAP.
  destruct (@canonical_source_scan_execution source package public pool allocation selected EQUIVALENT
    fe ge locals original current memory source_after final CAP SOURCE SETUP FRAME)
    as [sizes [checked (RUN & PUBLIC & PORTS & OBSERVE & LAYOUT & DIMENSIONS & LENGTH & RANGES & MODEL & FLAG)]].
  set (counts := map Z.of_nat (memory_recursive_counts (memory_nest_bounds nest) original)).
  set (values := memory_recursive_parameters scalars original).
  assert (NONNEG : Forall (fun count => 0<=count) counts).
  { eapply Forall_impl; [|exact RANGES]; intros count [NONNEG _]; exact NONNEG. }
  assert (MATCHING : linear_alias_templates_check (length counts) accesses=true).
  { unfold counts,nest; rewrite length_map,LENGTH; exact TEMPLATES. }
  pose proof (@linear_alias_source_exact counts values instructions sizes original memory final
    NONNEG MATCHING MODEL) as EXACT.
  fold accesses in EXACT.
  change (checked!(mtas_flag allocation)=Some (memory_boolean_word
    (canonical_alias_check (multi_tensor_locations original sizes) accesses values counts))) in FLAG.
  rewrite EXACT in FLAG.
  exists checked,(multi_tensor_affine_scan_check (multi_tensor_locations original sizes) accesses values counts).
  split; [exact RUN|split; [exact PUBLIC|split; [exact PORTS|split; [exact FLAG|]]]].
  intro ACCEPT; exists sizes; split; [exact OBSERVE|].
  eapply multi_tensor_affine_scan_footprint_separation with (ge:=ge) (locals:=locals);
    [exact LAYOUT|exact DIMENSIONS|exact NONNEG|exact MODEL|exact ACCEPT].
Qed.

Definition linear_canonical_prepared_scan : multi_tensor_prepared_scan package public :=
  {| prepared_scan_condition :=
      {| licensed_scan_statement:=linear_canonical_package_guard package public allocation selected;
         licensed_scan_result:=mtas_flag allocation;
         licensed_scan_execution:=linear_canonical_scan_service_execution |};
     prepared_scan_candidate_pool:=multi_tensor_scan_candidate_pool allocation |}.
End LINEAR.

Definition linear_canonical_scan_builder : multi_tensor_scan_builder := fun source package public pool =>
  match canonical_package_allocate package public pool with
  | Some allocation=>Some (@linear_canonical_prepared_scan source package public pool allocation
      (deduplicate_access_templates (multi_tensor_instruction_templates (map mt_instruction (mtr_items package))))
      (deduplicate_access_templates_membership (multi_tensor_instruction_templates (map mt_instruction (mtr_items package)))))
  | None=>None end.

Print Assumptions linear_canonical_package_includes_strict.
Print Assumptions linear_canonical_scan_service_execution.
Print Assumptions linear_canonical_prepared_scan.
Print Assumptions linear_canonical_scan_builder.
