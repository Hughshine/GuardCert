(** Prepared polyhedral scan services: the language boundary is shared, while
    allocators and derivations remain checked instance implementations. *)
From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRecursiveSource GuardMemoryRecursiveRestore
  GuardMemoryRecursiveDomain
  GuardMemoryMultiTensorBackend GuardMemoryMultiTensorAffineFootprint
  GuardMemoryBooleanScan GuardMemoryDynamicTensorLayout GuardMemoryDynamicTensorBackend
  GuardMemoryFootprintRestriction GuardMemoryFiniteFootprint GuardMemoryMultiTensorSequence.
From GuardInterface Require Import ClightSourceLicensedScan ClightMultiTensorDataPackage
  ClightTensorBackendGuard
  ClightMultiTensorCompleteGuard ClightMultiTensorAffinePackageScan
  ClightMultiTensorScanAllocation ClightMultiTensorAffineVersioned ClightMultiTensorPackageExecution
  ClightCanonicalScanAllocation ClightCanonicalPackageScan.
Import ListNotations.
Set Implicit Arguments.

Definition multi_tensor_scan_ready source (package : multi_tensor_region_package source) current :=
  decision_run current (multi_tensor_package_setup_guard package) true.
Definition multi_tensor_scan_entry_fact source (package : multi_tensor_region_package source) current :=
  exists sizes,
    tensor_observe_dimensions (mtr_dimensions (mtr_description package)) (entry_temps current)=Some sizes /\
    locations_nonalias (memory_restrict_locations (memory_footprint_allowed
      (multi_tensor_affine_source_footprint
        (map Z.of_nat (memory_recursive_counts (memory_nest_bounds (mtr_nest package)) (entry_temps current)))
        (memory_recursive_parameters (mtr_scalars (mtr_description package)) (entry_temps current))
        (map mt_instruction (mtr_items package))))
      (multi_tensor_locations (entry_temps current) sizes)).

Record multi_tensor_prepared_scan source (package : multi_tensor_region_package source) public : Type := {
  prepared_scan_condition : source_licensed_scan source
    (multi_tensor_affine_package_ports package public) public
    (multi_tensor_scan_ready package) (multi_tensor_scan_entry_fact package);
  prepared_scan_candidate_pool : list (ident * type)
}.
Definition multi_tensor_scan_builder := forall source (package : multi_tensor_region_package source)
  (public : list ident) (typed_pool : list (ident * type)), option (multi_tensor_prepared_scan package public).

Section PAIR.
Variable source : statement.
Variable package : multi_tensor_region_package source.
Variable public : list ident.
Variable typed_pool : list (ident * type).
Variable allocation : multi_tensor_scan_allocation source
  (multi_tensor_affine_package_ports package public) typed_pool
  (length (memory_nest_iterators (mtr_nest package))).

Lemma pair_scan_service_execution fe ge locals original current memory source_after final :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  multi_tensor_scan_ready package (Entry ge locals original memory) ->
  temp_agree (multi_tensor_affine_package_ports package public) original current ->
  exists checked answer,
    exec_stmt fe ge locals current memory (multi_tensor_affine_package_guard package public allocation)
      E0 checked memory Out_normal /\
    temp_agree (statement_temps source++public) current checked /\
    temp_agree (multi_tensor_affine_package_ports package public) current checked /\
    checked!(mtas_flag allocation)=Some (memory_boolean_word answer) /\
    (answer=true -> multi_tensor_scan_entry_fact package (Entry ge locals original memory)).
Proof.
  intros SOURCE READY FRAME.
  destruct (@multi_tensor_affine_package_source_scan source package public typed_pool allocation fe ge locals
    original current memory source_after final SOURCE READY FRAME)
    as [sizes [checked [RUN [PUBLIC [PORTS [LAYOUT [DIMENSIONS [MODEL [FLAG SOUND]]]]]]]]].
  exists checked, (multi_tensor_affine_scan_check (multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates (map mt_instruction (mtr_items package)))
    (memory_recursive_parameters (mtr_scalars (mtr_description package)) original)
    (map Z.of_nat (memory_recursive_counts (memory_nest_bounds (mtr_nest package)) original))).
  split; [exact RUN|split; [exact PUBLIC|split; [exact PORTS|split; [exact FLAG|]]]].
  intro ACCEPT; exists sizes; split.
  - apply multi_tensor_dimension_view_observation; [exact DIMENSIONS|].
    destruct (@tensor_layout_flag_sound sizes LAYOUT) as [POSITIVE [VOLUME _]].
    apply multi_tensor_positive_dimensions_signed; assumption.
  - apply SOUND; rewrite ACCEPT in FLAG; exact FLAG.
Qed.

Definition pair_prepared_scan : multi_tensor_prepared_scan package public :=
  {| prepared_scan_condition :=
      {| licensed_scan_statement:=multi_tensor_affine_package_guard package public allocation;
         licensed_scan_result:=mtas_flag allocation;
         licensed_scan_execution:=pair_scan_service_execution |};
     prepared_scan_candidate_pool:=multi_tensor_scan_candidate_pool allocation |}.
End PAIR.

Section CANONICAL.
Variable source : statement.
Variable package : multi_tensor_region_package source.
Variable public : list ident.
Variable typed_pool : list (ident * type).
Variable allocation : canonical_scan_allocation source
  (multi_tensor_affine_package_ports package public) typed_pool
  (length (memory_nest_iterators (mtr_nest package))).

Lemma canonical_scan_service_execution fe ge locals original current memory source_after final :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  multi_tensor_scan_ready package (Entry ge locals original memory) ->
  temp_agree (multi_tensor_affine_package_ports package public) original current ->
  exists checked answer,
    exec_stmt fe ge locals current memory (canonical_package_guard package public allocation)
      E0 checked memory Out_normal /\
    temp_agree (statement_temps source++public) current checked /\
    temp_agree (multi_tensor_affine_package_ports package public) current checked /\
    checked!(mtas_flag allocation)=Some (memory_boolean_word answer) /\
    (answer=true -> multi_tensor_scan_entry_fact package (Entry ge locals original memory)).
Proof.
  intros SOURCE READY FRAME.
  destruct (@canonical_package_source_scan source package public typed_pool allocation fe ge locals
    original current memory source_after final SOURCE READY FRAME)
    as [sizes [checked [RUN [PUBLIC [PORTS [LAYOUT [DIMENSIONS [MODEL [FLAG SOUND]]]]]]]]].
  exists checked, (multi_tensor_affine_scan_check (multi_tensor_locations original sizes)
    (multi_tensor_instruction_templates (map mt_instruction (mtr_items package)))
    (memory_recursive_parameters (mtr_scalars (mtr_description package)) original)
    (map Z.of_nat (memory_recursive_counts (memory_nest_bounds (mtr_nest package)) original))).
  split; [exact RUN|split; [exact PUBLIC|split; [exact PORTS|split; [exact FLAG|]]]].
  intro ACCEPT; exists sizes; split.
  - apply multi_tensor_dimension_view_observation; [exact DIMENSIONS|].
    destruct (@tensor_layout_flag_sound sizes LAYOUT) as [POSITIVE [VOLUME _]].
    apply multi_tensor_positive_dimensions_signed; assumption.
  - apply SOUND; rewrite ACCEPT in FLAG; exact FLAG.
Qed.

Definition canonical_prepared_scan : multi_tensor_prepared_scan package public :=
  {| prepared_scan_condition :=
      {| licensed_scan_statement:=canonical_package_guard package public allocation;
         licensed_scan_result:=mtas_flag allocation;
         licensed_scan_execution:=canonical_scan_service_execution |};
     prepared_scan_candidate_pool:=multi_tensor_scan_candidate_pool allocation |}.
End CANONICAL.

Definition pair_scan_builder : multi_tensor_scan_builder := fun source package public typed_pool =>
  match multi_tensor_affine_package_allocate package public typed_pool with
  | Some allocation=>Some (@pair_prepared_scan source package public typed_pool allocation)
  | None=>None end.
Definition canonical_scan_builder : multi_tensor_scan_builder := fun source package public typed_pool =>
  match canonical_package_allocate package public typed_pool with
  | Some allocation=>Some (@canonical_prepared_scan source package public typed_pool allocation)
  | None=>None end.

Print Assumptions pair_scan_service_execution.
Print Assumptions canonical_scan_service_execution.
Print Assumptions pair_scan_builder.
Print Assumptions canonical_scan_builder.
