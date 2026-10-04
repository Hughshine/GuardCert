From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Integers.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryPointerBackend GuardMemoryRuntime GuardMemoryRecursiveSource GuardMemoryRecursiveDomain
  GuardMemoryScalarPointerBounds GuardMemoryScalarLoops GuardMemoryStartedScalarLoop GuardMemoryStartedPointerBounds GuardMemoryParamPointerProjectedCandidate.
From GuardMemory Require Import GuardMemoryWindowSyntax GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowPackageHeader GuardMemoryWindowStaticBounds.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition window_package_context source (package : window_started_package source) :=
  memory_nest_bounds (window_region_nest (window_started_base package))++
  window_region_parameters (window_started_base package)++window_region_scalars (window_started_base package)++
  [window_started_iterator package].
Definition window_package_loop source (package : window_started_package source) :=
  memory_started_scalar_loop (length (memory_nest_iterators (window_region_nest (window_started_base package))))
    (length (window_region_parameters (window_started_base package)++window_region_scalars (window_started_base package)))
    (window_region_instructions (window_started_base package)).
Definition window_package_static_bounds source (package : window_started_package source) :=
  window_static_base_bounds (window_region_caps (window_started_base package))
    (window_region_parameter_bounds (window_started_base package)) (length (window_region_scalars (window_started_base package)))++
  [MemoryNested.A.Interval (window_region_root_lower (window_started_base package)) (hd 1 (window_region_caps (window_started_base package))-1)].
Definition window_package_pointer_bounds source (package : window_started_package source) :=
  window_pointer_static_base_bounds (window_region_caps (window_started_base package))
    (window_region_parameter_bounds (window_started_base package)) (length (window_region_scalars (window_started_base package)))++
  [MemoryFramedNested.N.A.Interval (window_region_root_lower (window_started_base package)) (hd 1 (window_region_caps (window_started_base package))-1)].
Theorem window_package_validator_within source (package : window_started_package source) s :
  window_package_header_domain package s -> window_package_header_accept package s = true ->
  MemoryNested.A.env_within (window_package_static_bounds package)
    (memory_recursive_parameters (window_package_context package) (entry_temps s)).
Proof.
  intros DOMAIN ACCEPT; destruct (window_package_header_sound DOMAIN ACCEPT) as [ACTIVE [ROOT [RANGES PARAM_RANGES]]].
  pose proof (window_region_certificate (window_started_base package)) as CERT.
  assert (BASE : MemoryNested.A.env_within
    (window_static_base_bounds (window_region_caps (window_started_base package))
      (window_region_parameter_bounds (window_started_base package)) (length (window_region_scalars (window_started_base package))))
    (memory_recursive_parameters (memory_nest_bounds (window_region_nest (window_started_base package))) (entry_temps s)++
      memory_recursive_parameters (window_region_parameters (window_started_base package)) (entry_temps s)++
      memory_recursive_parameters (window_region_scalars (window_started_base package)) (entry_temps s))).
  { pose proof (@window_validator_count_parameter_scalar_ranges _ _ _ _ _ (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s)
      RANGES PARAM_RANGES (memory_recursive_scalar_values_range (window_region_scalars (window_started_base package)) (entry_temps s))) as WITHIN.
    unfold memory_recursive_parameters in WITHIN; rewrite length_map in WITHIN; exact WITHIN. }
  unfold window_package_static_bounds,window_package_context,memory_recursive_parameters; rewrite !map_app; cbn [map].
  rewrite !app_assoc; apply memory_started_validator_within_append.
  - unfold window_static_base_bounds; rewrite !length_app,!length_map,repeat_length.
    rewrite (window_source_caps_length CERT),(window_source_parameters_length CERT),memory_nest_lengths; lia.
  - unfold memory_recursive_parameters in BASE; repeat rewrite app_assoc in BASE; exact BASE.
  - apply MemoryNested.A.env_within_cons; [unfold MemoryNested.A.contains; cbn; lia|].
    intros index interval ABSENT; rewrite nth_error_nil in ABSENT; discriminate.
Qed.
Print Assumptions window_package_validator_within.
Theorem window_package_encoder_within source (package : window_started_package source) s :
  window_package_header_domain package s -> window_package_header_accept package s = true ->
  MemoryFramedNested.N.A.env_within (window_package_pointer_bounds package)
    (memory_recursive_parameters (window_package_context package) (entry_temps s)).
Proof.
  intros DOMAIN ACCEPT; destruct (window_package_header_sound DOMAIN ACCEPT) as [ACTIVE [ROOT [RANGES PARAM_RANGES]]].
  pose proof (window_region_certificate (window_started_base package)) as CERT.
  assert (BASE : MemoryFramedNested.N.A.env_within
    (window_pointer_static_base_bounds (window_region_caps (window_started_base package))
      (window_region_parameter_bounds (window_started_base package)) (length (window_region_scalars (window_started_base package))))
    (memory_recursive_parameters (memory_nest_bounds (window_region_nest (window_started_base package))) (entry_temps s)++
      memory_recursive_parameters (window_region_parameters (window_started_base package)) (entry_temps s)++
      memory_recursive_parameters (window_region_scalars (window_started_base package)) (entry_temps s))).
  { pose proof (@window_encoder_count_parameter_scalar_ranges _ _ _ _ _ (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s)
      RANGES PARAM_RANGES (memory_recursive_scalar_values_range (window_region_scalars (window_started_base package)) (entry_temps s))) as WITHIN.
    unfold memory_recursive_parameters in WITHIN; rewrite length_map in WITHIN; exact WITHIN. }
  unfold window_package_pointer_bounds,window_package_context,memory_recursive_parameters; rewrite !map_app; cbn [map].
  rewrite !app_assoc; apply memory_started_encoder_within_append.
  - unfold window_pointer_static_base_bounds; rewrite !length_app,!length_map,repeat_length.
    rewrite (window_source_caps_length CERT),(window_source_parameters_length CERT),memory_nest_lengths; lia.
  - unfold memory_recursive_parameters in BASE; repeat rewrite app_assoc in BASE; exact BASE.
  - apply MemoryFramedNested.N.A.env_within_cons; [unfold MemoryFramedNested.N.A.contains; cbn; lia|].
    intros index interval ABSENT; rewrite nth_error_nil in ABSENT; discriminate.
Qed.

Print Assumptions window_package_encoder_within.
