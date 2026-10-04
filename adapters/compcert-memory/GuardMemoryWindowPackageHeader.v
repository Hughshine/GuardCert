From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryVectorBounds.
From GuardMemory Require Import GuardMemoryIntervalBox GuardMemoryWindowSyntax GuardMemoryWindowPackage GuardMemoryWindowStartedPackage GuardMemoryWindowHeader GuardMemoryWindowParameterGuard GuardMemoryWindowSourceHeader.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition window_package_header_accept source (package : window_started_package source) s :=
  window_header_accept (window_region_root_lower (window_started_base package))
    (hd 1 (window_region_caps (window_started_base package))) (window_region_caps (window_started_base package))
    (window_started_iterator package) (window_started_bound package)
    (memory_nest_bounds (window_region_nest (window_started_base package)))
    (window_region_parameter_bounds (window_started_base package)) (window_region_parameters (window_started_base package)) s.
Definition window_package_header_tree source (package : window_started_package source) :=
  window_header_tree (window_region_root_lower (window_started_base package))
    (hd 1 (window_region_caps (window_started_base package))) (window_region_caps (window_started_base package))
    (window_started_iterator package) (window_started_bound package)
    (memory_nest_bounds (window_region_nest (window_started_base package)))
    (window_region_parameter_bounds (window_started_base package)) (window_region_parameters (window_started_base package)).
Definition window_package_header_domain source (package : window_started_package source) s :=
  window_header_domain (window_region_root_lower (window_started_base package))
    (hd 1 (window_region_caps (window_started_base package))) (window_region_caps (window_started_base package))
    (window_started_iterator package) (window_started_bound package)
    (memory_nest_bounds (window_region_nest (window_started_base package)))
    (window_region_parameters (window_started_base package)) s.
Theorem window_package_source_header_domain source (package : window_started_package source) fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  window_package_header_domain package (Entry ge locals temps memory).
Proof.
  intro SOURCE; unfold window_package_header_domain.
  eapply window_source_header_domain; [exact (window_region_certificate (window_started_base package))|
    exact (window_started_nest package)|exact SOURCE].
Qed.
Theorem window_package_header_exact source (package : window_started_package source) s :
  window_package_header_domain package s -> forall flag,
  decision_run s (window_package_header_tree package) flag <-> flag = window_package_header_accept package s.
Proof. apply window_header_encoding_exact. Qed.
Theorem window_package_header_sound source (package : window_started_package source) s :
  window_package_header_domain package s -> window_package_header_accept package s = true ->
  window_region_root_lower (window_started_base package) <= Int.signed (temp_word (window_started_iterator package) (entry_temps s)) <
    Int.signed (temp_word (window_started_bound package) (entry_temps s)) /\
  Int.signed (temp_word (window_started_iterator package) (entry_temps s)) < hd 1 (window_region_caps (window_started_base package)) /\
  Forall2 (fun cap key => register_range key cap s) (window_region_caps (window_started_base package))
    (memory_nest_bounds (window_region_nest (window_started_base package))) /\
  interval_ranges (window_region_parameter_bounds (window_started_base package))
    (memory_recursive_parameters (window_region_parameters (window_started_base package)) (entry_temps s)).
Proof.
  intros [DOMAIN WORDS] ACCEPT; unfold window_package_header_accept,window_header_accept in ACCEPT.
  apply andb_true_iff in ACCEPT as [COUNTS PARAMETERS].
  pose proof (window_region_certificate (window_started_base package)) as CERT.
  destruct (@window_bounds_sound _ _ _ _ _ _ s (proj1 (window_source_root_lower CERT))
    (window_root_cap_last_signed (window_source_caps CERT)) (window_caps_signed (window_source_caps CERT)) DOMAIN COUNTS)
    as [ACTIVE [ROOT RANGES]].
  split; [exact ACTIVE|split; [exact ROOT|split; [exact RANGES|]]].
  apply window_parameters_accept_sound; [|exact PARAMETERS].
  eapply Forall_impl; [|exact (window_source_parameter_bounds CERT)].
  intros interval [NONEMPTY SIGNED]; exact SIGNED.
Qed.
Print Assumptions window_package_source_header_domain.
Print Assumptions window_package_header_sound.
