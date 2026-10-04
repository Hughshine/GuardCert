From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap ClightCountedLoop ClightRedundantSet ClightRectangularGuard ClightFiniteRegion ClightLoopSyntax ClightRegionProgress ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryNaryRanges GuardMemoryRecursiveDomain GuardMemoryRecursiveSource GuardMemoryVectorBounds GuardMemoryTripleGuard
  GuardMemoryParameterRanges GuardMemoryParamPointerSyntax GuardMemoryParamPointerProjectedCandidate GuardMemoryPointerSequence.
From GuardMemory Require Import GuardMemoryStartedPackage GuardMemoryStartedHeader GuardMemoryStartedSourceWords GuardMemoryStartedPointerWords.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.
Definition memory_started_pointer_bounds_accept source (package : memory_started_pointer_package source) s :=
  memory_started_bounds_accept (memory_started_pointer_root_cap package)
    (param_pointer_region_limits (started_pointer_package package)) (started_pointer_iterator package)
    (started_pointer_bound package) (memory_nest_bounds (param_pointer_region_nest (started_pointer_package package))) s.
Definition memory_started_pointer_bounds_domain source (package : memory_started_pointer_package source) s :=
  memory_started_bounds_domain (param_pointer_region_limits (started_pointer_package package))
    (started_pointer_iterator package) (started_pointer_bound package)
    (memory_nest_bounds (param_pointer_region_nest (started_pointer_package package))) s.
Definition memory_started_pointer_header_accept source (package : memory_started_pointer_package source) s :=
  memory_started_pointer_bounds_accept package s && memory_parameter_ranges_accept
    (param_pointer_region_parameter_limits (started_pointer_package package)) (param_pointer_region_parameters (started_pointer_package package)) s.
Definition memory_started_pointer_header_tree source (package : memory_started_pointer_package source) :=
  decision_bind (memory_started_bounds_tree (memory_started_pointer_root_cap package)
    (param_pointer_region_limits (started_pointer_package package)) (started_pointer_iterator package)
    (started_pointer_bound package) (memory_nest_bounds (param_pointer_region_nest (started_pointer_package package))))
    (memory_parameter_ranges_tree (param_pointer_region_parameter_limits (started_pointer_package package))
      (param_pointer_region_parameters (started_pointer_package package)) (Decision true)) (Decision false).
Definition memory_started_pointer_header_domain source (package : memory_started_pointer_package source) s :=
  memory_started_pointer_bounds_domain package s /\
  (memory_started_pointer_bounds_accept package s = true ->
    Forall (fun id => register_domain id s) (param_pointer_region_parameters (started_pointer_package package))).
Theorem memory_started_pointer_header_exact source (package : memory_started_pointer_package source) s :
  memory_started_pointer_header_domain package s -> forall flag,
  decision_run s (memory_started_pointer_header_tree package) flag <-> flag = memory_started_pointer_header_accept package s.
Proof.
  intros [BOUNDS PARAMS] flag; unfold memory_started_pointer_header_tree,memory_started_pointer_header_accept.
  unfold memory_started_pointer_bounds_accept.
  replace (memory_parameter_ranges_accept (param_pointer_region_parameter_limits (started_pointer_package package))
    (param_pointer_region_parameters (started_pointer_package package)) s) with
    (memory_parameter_ranges_accept (param_pointer_region_parameter_limits (started_pointer_package package))
    (param_pointer_region_parameters (started_pointer_package package)) s && true) at 1 by (rewrite andb_true_r; reflexivity).
  apply memory_guard_gate_exact; [apply memory_started_bounds_exact; exact BOUNDS|].
  intros ACCEPT answer; apply memory_parameter_ranges_exact; [apply PARAMS; exact ACCEPT|].
  intros ALL value; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Theorem memory_started_pointer_header_sound source (package : memory_started_pointer_package source) s :
  memory_started_pointer_header_domain package s -> memory_started_pointer_header_accept package s = true ->
  0 <= Int.signed (temp_word (started_pointer_iterator package) (entry_temps s)) <
    Int.signed (temp_word (started_pointer_bound package) (entry_temps s)) /\
  Forall2 (fun cap key => register_range key cap s) (param_pointer_region_limits (started_pointer_package package))
    (memory_nest_bounds (param_pointer_region_nest (started_pointer_package package))) /\
  memory_nary_ranges (param_pointer_region_parameter_limits (started_pointer_package package))
    (memory_recursive_parameters (param_pointer_region_parameters (started_pointer_package package)) (entry_temps s)).
Proof.
  intros [DOMAIN WORDS] ACCEPT; unfold memory_started_pointer_header_accept in ACCEPT.
  apply andb_true_iff in ACCEPT as [COUNTS PARAMETERS].
  destruct (memory_started_pointer_root_cap_sound package) as [ROOT_POS ROOT_SIGNED].
  destruct (@memory_started_bounds_sound _ _ _ _ _ _ ROOT_POS ROOT_SIGNED
    (memory_param_pointer_caps_signed (started_pointer_package package)) DOMAIN COUNTS) as [ACTIVE RANGES].
  split; [exact ACTIVE|]; split; [exact RANGES|].
  eapply memory_parameter_ranges_sound; [exact (param_pointer_region_parameter_caps (param_pointer_region_syntax (started_pointer_package package)))|exact PARAMETERS].
Qed.
Theorem memory_started_pointer_source_bounds_domain source (package : memory_started_pointer_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_started_pointer_bounds_domain package (Entry ge locals temps memory).
Proof.
  intro SOURCE; pose proof (param_pointer_region_syntax (started_pointer_package package)) as CERT.
  pose proof (param_pointer_region_body CERT) as BODY.
  pose proof (started_pointer_nest package) as NEST.
  assert (LOOP : exec_stmt fe ge locals temps memory (memory_nest_source
    (MemorySourceAxis (started_pointer_iterator package) (started_pointer_bound package)
      (started_pointer_body package) (started_pointer_child package))) E0 after final Out_normal).
  { rewrite <-NEST,<- (param_pointer_region_source CERT); exact SOURCE. }
  assert (LENGTH : length (param_pointer_region_limits (started_pointer_package package)) =
    length (started_pointer_bound package::memory_nest_bounds (started_pointer_child package))).
  { pose proof (param_pointer_region_limits_length CERT) as LEN; rewrite memory_nest_lengths,NEST in LEN; exact LEN. }
  rewrite NEST in BODY; cbn [memory_nest_leaf] in BODY.
  assert (NORMAL : normal_statement (memory_nest_leaf (started_pointer_child package)) = true).
  { eapply memory_pointer_sequence_normal; exact BODY. }
  assert (QUIET : quiet_statement (memory_nest_leaf (started_pointer_child package)) = true).
  { eapply memory_pointer_sequence_quiet; exact BODY. }
  assert (WRITES : writes_only [] (memory_nest_leaf (started_pointer_child package))).
  { eapply memory_pointer_sequence_writes; exact BODY. }
  destruct (@memory_started_source_vector_bounds fe ge locals (started_pointer_iterator package) (started_pointer_bound package)
    (started_pointer_body package) (started_pointer_child package) (param_pointer_region_limits (started_pointer_package package))
    temps memory after final LENGTH (memory_param_pointer_caps_signed (started_pointer_package package))
    ltac:(rewrite <-NEST; exact (param_pointer_region_shapes CERT))
    ltac:(rewrite <-NEST; exact (param_pointer_region_fresh CERT))
    NORMAL QUIET WRITES
    LOOP) as [ITERATOR [BOUND DOMAIN]].
  unfold memory_started_pointer_bounds_domain,memory_started_bounds_domain.
  split; [exact ITERATOR|]; split; [exact BOUND|]; intro ACTIVE.
  rewrite NEST; apply DOMAIN; apply memory_started_active_true in ACTIVE; exact ACTIVE.
Qed.
Print Assumptions memory_started_pointer_header_exact.
Print Assumptions memory_started_pointer_header_sound.
Print Assumptions memory_started_pointer_source_bounds_domain.

Theorem memory_started_pointer_source_header_domain source (package : memory_started_pointer_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_started_pointer_header_domain package (Entry ge locals temps memory).
Proof.
  intro SOURCE.
  pose proof (@memory_started_pointer_source_bounds_domain source package fe ge locals temps memory after final SOURCE) as DOMAIN.
  split; [exact DOMAIN|]; intro ACCEPT.
  destruct (memory_started_pointer_root_cap_sound package) as [ROOT_POS ROOT_SIGNED].
  destruct (@memory_started_bounds_sound _ _ _ _ _ _ ROOT_POS ROOT_SIGNED
    (memory_param_pointer_caps_signed (started_pointer_package package)) DOMAIN ACCEPT) as [ACTIVE RANGES].
  assert (POSITIVE : Forall (fun key => 0 < Int.signed (temp_word key temps))
    (memory_nest_bounds (param_pointer_region_nest (started_pointer_package package)))).
  { induction RANGES; constructor; [exact (proj1 (proj2 H))|exact IHRANGES]. }
  rewrite (started_pointer_nest package) in POSITIVE; inversion POSITIVE as [|same keys POS CHILD_POS]; subst same keys.
  apply Forall_forall; intros identifier MEMBER.
  destruct (@memory_started_pointer_source_first_capability source (started_pointer_package package)
    (started_pointer_iterator package) (started_pointer_bound package) (started_pointer_body package) (started_pointer_child package)
    fe ge locals temps memory after final (started_pointer_nest package) CHILD_POS (proj2 ACTIVE) SOURCE identifier
    ltac:(apply in_or_app; left; exact MEMBER)) as [word WORD].
  exists word; exact WORD.
Qed.
Print Assumptions memory_started_pointer_source_header_domain.
