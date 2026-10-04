From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap
  ClightCountedLoop ClightRedundantSet ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRecursiveSource GuardMemoryRecursiveDomain
  GuardMemoryVectorBounds GuardMemoryVectorGuard GuardMemoryTripleGuard GuardMemoryNaryRanges.
From GuardMemory Require Import GuardMemoryParameterRanges GuardMemoryParamPointerSyntax
  GuardMemoryParamPointerBody GuardMemoryParamPointerDomain.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_param_pointer_header_accept source (package : memory_param_pointer_region_package source) s :=
  memory_vector_guard_accept (param_pointer_region_limits package) (param_pointer_region_nest package) s &&
  memory_parameter_ranges_accept (param_pointer_region_parameter_limits package)
    (param_pointer_region_parameters package) s.
Definition memory_param_pointer_header_tree source (package : memory_param_pointer_region_package source) :=
  decision_bind (memory_vector_guard_tree (param_pointer_region_limits package) (param_pointer_region_nest package))
    (memory_parameter_ranges_tree (param_pointer_region_parameter_limits package)
      (param_pointer_region_parameters package) (Decision true)) (Decision false).
Definition memory_param_pointer_header_domain source (package : memory_param_pointer_region_package source) s :=
  memory_vector_guard_domain (param_pointer_region_limits package) (param_pointer_region_nest package) s /\
  (memory_vector_guard_accept (param_pointer_region_limits package) (param_pointer_region_nest package) s = true ->
    Forall (fun identifier => register_domain identifier s) (param_pointer_region_parameters package)).

Theorem memory_param_pointer_header_exact source (package : memory_param_pointer_region_package source) s :
  memory_param_pointer_header_domain package s -> forall flag,
    decision_run s (memory_param_pointer_header_tree package) flag <->
    flag = memory_param_pointer_header_accept package s.
Proof.
  intros [COUNTS PARAMETERS] flag; unfold memory_param_pointer_header_tree,memory_param_pointer_header_accept.
  replace (memory_vector_guard_accept (param_pointer_region_limits package) (param_pointer_region_nest package) s &&
    memory_parameter_ranges_accept (param_pointer_region_parameter_limits package) (param_pointer_region_parameters package) s)
    with (memory_vector_guard_accept (param_pointer_region_limits package) (param_pointer_region_nest package) s &&
      (memory_parameter_ranges_accept (param_pointer_region_parameter_limits package) (param_pointer_region_parameters package) s && true))
    by (rewrite andb_true_r; reflexivity).
  apply memory_guard_gate_exact; [apply memory_vector_guard_exact; exact COUNTS|].
  intro ACCEPT; apply memory_parameter_ranges_exact; [apply PARAMETERS; exact ACCEPT|].
  intros _ result; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Theorem memory_param_pointer_header_sound source (package : memory_param_pointer_region_package source) s :
  memory_param_pointer_header_domain package s -> memory_param_pointer_header_accept package s = true ->
  memory_nest_initial (param_pointer_region_nest package) (entry_temps s) /\
  Forall2 (fun cap bound => register_range bound cap s) (param_pointer_region_limits package)
    (memory_nest_bounds (param_pointer_region_nest package)) /\
  memory_nary_ranges (param_pointer_region_parameter_limits package)
    (memory_recursive_parameters (param_pointer_region_parameters package) (entry_temps s)).
Proof.
  intros [DOMAIN WORDS] ACCEPT; unfold memory_param_pointer_header_accept in ACCEPT.
  apply andb_true_iff in ACCEPT as [COUNTS PARAMETERS].
  assert (CAPS : Forall signed_range (param_pointer_region_limits package)).
  { eapply Forall_impl; [|exact (param_pointer_region_caps (param_pointer_region_syntax package))].
    intros cap [POSITIVE SIGNED]; exact SIGNED. }
  destruct (@memory_vector_guard_sound _ _ _ CAPS DOMAIN COUNTS) as [INITIAL RANGES].
  split; [exact INITIAL|]; split; [exact RANGES|].
  eapply memory_parameter_ranges_sound; [exact (param_pointer_region_parameter_caps (param_pointer_region_syntax package))|exact PARAMETERS].
Qed.
Theorem memory_param_pointer_source_header_domain source (package : memory_param_pointer_region_package source)
  fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  memory_param_pointer_header_domain package (Entry ge locals temps memory).
Proof.
  intro SOURCE.
  pose proof (@memory_param_pointer_region_source_domain source package fe ge locals temps memory after final SOURCE) as DOMAIN.
  split; [exact DOMAIN|]; intro ACCEPT.
  assert (CAPS : Forall signed_range (param_pointer_region_limits package)).
  { eapply Forall_impl; [|exact (param_pointer_region_caps (param_pointer_region_syntax package))].
    intros cap [POSITIVE SIGNED]; exact SIGNED. }
  destruct (@memory_vector_guard_sound _ _ _ CAPS DOMAIN ACCEPT) as [INITIAL RANGES].
  assert (POSITIVE : Forall (fun bound => 0 < Int.signed (temp_word bound temps))
    (memory_nest_bounds (param_pointer_region_nest package))).
  { assert (FROM_RANGES : forall caps bounds,
      Forall2 (fun cap bound => register_range bound cap (Entry ge locals temps memory)) caps bounds ->
      Forall (fun bound => 0 < Int.signed (temp_word bound temps)) bounds).
    { intros caps bounds RUN; induction RUN; constructor; [exact (proj1 (proj2 H))|exact IHRUN]. }
    eapply FROM_RANGES; exact RANGES. }
  apply Forall_forall; intros identifier MEMBER.
  destruct (@memory_param_pointer_source_first_capability source package fe ge locals temps memory after final
    POSITIVE INITIAL SOURCE identifier ltac:(apply in_or_app; left; exact MEMBER)) as [word WORD].
  exists word; exact WORD.
Qed.
Print Assumptions memory_param_pointer_header_exact.
Print Assumptions memory_param_pointer_header_sound.
Print Assumptions memory_param_pointer_source_header_domain.
