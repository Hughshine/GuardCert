From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint.
From GuardMemory Require Import GuardMemoryRecursiveSource GuardMemoryParamPointerSyntax
  GuardMemoryParamPointerHeader GuardMemoryParamPointerProjectedCandidate GuardMemoryParamAxisFrame
  GuardMemoryParamAxisGuard.
From GuardInterface Require Import GuardInterface ClightPrivateScan ClightPrivateScanSafety
  ClightPrivateScanHost ClightParamPointerScanBridge.
Import ListNotations.
Set Implicit Arguments.

Section CERTIFICATE.
Variable source : statement.
Variable package : memory_param_pointer_region_package source.
Variable live left right : list ident.
Variable flag result : ident.
Hypothesis LEFT : length left = length (memory_nest_iterators (param_pointer_region_nest package)).
Hypothesis RIGHT : length right = length (memory_nest_iterators (param_pointer_region_nest package)).
Hypothesis UNIQUE : NoDup (left ++ right).
Hypothesis LEFT_PARAM : NoDup (left ++ param_pointer_region_parameters package).
Hypothesis RIGHT_PARAM : NoDup (right ++ param_pointer_region_parameters package).
Hypothesis FRESH : forall identifier, In identifier (left ++ right) ->
  ~ In identifier (memory_param_axis_pointer_guard_protected package live) /\ identifier <> flag.
Hypothesis FLAG : ~ In flag (memory_param_axis_pointer_guard_protected package live).
Hypothesis RESULT : ~ In result
  (statement_temps (memory_param_axis_pointer_guard_statement package left right flag) ++
   memory_param_axis_pointer_guard_protected package live).

Definition param_pointer_scan_test : private_scan_test.
Proof.
  refine {| scan_body := memory_param_axis_pointer_guard_statement package left right flag;
    scan_result := result; scan_supported := param_axis_pointer_guard_supported package left right flag |}.
  intro BAD; apply RESULT; apply in_or_app; left; exact BAD.
Defined.

Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Context {O : Type} (observe : fragment_observation -> O -> Prop).

(** D provides machine values needed to execute the encoder, without assuming
    the header's acceptance or the nonaliasing premise. P refers to the
    original entry. Both outcomes expose the same protected entry frame. *)
Definition param_pointer_scan_certificate :
  guard_certificate (private_scan_host fe observe)
    (memory_param_pointer_runtime_domain package) (memory_param_pointer_runtime_presumption package)
    (private_scan_entry_frame (memory_param_axis_pointer_guard_protected package live))
    (private_scan_entry_frame (memory_param_axis_pointer_guard_protected package live))
    param_pointer_scan_test.
Proof.
  assert (SAFE : forall entry, memory_param_pointer_runtime_domain package entry ->
    check_safe (private_scan_host fe observe) param_pointer_scan_test entry).
  { intros entry DOMAIN.
    destruct (@param_axis_pointer_prefix_entry_witness source package fe entry live left right flag result
      LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM FRESH FLAG RESULT DOMAIN)
      as [accepted [checked [PREFIX REST]]].
    eapply completed_private_scan_safe; [exact PREFIX|].
    apply private_scan_prefix_supported; apply param_axis_pointer_guard_supported. }
  constructor.
  - exact SAFE.
  - intros entry DOMAIN; apply private_scan_host_safe_available; apply SAFE; exact DOMAIN.
  - intros entry accepted checked DOMAIN CHECK.
    destruct (@private_scan_checks_prefix fe param_pointer_scan_test entry accepted checked CHECK)
      as [PREFIX [GE [ENV [MEMORY TEST]]]].
    destruct (@param_axis_pointer_prefix_all_executions source package fe entry live left right flag result
      LEFT RIGHT UNIQUE LEFT_PARAM RIGHT_PARAM FRESH FLAG RESULT DOMAIN _ _ _ _ PREFIX)
      as [_ [_ [_ [FRAME SOUND]]]].
    assert (ENTRY : private_scan_entry_frame (memory_param_axis_pointer_guard_protected package live) entry checked)
      by (repeat split; assumption).
    destruct accepted; cbn; [split; [|exact ENTRY]|exact ENTRY].
    apply SOUND; destruct checked as [ge locals temps memory]; cbn in GE, ENV, MEMORY, TEST |- *.
    subst; exact TEST.
Defined.
End CERTIFICATE.

Print Assumptions param_pointer_scan_test.
Print Assumptions param_pointer_scan_certificate.
