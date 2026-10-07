From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightRedundantSet ClightCountedLoop.
From GuardMemory Require Import GuardMemoryBooleanScan GuardMemoryWindowParameterGuard
  GuardMemoryIntervalBox GuardMemoryIntervalGuard.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage
  AffineNestPackageGuard AffineNestStaticPackage AffineNestScanNamespace.
From GuardInterface Require Import ClightSharedGuard ClightMaterializedCheck ClightCheckPlanFrame
  ClightAffineNestMaterialized ClightAffineFirstBodyReceipt ClightLoadedAffineFirstPath
  ClightLoadedAffineNumericGuard ClightLoadedAffineNumericSite ClightLoadedAffineBodyDomain
  ClightLoadedAffineBodyPrefix ClightLoadedAffineRootScan ClightLoadedAffineScanSite ClightLoadedOffsetHeader
  ClightExpressionAffineNumericSite ClightLoadedOffsetAffineRootScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition offset_affine_scan_body source parameters live proposal pointer delta
  (numeric : expression_affine_numeric_site source parameters live proposal (signed_load_offset pointer delta)) :=
  Ssequence(expression_numeric_check_code numeric)(loaded_affine_scan_tail proposal pointer).

(* A proposal is still syntax and interval data. This constructor checks all
   additional names, the recursive model, and the concrete dispatch body. *)
Record offset_affine_scan_site source parameters live proposal pointer delta := {
  offset_scan_numeric : expression_affine_numeric_site source parameters live proposal (signed_load_offset pointer delta);
  offset_scan_pointer_ports : incl(pointer::affine_proposed_pointers proposal) live;
  offset_scan_body_names : affine_loaded_body_names_check proposal pointer=true;
  offset_scan_child_code : GuardMemoryLoops.L.stmt;
  offset_scan_child_lower : affine_loaded_body_model parameters proposal=Some offset_scan_child_code;
  offset_scan_namespace : affine_scan_namespace(affine_proposal_nest proposal) parameters
    (loaded_affine_scan_ports parameters proposal live)(affine_proposal_rename proposal)(affine_proposed_result proposal);
  offset_scan_test : materialized_check;
  offset_scan_describe : describe_materialized_check(offset_affine_scan_body offset_scan_numeric)
    (shared_guard_choice(affine_proposed_result proposal))=Some offset_scan_test
}.
Definition check_offset_affine_scan_site source parameters live proposal pointer delta :
  option(offset_affine_scan_site source parameters live proposal pointer delta).
Proof.
  destruct(check_expression_affine_numeric_site source parameters live proposal (signed_load_offset pointer delta)) as [numeric|]; [|exact None].
  destruct(affine_names_allocated_check(pointer::affine_proposed_pointers proposal) live) eqn:POINTERS; [|exact None].
  destruct(affine_loaded_body_names_check proposal pointer) eqn:NAMES; [|exact None].
  destruct(affine_loaded_body_model parameters proposal) as [child|] eqn:LOWER; [|exact None].
  destruct(check_affine_scan_namespace(affine_proposal_nest proposal) parameters
    (loaded_affine_scan_ports parameters proposal live)(affine_proposal_rename proposal)(affine_proposed_result proposal))
    as [namespace|]; [|exact None].
  destruct(describe_materialized_check(offset_affine_scan_body numeric)(shared_guard_choice(affine_proposed_result proposal)))
    as [test|] eqn:DESCRIBE; [|exact None].
  exact(Some {| offset_scan_numeric:=numeric; offset_scan_pointer_ports:=@affine_names_allocated_check_sound _ _ POINTERS;
    offset_scan_body_names:=NAMES; offset_scan_child_code:=child; offset_scan_child_lower:=LOWER;
    offset_scan_namespace:=namespace; offset_scan_test:=test; offset_scan_describe:=DESCRIBE |}).
Defined.

Print Assumptions check_offset_affine_scan_site.
