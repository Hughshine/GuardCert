From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightRegionProgress.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode AffineNestLeafModel
  AffineNestGuardPackage AffineNestPackageGuard AffineNestPackageDecode.
From GuardInterface Require Import ClightConstantBoundModel ClightNestedExpressionTransport ClightNestedConstantModel.
Import ListNotations.
Set Implicit Arguments.

(** The existing data checker supplies the memory leaf and affine integer
    domain. The concrete source-to-model bridge supplies the actual execution;
    callers do not postulate a source/Loop correspondence. The cached source
    premise belongs after successful observation-preservation checks. *)
Theorem nested_constant_package_source_decode row root_cache column child_cache child_helper iterator component_helper
  upper body parameters live proposal
  (package:affine_guard_package
    (nested_constant_model_source row root_cache column child_cache child_helper iterator component_helper upper body)
    parameters live proposal)
  source_loop fe ge locals child_upper temps memory after final :
  affine_proposal_nest proposal=
    nested_constant_model_nest row root_cache column child_cache child_helper iterator component_helper upper body
      (AffineSourceLeaf body) ->
  NoDup [row;column;iterator;child_cache;child_helper;component_helper] ->
  temps!child_cache=Some(Vint child_upper) -> temps!child_helper=Some(Vint child_upper) ->
  temps!component_helper=Some(Vint(Int.repr upper)) ->
  (forall identifier, In identifier(affine_proposed_pointers proposal) ->
    ~In identifier(affine_nest_mutated(affine_proposal_nest proposal))) ->
  affine_package_source_loop parameters proposal=Some source_loop ->
  affine_package_guard_flag parameters proposal(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory
    (nested_cached_source row root_cache column child_cache(constant_body_source iterator(Int.repr upper) body))
    E0 after final Out_normal ->
  L.loop_semantics source_loop (map(affine_word_valuation temps)(affine_package_context parameters proposal))
    (RuntimeState(window_multi_pointer_locations temps(affine_proposed_window_lower proposal)
      (affine_proposed_window_upper proposal)) memory)
    (RuntimeState(window_multi_pointer_locations temps(affine_proposed_window_lower proposal)
      (affine_proposed_window_upper proposal)) final).
Proof.
  intros NEST DISTINCT CACHE CHILD COMPONENT POINTERS LOWER ACCEPT SOURCE.
  pose proof(affine_leaf_quiet(affine_package_leaf package)) as QUIET.
  pose proof(affine_leaf_writes(affine_package_leaf package)) as WRITES.
  rewrite NEST in QUIET,WRITES.
  change (quiet_statement body=true) in QUIET.
  change (writes_only [] body) in WRITES.
  pose proof(@nested_constant_closed_preinitialized_model fe ge locals row root_cache column child_cache child_helper
    iterator component_helper upper body child_upper temps memory E0 after final Out_normal
    DISTINCT QUIET WRITES CACHE CHILD COMPONENT SOURCE) as MODEL.
  exact(@affine_package_source_decode _ parameters live proposal package source_loop fe ge locals temps memory after final
    POINTERS LOWER ACCEPT MODEL).
Qed.

Print Assumptions nested_constant_package_source_decode.
