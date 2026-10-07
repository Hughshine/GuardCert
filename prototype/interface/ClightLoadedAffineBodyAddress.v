From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryWindowCells GuardMemoryWindowAccess
  GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryRectangularFootprint GuardMemoryFiniteAliasCondition.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestGuardPackage
  AffineNestLeafModel AffineNestFirstDomain AffineNestScanModel AffineNestScanSyntax AffineNestScanAccesses
  AffineNestPackageScanAccesses AffineNestScanAddress.
From GuardInterface Require Import ClightLoadedBodyPrefix ClightLoadedAffineBodyPrefix
  ClightLoadedAffineBodyDomain ClightCapableWordSeparation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Instantiate the actual word-comparison domain from a checked recursive
    body. The prefix determines which body is reached; scan words describe
    the private cursor state. Mathematical windows never grant permission. *)
Theorem affine_loaded_body_point_address_domain source parameters live proposal pointer
  (package : affine_guard_package source parameters live proposal) fe entry i code point access values checked :
  affine_loaded_body_names_check proposal pointer=true ->
  loaded_body_prefix fe (affine_proposed_iterator proposal)(affine_proposed_bound proposal) pointer
    (affine_proposed_body proposal)(affine_loaded_body_stable parameters proposal pointer)
    (affine_loaded_body_ready parameters proposal) i entry ->
  i<Int.signed(temp_word (affine_proposed_bound proposal)(entry_temps entry)) ->
  affine_loaded_body_model parameters proposal=Some code ->
  affine_scan_point (affine_proposed_child proposal)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i) 0 point ->
  In access(affine_scan_accesses(affine_proposed_operations proposal)) ->
  temp_agree (pointer::affine_proposed_pointers proposal)(entry_temps entry) checked ->
  affine_scan_word_view (affine_proposal_layout proposal parameters) values point checked ->
  capable_word_address_domain
    (affine_scan_address (memory_nary_access_array access) values(memory_nary_access_expression access)) pointer
    (Entry (entry_ge entry)(entry_env entry) checked(entry_memory entry)).
Proof.
  intros NAMES PREFIX ACTIVE LOWER POINT ACCESS FRAME WORDS.
  pose proof (@affine_loaded_prefix_point_capabilities source parameters live proposal package pointer NAMES
    fe i entry code PREFIX ACTIVE LOWER point POINT) as CAPABLE.
  rewrite (@affine_scan_point_footprint (affine_proposed_leaf_bounds proposal)(affine_proposed_window_lower proposal)
    (affine_proposed_window_upper proposal)(affine_proposal_layout proposal parameters) []
    (affine_proposed_operations proposal) point(affine_leaf_valid(affine_package_leaf package))) in CAPABLE.
  apply Forall_forall with(x:=affine_scan_access_cell point access) in CAPABLE; [|apply in_map; exact ACCESS].
  destruct (@affine_package_scan_access source parameters live proposal package access ACCESS)
    as [OWNED [LOW [HIGH VALID]]].
  pose proof (@affine_scan_address_binding (memory_nary_access_expression access) values point
    (entry_ge entry)(entry_env entry)(entry_temps entry) checked(entry_memory entry)
    (affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)(memory_nary_access_array access)
    LOW HIGH (FRAME _ (or_intror OWNED))
    (fun identifier MEMBER=>WORDS identifier
      (@affine_package_scan_access_reads source parameters live proposal package access identifier ACCESS MEMBER)) CAPABLE)
    as BINDING.
  destruct BINDING as [location [offset BINDING]].
  destruct BINDING as [RESOLVE [CHUNK [OFFSET [PURE [TYPE [EVAL [VALID_POINTER ALIGN]]]]]]].
  destruct PREFIX as [_ [_ [_ REST]]].
  destruct REST as [bound_block [base [current [memory [after [final REST]]]]]].
  destruct REST as [POINTER [READ REST]].
  exists (location_block location),offset,bound_block,base,(Vint(temp_word(affine_proposed_bound proposal)(entry_temps entry))).
  split; [exact EVAL|split; [cbn [entry_temps]; rewrite FRAME by (left; reflexivity); exact POINTER|
    split; [exact VALID_POINTER|split; [exact ALIGN|exact READ]]]].
Qed.

Print Assumptions affine_loaded_body_point_address_domain.
