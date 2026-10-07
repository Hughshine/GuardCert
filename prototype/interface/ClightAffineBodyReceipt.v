From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightCountedLoop ClightLoopSyntax ClightRegionProgress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryFootprintCapabilities
  GuardMemoryNaryCompute GuardMemoryRectangularFootprint.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestGuardPackage
  AffineNestLeafModel AffineNestLeafDecode AffineNestLeafLoop AffineNestLoopEncoding AffineNestScanPoints AffineNestScanModel.
From GuardInterface Require Import ClightLoadedAffineBodyPrefix ClightLoadedAffineBodyDomain
  ClightExpressionBodyPrefix ClightAffineBodyCapabilities ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A receipt of a reached recursive affine body. No relation between a
    memory observation and the cached upper is embedded in this interface. *)
Definition affine_body_receipt fe parameters proposal pointer index entry :=
  affine_loaded_body_ready parameters proposal entry /\
  0<=index<Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps entry)) /\
  exists current memory after final,
    current!(affine_proposed_iterator proposal)=Some(Vint(Int.repr index)) /\
    temp_agree(affine_loaded_body_stable parameters proposal pointer)(entry_temps entry) current /\
    memory_accesses_back(entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry)(entry_env entry) current memory(affine_proposed_body proposal)
      E0 after final Out_normal.

Theorem affine_received_point_capabilities source parameters live proposal pointer
  (package : affine_guard_package source parameters live proposal) fe entry index code :
  affine_loaded_body_names_check proposal pointer=true -> affine_body_receipt fe parameters proposal pointer index entry ->
  affine_loaded_body_model parameters proposal=Some code -> forall point,
  affine_scan_point(affine_proposed_child proposal)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) index) 0 point ->
  Forall (memory_cell_capable(window_multi_pointer_locations(entry_temps entry)
    (affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal))(entry_memory entry))
    (memory_point_footprint(map memory_nary_compute_instruction(affine_proposed_operations proposal))
      (map point(affine_proposal_layout proposal parameters))).
Proof.
  intros NAMES [READY [RANGE [current [memory [after [final [ROW [FRAME [BACK BODY]]]]]]]]] LOWER point POINT.
  pose proof (@affine_loaded_ready_body_decode source parameters live proposal package pointer NAMES
    fe entry index code current memory after final [] READY RANGE ROW FRAME LOWER BODY) as MODEL.
  unfold affine_loaded_body_model,affine_checked_leaf_code in LOWER; rewrite app_nil_r in LOWER.
  pose proof (affine_leaf_unique(affine_package_leaf package)) as UNIQUE; rewrite app_nil_r in UNIQUE.
  eapply affine_prefix_capabilities_at_guard_entry with(prefix:=[affine_proposed_iterator proposal])
    (lower:=0)(lower_code:=L.Constant 0)(code:=code)(tail:=[])(memory:=memory)(final:=final);
    try eassumption; try reflexivity.
  exact(window_multi_pointer_locations_int32 _ _ _).
Qed.

(** A compound-header prefix supplies the receipt. HEADER and READY are
    explicit domain inputs; neither licenses an unreached source body. *)
Theorem affine_expression_prefix_body_receipt fe parameters proposal pointer bound ready observations entry index :
  typeof bound=type_int32s -> normal_statement(affine_proposed_body proposal)=true ->
  quiet_statement(affine_proposed_body proposal)=true ->
  (forall origin, ready origin -> affine_loaded_body_ready parameters proposal origin) ->
  (forall origin i current memory, ready origin ->
    0<=i<=Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps origin)) ->
    current!(affine_proposed_iterator proposal)=Some(Vint(Int.repr i)) ->
    temp_agree(affine_loaded_body_stable parameters proposal pointer)(entry_temps origin) current ->
    ClightObservedHeaderPrefix.header_observations_match(observations origin) memory ->
    eval_expr(entry_ge origin)(entry_env origin) current memory bound (Vint(temp_word(affine_proposed_bound proposal)(entry_temps origin)))) ->
  expression_body_prefix fe (affine_proposed_iterator proposal)(affine_proposed_bound proposal) bound
    (affine_proposed_body proposal)(affine_loaded_body_stable parameters proposal pointer) ready observations index entry ->
  index<Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps entry)) ->
  affine_body_receipt fe parameters proposal pointer index entry.
Proof.
  intros TYPE NORMAL QUIET READY HEADER PREFIX ACTIVE.
  pose proof PREFIX as [ENTRY_READY [CACHE [RANGE REST]]].
  destruct (@expression_body_prefix_receipt fe (affine_proposed_iterator proposal)(affine_proposed_bound proposal) bound
    (affine_proposed_body proposal)(affine_loaded_body_stable parameters proposal pointer) ready observations
    TYPE NORMAL QUIET HEADER index entry PREFIX ACTIVE)
    as [current [memory [after [final [ROW [FRAME [OBSERVED [BACK BODY]]]]]]]].
  split; [apply READY; exact ENTRY_READY|split; [lia|]].
  exists current,memory,after,final; split; [exact ROW|split; [exact FRAME|split; [exact BACK|exact BODY]]].
Qed.

Print Assumptions affine_received_point_capabilities.
Print Assumptions affine_expression_prefix_body_receipt.
