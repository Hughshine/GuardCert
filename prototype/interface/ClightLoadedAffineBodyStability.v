From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells
  GuardMemoryAffineSourceValuation GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryObservationStability.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestGuardPackage AffineNestLeafModel
  AffineNestLeafDecode AffineNestLoopEncoding AffineNestScanModel AffineNestScanAccesses AffineNestWriteFootprint.
From GuardInterface Require Import ClightLoadedBodyPrefix ClightLoadedAffineBodyPrefix ClightLoadedAffineBodyDomain.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_loaded_body_writes_apart proposal i entry observation :=
  forall point, affine_scan_point (affine_proposed_child proposal)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i) 0 point ->
  forall operation, In operation(affine_proposed_operations proposal) -> forall write,
    window_multi_pointer_locations(entry_temps entry)(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal)
      (affine_scan_access_cell point(memory_nary_compute_write operation))=Some write ->
    location_disjoint write observation.

Section BODY.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable package : affine_guard_package source parameters live proposal.
Variable pointer : ident.
Hypothesis NAMES : affine_loaded_body_names_check proposal pointer=true.

Theorem affine_loaded_ready_body_observation fe entry i code current memory after final observation :
  affine_loaded_body_ready parameters proposal entry ->
  0<=i<Int.signed(temp_word (affine_proposed_bound proposal)(entry_temps entry)) ->
  current!(affine_proposed_iterator proposal)=Some(Vint(Int.repr i)) ->
  temp_agree (affine_loaded_body_stable parameters proposal pointer)(entry_temps entry) current ->
  affine_loaded_body_model parameters proposal=Some code ->
  affine_loaded_body_writes_apart proposal i entry observation ->
  exec_stmt fe (entry_ge entry)(entry_env entry) current memory(affine_proposed_body proposal) E0 after final Out_normal ->
  location_load observation final=location_load observation memory.
Proof.
  intros READY RANGE ROW FRAME LOWER APART BODY.
  pose proof (@affine_loaded_ready_body_decode source parameters live proposal package pointer NAMES
    fe entry i code current memory after final [] READY RANGE ROW FRAME LOWER BODY) as MODEL.
  unfold affine_loaded_body_model,affine_checked_leaf_code in LOWER; rewrite app_nil_r in LOWER.
  pose proof(affine_leaf_unique(affine_package_leaf package)) as UNIQUE; rewrite app_nil_r in UNIQUE.
  eapply memory_loop_observation_preserved; [|exact MODEL].
  eapply affine_scan_checked_writes_apart with(prefix:=[affine_proposed_iterator proposal])
    (lower_code:=L.Constant 0)(bounds:=affine_proposed_leaf_bounds proposal)
    (window_lower:=affine_proposed_window_lower proposal)(window_upper:=affine_proposed_window_upper proposal);
    try eassumption; try reflexivity.
  exact(affine_leaf_valid(affine_package_leaf package)).
Qed.

(** This is the property required by the root prefix service, obtained from
    pointwise write separation. It quantifies real body executions and does
    not assume observation preservation or cached-root completion. *)
Theorem affine_loaded_body_separation_preserved fe entry i code :
  affine_loaded_body_ready parameters proposal entry ->
  0<=i<Int.signed(temp_word (affine_proposed_bound proposal)(entry_temps entry)) ->
  affine_loaded_body_model parameters proposal=Some code ->
  (forall block offset, (entry_temps entry)!pointer=Some(Vptr block offset) ->
    affine_loaded_body_writes_apart proposal i entry
      (MemoryLocation Mint32 block(Ptrofs.unsigned offset))) ->
  loaded_body_preserved fe (affine_proposed_iterator proposal)(affine_proposed_bound proposal) pointer
    (affine_proposed_body proposal)(affine_loaded_body_stable parameters proposal pointer) i entry.
Proof.
  intros READY RANGE LOWER APART block offset current memory after final POINTER ROW FRAME READ BODY.
  pose proof (@affine_loaded_ready_body_observation fe entry i code current memory after final
    (MemoryLocation Mint32 block(Ptrofs.unsigned offset)) READY RANGE ROW FRAME LOWER (APART block offset POINTER) BODY) as KEEP.
  cbn [location_load location_chunk location_block location_offset] in KEEP.
  cbn [Mem.loadv] in READ |- *.
  destruct(zle(Ptrofs.unsigned offset+size_chunk Mint32)Ptrofs.modulus); [exact KEEP|discriminate].
Qed.
End BODY.

Print Assumptions affine_loaded_ready_body_observation.
Print Assumptions affine_loaded_body_separation_preserved.
