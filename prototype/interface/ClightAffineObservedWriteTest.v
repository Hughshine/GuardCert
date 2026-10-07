From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryWindowCells GuardMemoryNaryCompute
  GuardMemoryNaryAffineAccess GuardMemoryAffineSourceValuation GuardMemoryAffineSourceExpressions
  GuardMemoryFiniteAliasCondition GuardMemoryFootprintCapabilities GuardMemoryWindowAccess.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestGuardPackage
  AffineNestLeafModel AffineNestScanModel AffineNestScanSyntax AffineNestScanAccesses AffineNestScanAddress
  AffineNestPackageScanAccesses.
From GuardInterface Require Import ClightLoadedBodyPrefix ClightLoadedAffineBodyPrefix ClightLoadedAffineBodyDomain
  ClightLoadedAffineBodyStability ClightLoadedAffineWriteTest ClightAffineBodyReceipt ClightObservedWordProbe ClightAffineObservationLeaf.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section BODY.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable package : affine_guard_package source parameters live proposal.
Variable pointer : ident.
Hypothesis NAMES : affine_loaded_body_names_check proposal pointer=true.
Variable fe : genv -> Clight.function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable entry : clight_entry.
Variable i : Z.
Variable code : GuardMemoryLoops.L.stmt.
Hypothesis RECEIPT : affine_body_receipt fe parameters proposal pointer i entry.
Hypothesis OBSERVED : forall block offset, (entry_temps entry)!pointer=Some(Vptr block offset) ->
  exists value, Mem.loadv Mint32(entry_memory entry)(Vptr block offset)=Some value.
Hypothesis LOWER : affine_loaded_body_model parameters proposal=Some code.

Lemma affine_received_point_write_capable point operation :
  affine_scan_point (affine_proposed_child proposal)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i) 0 point ->
  In operation(affine_proposed_operations proposal) ->
  memory_cell_capable(window_multi_pointer_locations(entry_temps entry)
    (affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal))(entry_memory entry)
    (affine_scan_access_cell point(memory_nary_compute_write operation)).
Proof.
  intros POINT OPERATION.
  pose proof(@affine_received_point_capabilities source parameters live proposal pointer package
    fe entry i code NAMES RECEIPT LOWER point POINT) as CAPABLE.
  rewrite(@affine_scan_point_footprint _ _ _ _ [] _ point(affine_leaf_valid(affine_package_leaf package))) in CAPABLE.
  apply Forall_forall with(x:=affine_scan_access_cell point(memory_nary_compute_write operation)) in CAPABLE;
    [exact CAPABLE|apply in_map,affine_write_in_accesses; exact OPERATION].
Qed.

Lemma affine_received_point_write_binding point operation values checked :
  affine_scan_point (affine_proposed_child proposal)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i) 0 point ->
  In operation(affine_proposed_operations proposal) ->
  temp_agree(pointer::affine_proposed_pointers proposal)(entry_temps entry) checked ->
  affine_scan_word_view(affine_proposal_layout proposal parameters) values point checked ->
  memory_cell_address_binding(fun _=>affine_scan_address
    (memory_nary_access_array(memory_nary_compute_write operation)) values
    (memory_nary_access_expression(memory_nary_compute_write operation)))
    (window_multi_pointer_locations(entry_temps entry)(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal))
    (Entry(entry_ge entry)(entry_env entry) checked(entry_memory entry))
    (affine_scan_access_cell point(memory_nary_compute_write operation)).
Proof.
  intros POINT OPERATION FRAME WORDS.
  pose proof(@affine_write_in_accesses operation (affine_proposed_operations proposal) OPERATION) as ACCESS.
  destruct(@affine_package_scan_access source parameters live proposal package _ ACCESS) as [OWNED [LOW [HIGH VALID]]].
  eapply affine_scan_address_binding;
    [exact LOW|exact HIGH|apply FRAME; right; exact OWNED| |apply affine_received_point_write_capable; assumption].
  intros identifier MEMBER; apply WORDS.
  exact(@affine_package_scan_access_reads source parameters live proposal package _ identifier ACCESS MEMBER).
Qed.

Lemma affine_received_point_write_test point operation values checked block offset :
  affine_scan_point (affine_proposed_child proposal)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i) 0 point ->
  In operation(affine_proposed_operations proposal) ->
  temp_agree(pointer::affine_proposed_pointers proposal)(entry_temps entry) checked ->
  affine_scan_word_view(affine_proposal_layout proposal parameters) values point checked ->
  (entry_temps entry)!pointer=Some(Vptr block offset) ->
  expression_test(affine_observation_test pointer values operation)
    (Entry(entry_ge entry)(entry_env entry) checked(entry_memory entry))
    (observed_word_cell_check
      (window_multi_pointer_locations(entry_temps entry)(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal))
      (MemoryLocation Mint32 block(Ptrofs.unsigned offset))(affine_scan_access_cell point(memory_nary_compute_write operation))).
Proof.
  intros POINT OPERATION FRAME WORDS POINTER.
  destruct (@OBSERVED block offset POINTER) as [value READ].
  unfold affine_observation_test.
  eapply (@observed_word_cell_check_evaluation
    (fun _=>affine_scan_address (memory_nary_access_array(memory_nary_compute_write operation)) values
      (memory_nary_access_expression(memory_nary_compute_write operation)))
    (window_multi_pointer_locations(entry_temps entry)(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal))
    (affine_scan_access_cell point(memory_nary_compute_write operation))
    (entry_ge entry)(entry_env entry) checked(entry_memory entry) pointer block offset
    value);
    [apply affine_received_point_write_binding; eassumption|rewrite FRAME by(left; reflexivity); exact POINTER|exact READ].
Qed.

Theorem affine_received_body_check_writes_apart block offset :
  (entry_temps entry)!pointer=Some(Vptr block offset) ->
  affine_loaded_body_check_result proposal i entry(MemoryLocation Mint32 block(Ptrofs.unsigned offset))=true ->
  affine_loaded_body_writes_apart proposal i entry (MemoryLocation Mint32 block(Ptrofs.unsigned offset)).
Proof.
  intros POINTER CHECK.
  destruct (@OBSERVED block offset POINTER) as [value READ].
  assert(ALIGN:(4|Ptrofs.unsigned offset)).
  { cbn [Mem.loadv] in READ; destruct(zle(Ptrofs.unsigned offset+size_chunk Mint32)Ptrofs.modulus); [|discriminate].
    exact(proj2(Mem.load_valid_access _ _ _ _ _ READ)). }
  intros point POINT operation OPERATION write WRITE.
  unfold affine_loaded_body_check_result in CHECK.
  pose proof(proj1(@affine_scan_result_points (affine_proposed_child proposal)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i) 0 _) CHECK point POINT)
    as POINT_CHECK.
  unfold affine_observation_result in POINT_CHECK; apply forallb_forall with(x:=operation) in POINT_CHECK; [|exact OPERATION].
  eapply observed_word_cell_check_sound;
    [apply affine_received_point_write_capable; eassumption|exact WRITE|reflexivity|exact ALIGN|exact POINT_CHECK].
Qed.
End BODY.

Print Assumptions affine_received_point_write_capable.
Print Assumptions affine_received_point_write_binding.
Print Assumptions affine_received_point_write_test.
Print Assumptions affine_received_body_check_writes_apart.
