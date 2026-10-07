From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader
  ClightAffineJointObservation ClightNestedIndexedObservers ClightObservedHeaderPrefix
  ClightJointObserverSyntax ClightConstantJointOuterScan ClightNestedConstantSite.
Import ListNotations.
Set Implicit Arguments.

(** Fixed compile-time addresses. Dummy physical fields are never consumed
    by generated syntax; actual receipt fields are produced from entry reads. *)
Definition ncs_observer_templates shape :=
  [ClightWordObserver(signed_pointer_temp(ncs_pointer shape)) 1%positive Ptrofs.zero Vundef;
   ClightWordObserver(signed_indexed_pointer(ncs_pointer shape)(ncs_index shape)) 1%positive Ptrofs.zero Vundef].
Definition ncs_observers shape block offset raw child_raw :=
  nested_indexed_word_observers(ncs_pointer shape)(ncs_index shape) block offset raw child_raw.
Definition ncs_observations shape entry := loaded_offset_observations(ncs_pointer shape) entry++
  indexed_offset_observations(ncs_pointer shape)(ncs_index shape) entry.
Definition ncs_header_ready shape entry :=
  loaded_offset_cached_header(ncs_pointer shape)(ncs_delta shape)(ncs_root_cache shape) entry /\
  indexed_offset_cached_header(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape)(ncs_child_cache shape) entry.

Record ncs_observation_receipt shape entry observers := NCSObservationReceipt {
  ncs_receipt_ready : ncs_header_ready shape entry;
  ncs_receipt_reads : Forall(word_observer_receipt(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)) observers;
  ncs_receipt_addresses : map word_observer_address observers=map word_observer_address(ncs_observer_templates shape);
  ncs_receipt_snapshots : map word_observer_snapshot observers=ncs_observations shape entry;
  ncs_receipt_initial : header_observations_match(map word_observer_snapshot observers)(entry_memory entry)
}.

Theorem ncs_headers_from_actual_evaluations shape ge locals temps memory root_word child_word :
  temps!(ncs_root_cache shape)=Some(Vint root_word) -> temps!(ncs_child_cache shape)=Some(Vint child_word) ->
  eval_expr ge locals temps memory(signed_load_offset(ncs_pointer shape)(ncs_delta shape))(Vint root_word) ->
  eval_expr ge locals temps memory(signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))(Vint child_word) ->
  exists block offset raw child_raw,
    ncs_observation_receipt shape(Entry ge locals temps memory)(ncs_observers shape block offset raw child_raw).
Proof.
  intros CACHE CHILD_CACHE ROOT CHILD.
  destruct(@nested_indexed_observer_receipts ge locals temps memory(ncs_pointer shape)(ncs_index shape)
    (ncs_delta shape)(ncs_child_delta shape) root_word child_word ROOT CHILD)
    as [block [offset [raw [child_raw [POINTER [UPPER [CHILD_UPPER [READS SNAPSHOTS]]]]]]]].
  pose proof(Forall_inv READS) as ROOT_RECEIPT.
  pose proof(Forall_inv(Forall_inv_tail READS)) as CHILD_RECEIPT.
  exists block,offset,raw,child_raw; constructor.
  - split.
    + exists block,offset,raw; cbn [entry_temps entry_memory]; split; [exact POINTER|split].
      * exact(proj2(proj2 ROOT_RECEIPT)).
      * rewrite <-UPPER; exact CACHE.
    + exists block,offset,child_raw; cbn [entry_temps entry_memory]; split; [exact POINTER|split].
      * exact(proj2(proj2 CHILD_RECEIPT)).
      * rewrite <-CHILD_UPPER; exact CHILD_CACHE.
  - exact READS.
  - reflexivity.
  - exact SNAPSHOTS.
  - unfold header_observations_match; rewrite Forall_map.
    eapply Forall_impl; [|exact READS].
    intros observer RECEIPT; exact(proj1(word_observer_receipt_load RECEIPT)).
Qed.

Theorem ncs_root_header_from_receipt shape entry observers
  (receipt:ncs_observation_receipt shape entry observers) stable current memory :
  In(ncs_pointer shape) stable -> temp_agree stable(entry_temps entry) current ->
  header_observations_match(map word_observer_snapshot observers) memory ->
  eval_expr(entry_ge entry)(entry_env entry) current memory(signed_load_offset(ncs_pointer shape)(ncs_delta shape))
    (Vint(temp_word(ncs_root_cache shape)(entry_temps entry))).
Proof.
  intros POINTER FRAME OBSERVED; rewrite(ncs_receipt_snapshots receipt) in OBSERVED.
  unfold header_observations_match,ncs_observations in OBSERVED; apply Forall_app in OBSERVED as [ROOT CHILD].
  pose proof(proj1(ncs_receipt_ready receipt)) as READY.
  destruct READY as [block [offset [raw [TEMP [READ WORD]]]]].
  assert(CACHE : (entry_temps entry)!(ncs_root_cache shape)=Some(Vint(temp_word(ncs_root_cache shape)(entry_temps entry)))).
  { unfold temp_word; rewrite WORD; reflexivity. }
  eapply loaded_offset_bound_from_observations; [exact POINTER| |exact CACHE|exact FRAME|exact ROOT].
  exists block,offset,raw; repeat split; assumption.
Qed.

Theorem ncs_child_header_from_receipt shape entry observers
  (receipt:ncs_observation_receipt shape entry observers) stable current memory :
  In(ncs_pointer shape) stable -> temp_agree stable(entry_temps entry) current ->
  header_observations_match(map word_observer_snapshot observers) memory ->
  eval_expr(entry_ge entry)(entry_env entry) current memory
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    (Vint(temp_word(ncs_child_cache shape)(entry_temps entry))).
Proof.
  intros POINTER FRAME OBSERVED; rewrite(ncs_receipt_snapshots receipt) in OBSERVED.
  unfold header_observations_match,ncs_observations in OBSERVED; apply Forall_app in OBSERVED as [ROOT CHILD].
  pose proof(proj2(ncs_receipt_ready receipt)) as READY.
  destruct READY as [block [offset [raw [TEMP [READ WORD]]]]].
  assert(CACHE : (entry_temps entry)!(ncs_child_cache shape)=Some(Vint(temp_word(ncs_child_cache shape)(entry_temps entry)))).
  { unfold temp_word; rewrite WORD; reflexivity. }
  eapply indexed_offset_bound_from_observations; [exact POINTER| |exact CACHE|exact FRAME|exact CHILD].
  exists block,offset,raw; repeat split; assumption.
Qed.

Theorem ncs_outer_syntax_uses_templates shape entry observers
  (receipt:ncs_observation_receipt shape entry observers)
  row_cursor row_limit column_cursor column_limit flag nest controls values operations :
  constant_joint_outer_statement(ncs_root_cache shape)(ncs_child_cache shape) row_cursor row_limit column_cursor column_limit
    flag nest controls values observers operations=
  constant_joint_outer_statement(ncs_root_cache shape)(ncs_child_cache shape) row_cursor row_limit column_cursor column_limit
    flag nest controls values(ncs_observer_templates shape) operations.
Proof. apply constant_joint_outer_same_addresses; exact(ncs_receipt_addresses receipt). Qed.

Print Assumptions ncs_headers_from_actual_evaluations.
Print Assumptions ncs_root_header_from_receipt.
Print Assumptions ncs_child_header_from_receipt.
Print Assumptions ncs_outer_syntax_uses_templates.
