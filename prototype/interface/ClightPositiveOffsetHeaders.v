From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightCondition ClightNoWrap.
From GuardInterface Require Import CompCertPositiveOffsetFacts ClightLoadedOffsetHeader
  ClightSignedIndexedOffsetHeader ClightNestedConstantSite ClightNestedConstantHeaders.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This service consumes the existing capture receipt and actual cached word.
    It neither authorizes a new load nor assumes that the original raw header
    was a nonnegative mathematical bound. *)
Theorem loaded_positive_offset_presumption pointer delta cache entry :
  loaded_offset_cached_header pointer delta cache entry ->
  0 <= Int.signed delta ->
  0 <= Int.signed(temp_word cache(entry_temps entry)) ->
  exists block offset raw,
    (entry_temps entry)!pointer=Some(Vptr block offset) /\
    Mem.loadv Mint32(entry_memory entry)(Vptr block offset)=Some(Vint raw) /\
    Int.signed(temp_word cache(entry_temps entry))=Int.signed raw+Int.signed delta /\
    Int.min_signed<=Int.signed raw+Int.signed delta<=Int.max_signed.
Proof.
  intros [block [offset [raw [POINTER [READ CACHE]]]]] DELTA POSITIVE.
  assert(WORD:temp_word cache(entry_temps entry)=Int.add raw delta).
  { unfold temp_word; rewrite CACHE; reflexivity. }
  rewrite WORD in *; exists block,offset,raw.
  split; [exact POINTER|split; [exact READ|split]].
  - apply nonnegative_added_offset_exact; assumption.
  - apply nonnegative_added_offset_in_range; assumption.
Qed.

Theorem indexed_positive_offset_presumption pointer index delta cache entry :
  indexed_offset_cached_header pointer index delta cache entry ->
  0 <= Int.signed delta ->
  0 <= Int.signed(temp_word cache(entry_temps entry)) ->
  exists block offset raw,
    (entry_temps entry)!pointer=Some(Vptr block offset) /\
    Mem.loadv Mint32(entry_memory entry)(Vptr block(signed_indexed_address offset index))=Some(Vint raw) /\
    Int.signed(temp_word cache(entry_temps entry))=Int.signed raw+Int.signed delta /\
    Int.min_signed<=Int.signed raw+Int.signed delta<=Int.max_signed.
Proof.
  intros [block [offset [raw [POINTER [READ CACHE]]]]] DELTA POSITIVE.
  assert(WORD:temp_word cache(entry_temps entry)=Int.add raw delta).
  { unfold temp_word; rewrite CACHE; reflexivity. }
  rewrite WORD in *; exists block,offset,raw.
  split; [exact POINTER|split; [exact READ|split]].
  - apply nonnegative_added_offset_exact; assumption.
  - apply nonnegative_added_offset_in_range; assumption.
Qed.

(** The loaded tensor driver already produces this receipt after both reads.
    Positive profiles at that entry yield mathematical bounds without adding
    a raw-header overflow assumption to the family or compiler theorem. *)
Theorem nested_positive_offsets_presumption shape entry observers
  (receipt:ncs_observation_receipt shape entry observers) :
  0 <= Int.signed(ncs_delta shape) ->
  0 <= Int.signed(ncs_child_delta shape) ->
  0 <= Int.signed(temp_word(ncs_root_cache shape)(entry_temps entry)) ->
  0 <= Int.signed(temp_word(ncs_child_cache shape)(entry_temps entry)) ->
  (exists raw,
    Int.signed(temp_word(ncs_root_cache shape)(entry_temps entry))=Int.signed raw+Int.signed(ncs_delta shape) /\
    Int.min_signed<=Int.signed raw+Int.signed(ncs_delta shape)<=Int.max_signed) /\
  (exists raw,
    Int.signed(temp_word(ncs_child_cache shape)(entry_temps entry))=Int.signed raw+Int.signed(ncs_child_delta shape) /\
    Int.min_signed<=Int.signed raw+Int.signed(ncs_child_delta shape)<=Int.max_signed).
Proof.
  intros DELTA CHILD_DELTA POSITIVE CHILD_POSITIVE.
  destruct(ncs_receipt_ready receipt) as [ROOT CHILD].
  destruct(loaded_positive_offset_presumption ROOT DELTA POSITIVE)
    as [block [offset [raw [_ [_ [EXACT RANGE]]]]]].
  destruct(indexed_positive_offset_presumption CHILD CHILD_DELTA CHILD_POSITIVE)
    as [child_block [child_offset [child_raw [_ [_ [CHILD_EXACT CHILD_RANGE]]]]]].
  split; [exists raw|exists child_raw]; split; assumption.
Qed.

Print Assumptions loaded_positive_offset_presumption.
Print Assumptions indexed_positive_offset_presumption.
Print Assumptions nested_positive_offsets_presumption.
