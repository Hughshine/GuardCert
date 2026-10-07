From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightProjectedExecution.
From GuardInterface Require Import ClightWordArithmeticTransport ClightDirectWordObservation
  ClightNestedConstantSite ClightNestedConstantHeaders ClightNestedConstantFirstLeaf
  ClightNestedExpressionCapture ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightSignedIndexedOffsetHeader ClightObservedHeaderPrefix ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.

(** The coordinates are replaced in guard expressions, rather than read
    from uninitialized public loop counters. All other parameters remain
    the actual source parameters, including a variable leading dimension. *)
Definition tensor_zero_binding shape id :=
  if peq id(ncs_row shape) then Some Int.zero else
  if peq id(ncs_column shape) then Some Int.zero else
  if peq id(ncs_iterator shape) then Some Int.zero else None.
Definition tensor_first_temps shape temps :=
  PTree.set(ncs_iterator shape)(Vint Int.zero)(PTree.set(ncs_column shape)(Vint Int.zero)temps).

Lemma tensor_first_point_frame shape pointer index temps :
  temps!(ncs_row shape)=Some(Vint Int.zero) ->
  ~In pointer(ncs_coordinates shape) ->
  direct_word_frame(tensor_zero_binding shape)pointer index(tensor_first_temps shape temps)temps.
Proof.
  intros ROW PRIVATE; split.
  - unfold tensor_first_temps; rewrite !PTree.gso; [reflexivity| |];
      unfold ncs_coordinates in PRIVATE; cbn in PRIVATE; intuition congruence.
  - intros id MEMBER; unfold tensor_zero_binding,tensor_first_temps.
    repeat rewrite PTree.gsspec.
    repeat match goal with |-context[peq ?first ?second]=>destruct(peq first second)end;
      subst; congruence.
Qed.

Lemma tensor_child_header_independent shape :
  ncs_column shape<>ncs_pointer shape ->
  ~In(ncs_column shape)(expression_temps
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))).
Proof.
  intro PRIVATE; cbn [signed_indexed_offset signed_indexed_load signed_indexed_pointer
    signed_pointer_temp expression_temps].
  cbn; intuition congruence.
Qed.

(** The witness is obtained from the original loaded-bound nest, not from
    a cached affine model. The leaf's actual store supplies guard permission.
    No no-alias/no-wrap assertion or semantic callback is an input. *)
Theorem tensor_header_original_first_point fe shape pointer index rhs entry observers after final :
  ncs_leaf shape=direct_word_store pointer index rhs ->
  ~In pointer(ncs_coordinates shape) -> ncs_column shape<>ncs_pointer shape ->
  (entry_temps entry)!(ncs_row shape)=Some(Vint Int.zero) ->
  ncs_observation_receipt shape entry observers ->
  Int.lt Int.zero(temp_word(ncs_root_cache shape)(entry_temps entry))=true ->
  Int.lt Int.zero(temp_word(ncs_child_cache shape)(entry_temps entry))=true ->
  Int.lt Int.zero(Int.repr(ncs_upper shape))=true ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (ncs_original shape)E0 after final Out_normal ->
  direct_word_point_domain fe(tensor_zero_binding shape)pointer index rhs observers entry.
Proof.
  intros LEAF PRIVATE HEADER_PRIVATE ROW RECEIPT ROOT_ACTIVE CHILD_ACTIVE LITERAL_ACTIVE SOURCE.
  pose proof(@ncs_root_header_from_receipt shape entry observers RECEIPT[ncs_pointer shape]
    (entry_temps entry)(entry_memory entry)(or_introl eq_refl)(temp_agree_refl _ _)
    (ncs_receipt_initial RECEIPT))as ROOT.
  pose proof(@ncs_child_header_from_receipt shape entry observers RECEIPT[ncs_pointer shape]
    (entry_temps entry)(entry_memory entry)(or_introl eq_refl)(temp_agree_refl _ _)
    (ncs_receipt_initial RECEIPT))as CHILD.
  assert(ACTIVE:Int.lt(temp_word(ncs_row shape)(entry_temps entry))
    (temp_word(ncs_root_cache shape)(entry_temps entry))=true).
  { unfold temp_word at 1; rewrite ROW; exact ROOT_ACTIVE. }
  destruct(@nested_constant_original_first_leaf fe(entry_ge entry)(entry_env entry)
    (ncs_row shape)(signed_load_offset(ncs_pointer shape)(ncs_delta shape))
    (ncs_column shape)(signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    (ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape)
    (entry_temps entry)(entry_memory entry)after final
    (temp_word(ncs_root_cache shape)(entry_temps entry))(temp_word(ncs_child_cache shape)(entry_temps entry))
    eq_refl eq_refl ltac:(rewrite LEAF; reflexivity)ltac:(rewrite LEAF; reflexivity)
    (@tensor_child_header_independent shape HEADER_PRIVATE)ROOT CHILD ACTIVE CHILD_ACTIVE LITERAL_ACTIVE SOURCE)
    as [leaf_after [leaf_final RUN]].
  split; [exact(ncs_receipt_reads RECEIPT)|].
  exists(tensor_first_temps shape(entry_temps entry)),(entry_memory entry),leaf_after,leaf_final.
  split; [apply tensor_first_point_frame; assumption|split; [apply memory_accesses_back_refl|]].
  rewrite LEAF in RUN; exact RUN.
Qed.

Theorem tensor_header_first_check_available fe shape pointer index rhs entry observers after final :
  word_arithmetic index ->
  ncs_leaf shape=direct_word_store pointer index rhs ->
  ~In pointer(ncs_coordinates shape) -> ncs_column shape<>ncs_pointer shape ->
  (entry_temps entry)!(ncs_row shape)=Some(Vint Int.zero) ->
  ncs_observation_receipt shape entry observers ->
  Int.lt Int.zero(temp_word(ncs_root_cache shape)(entry_temps entry))=true ->
  Int.lt Int.zero(temp_word(ncs_child_cache shape)(entry_temps entry))=true ->
  Int.lt Int.zero(Int.repr(ncs_upper shape))=true ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (ncs_original shape)E0 after final Out_normal ->
  exists accepted,decision_run entry
    (direct_word_observer_tree(tensor_zero_binding shape)pointer index(ncs_observer_templates shape))accepted.
Proof.
  intros WORD LEAF PRIVATE HEADER_PRIVATE ROW RECEIPT ROOT CHILD LITERAL SOURCE.
  pose proof(@tensor_header_original_first_point fe shape pointer index rhs entry observers after final
    LEAF PRIVATE HEADER_PRIVATE ROW RECEIPT ROOT CHILD LITERAL SOURCE)as DOMAIN.
  destruct(direct_word_point_available WORD DOMAIN)as [accepted RUN].
  rewrite(@direct_word_observer_tree_addresses _ _ _ _ _ (ncs_receipt_addresses RECEIPT))in RUN.
  exists accepted; exact RUN.
Qed.

Print Assumptions tensor_first_point_frame.
Print Assumptions tensor_child_header_independent.
Print Assumptions tensor_header_original_first_point.
Print Assumptions tensor_header_first_check_available.
