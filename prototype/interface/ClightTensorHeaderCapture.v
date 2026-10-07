From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap
  ClightRegionProgress ClightProjectedExecution.
From GuardInterface Require Import ClightWordArithmeticTransport ClightDirectWordObservation
  ClightTensorHeaderFirstPoint ClightNestedConstantSite ClightNestedConstantHeaders
  ClightNestedConstantFirstLeaf ClightNestedExpressionCapture ClightConstantBoundModel
  ClightLoadedBoundSyntax ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader
  ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.

Definition tensor_header_capture shape := nested_expression_capture(ncs_row shape)(ncs_root_cache shape)
  (signed_load_offset(ncs_pointer shape)(ncs_delta shape))(ncs_child_cache shape)
  (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape)).
Definition tensor_header_captured shape temps upper child :=
  nested_expression_captured(ncs_root_cache shape)(ncs_child_cache shape)temps upper child.

(** Conditional reads and the private snapshot state are produced from a
    completed original execution. A Some child receipt means the original
    outer loop reached the child header; an empty outer loop skips it. *)
Theorem tensor_header_capture_execution fe ge locals shape live temps memory after final :
  quiet_statement(ncs_leaf shape)=true -> check_plan_frameable(ncs_original shape)=true ->
  ~In(ncs_root_cache shape)(statement_temps(ncs_original shape)++live) ->
  ~In(ncs_child_cache shape)(statement_temps(ncs_original shape)++live) ->
  ncs_root_cache shape<>ncs_child_cache shape -> ncs_column shape<>ncs_pointer shape ->
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 after final Out_normal ->
  exists upper child prepared_after,
    exec_stmt fe ge locals temps memory(tensor_header_capture shape)
      E0(tensor_header_captured shape temps upper child)memory Out_normal /\
    exec_stmt fe ge locals(tensor_header_captured shape temps upper child)memory
      (ncs_original shape)E0 prepared_after final Out_normal /\
    temp_agree(statement_temps(ncs_original shape)++live)after prepared_after /\
    (match child with
    | None=>Int.lt(temp_word(ncs_row shape)temps)upper=false
    | Some word=>Int.lt(temp_word(ncs_row shape)temps)upper=true /\
        exists observers,ncs_observation_receipt shape
          (Entry ge locals(tensor_header_captured shape temps upper child)memory)observers
    end).
Proof.
  intros QUIET FRAMEABLE ROOT_PRIVATE CHILD_PRIVATE DISTINCT HEADER_PRIVATE SOURCE.
  destruct(@nested_expression_capture_execution fe ge locals temps memory(ncs_row shape)
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape))(ncs_column shape)
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))
    (constant_body_source(ncs_iterator shape)(Int.repr(ncs_upper shape))(ncs_leaf shape))
    (ncs_root_cache shape)(ncs_child_cache shape)live after final eq_refl eq_refl
    (@constant_literal_source_quiet _ _ _ QUIET)FRAMEABLE ROOT_PRIVATE CHILD_PRIVATE DISTINCT
    (@tensor_child_header_independent shape HEADER_PRIVATE)SOURCE)
    as [upper [child [prepared_after [CAPTURE [PREPARED [PUBLIC [ROOT CHILD]]]]]]].
  exists upper,child,prepared_after; split; [exact CAPTURE|split; [exact PREPARED|split; [exact PUBLIC|]]].
  destruct child as [word|]; [destruct CHILD as [ACTIVE CHILD]; split; [exact ACTIVE|]|exact CHILD].
  assert(FRAME:temp_agree(statement_temps(ncs_original shape)++live)temps
    (tensor_header_captured shape temps upper(Some word))).
  { apply nested_expression_captured_frame; assumption. }
  assert(ROOT_PREPARED:eval_expr ge locals(tensor_header_captured shape temps upper(Some word))memory
    (signed_load_offset(ncs_pointer shape)(ncs_delta shape))(Vint upper)).
  { eapply expression_temp_transport; [|exact FRAME|exact ROOT].
    intros id MEMBER; apply in_or_app; left; eapply nested_constant_bound_scope; exact MEMBER. }
  assert(CHILD_PREPARED:eval_expr ge locals(tensor_header_captured shape temps upper(Some word))memory
    (signed_indexed_offset(ncs_pointer shape)(ncs_index shape)(ncs_child_delta shape))(Vint word)).
  { eapply expression_temp_transport; [|exact FRAME|exact CHILD].
    intros id MEMBER; apply in_or_app; left; eapply nested_constant_child_bound_scope; exact MEMBER. }
  destruct(@ncs_headers_from_actual_evaluations shape ge locals
    (tensor_header_captured shape temps upper(Some word))memory upper word
    (@nested_expression_captured_root _ _ temps upper(Some word)DISTINCT)
    (@nested_expression_captured_child _ _ temps upper word)
    ROOT_PREPARED CHILD_PREPARED)as [block [offset [raw [child_raw RECEIPT]]]].
  exists(ncs_observers shape block offset raw child_raw); exact RECEIPT.
Qed.

(** Compose capture and source-path licensing at the same actual entry. The
    positive-child branch supplies the domain and an executable point check;
    this is still a first-point service, not a complete nested-loop scan. *)
Theorem tensor_header_capture_point_ready fe ge locals shape live pointer index rhs flag temps memory after final :
  word_arithmetic index -> ncs_leaf shape=direct_word_store pointer index rhs ->
  ~In pointer(ncs_coordinates shape) -> ncs_column shape<>ncs_pointer shape ->
  check_plan_frameable(ncs_original shape)=true ->
  ~In(ncs_root_cache shape)(statement_temps(ncs_original shape)++live) ->
  ~In(ncs_child_cache shape)(statement_temps(ncs_original shape)++live) ->
  ncs_root_cache shape<>ncs_child_cache shape ->
  temps!(ncs_row shape)=Some(Vint Int.zero) -> Int.lt Int.zero(Int.repr(ncs_upper shape))=true ->
  exec_stmt fe ge locals temps memory(ncs_original shape)E0 after final Out_normal ->
  exists upper child prepared_after,
    exec_stmt fe ge locals temps memory(tensor_header_capture shape)
      E0(tensor_header_captured shape temps upper child)memory Out_normal /\
    exec_stmt fe ge locals(tensor_header_captured shape temps upper child)memory
      (ncs_original shape)E0 prepared_after final Out_normal /\
    temp_agree(statement_temps(ncs_original shape)++live)after prepared_after /\
    forall word,child=Some word -> Int.lt Int.zero word=true -> exists observers,exists accepted:bool,
      ncs_observation_receipt shape(Entry ge locals(tensor_header_captured shape temps upper child)memory)observers /\
      direct_word_point_domain fe(tensor_zero_binding shape)pointer index rhs observers
        (Entry ge locals(tensor_header_captured shape temps upper child)memory) /\
      exec_stmt fe ge locals(tensor_header_captured shape temps upper child)memory
        (direct_word_check_code(tensor_zero_binding shape)pointer index observers flag)E0
        (PTree.set flag(Vint(if accepted then Int.one else Int.zero))
          (tensor_header_captured shape temps upper child))memory Out_normal.
Proof.
  intros WORD LEAF PRIVATE HEADER_PRIVATE FRAMEABLE ROOT_PRIVATE CHILD_PRIVATE DISTINCT ROW LITERAL SOURCE.
  destruct(@tensor_header_capture_execution fe ge locals shape live temps memory after final
    ltac:(rewrite LEAF; reflexivity)FRAMEABLE ROOT_PRIVATE CHILD_PRIVATE DISTINCT HEADER_PRIVATE SOURCE)
    as [upper [child [prepared_after [CAPTURE [PREPARED [PUBLIC RECEIPTS]]]]]].
  exists upper,child,prepared_after; split; [exact CAPTURE|split; [exact PREPARED|split; [exact PUBLIC|]]].
  intros word SAME POSITIVE; subst child; destruct RECEIPTS as [ACTIVE [observers RECEIPT]].
  assert(PREPARED_ROW:(tensor_header_captured shape temps upper(Some word))!(ncs_row shape)=Some(Vint Int.zero)).
  { unfold tensor_header_captured; rewrite(@nested_expression_captured_frame(statement_temps(ncs_original shape)++live)
      _ _ temps upper(Some word)ROOT_PRIVATE CHILD_PRIVATE(ncs_row shape)
      ltac:(apply in_or_app; left; apply nested_constant_row_scope)); exact ROW. }
  assert(ROOT_WORD:temp_word(ncs_root_cache shape)(tensor_header_captured shape temps upper(Some word))=upper).
  { unfold temp_word,tensor_header_captured; rewrite(@nested_expression_captured_root _ _ temps upper(Some word)DISTINCT); reflexivity. }
  assert(CHILD_WORD:temp_word(ncs_child_cache shape)(tensor_header_captured shape temps upper(Some word))=word).
  { unfold temp_word,tensor_header_captured; rewrite(@nested_expression_captured_child _ _ temps upper word); reflexivity. }
  assert(ROOT_ACTIVE:Int.lt Int.zero(temp_word(ncs_root_cache shape)
    (tensor_header_captured shape temps upper(Some word)))=true).
  { rewrite ROOT_WORD; unfold temp_word in ACTIVE; rewrite ROW in ACTIVE; exact ACTIVE. }
  pose proof(@tensor_header_original_first_point fe shape pointer index rhs
    (Entry ge locals(tensor_header_captured shape temps upper(Some word))memory)observers prepared_after final
    LEAF PRIVATE HEADER_PRIVATE PREPARED_ROW RECEIPT ROOT_ACTIVE
    ltac:(cbn[entry_temps]; rewrite CHILD_WORD; exact POSITIVE)LITERAL PREPARED)as DOMAIN.
  destruct(@direct_word_point_check_execution fe(tensor_zero_binding shape)pointer index rhs observers
    (Entry ge locals(tensor_header_captured shape temps upper(Some word))memory)flag WORD DOMAIN)
    as [accepted [CHECK PRESERVE]].
  exists observers,accepted; split; [exact RECEIPT|split; [exact DOMAIN|exact CHECK]].
Qed.

Print Assumptions tensor_header_capture_execution.
Print Assumptions tensor_header_capture_point_ready.
