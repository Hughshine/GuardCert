From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap.
From GuardAffineNest Require Import AffineNestGuardPackage.
From GuardInterface Require Import CompCertWordObservation ClightNestedConstantSite ClightNestedConstantWordModel
  ClightNestedConstantSitePrepare ClightNestedConstantHeaders ClightNestedConstantScanNames
  ClightNestedConstantSiteNumeric.
Import ListNotations.
Set Implicit Arguments.

Definition ncs_word_equal_expression cache expected :=
  Ebinop Cop.Oeq (Etempvar cache type_int32s) (Econst_int expected type_int32s) type_int32s.
Definition ncs_same_word_check shape word result :=
  Sifthenelse (ncs_word_equal_expression (ncs_root_cache shape) (Int.add word (ncs_delta shape)))
    (Sifthenelse (ncs_word_equal_expression (ncs_child_cache shape) (Int.add word (ncs_child_delta shape)))
      (Sset result (Econst_int Int.one type_int32s))
      (Sset result (Econst_int Int.zero type_int32s)))
    (Sset result (Econst_int Int.zero type_int32s)).
Definition ncs_same_word_check_temps shape word result ge locals memory temps :=
  PTree.set result (Val.of_bool (ncs_same_word_flag shape word (Entry ge locals temps memory))) temps.

Lemma ncs_word_equal_expression_test ge locals temps memory cache value expected :
  temps!cache = Some (Vint value) ->
  expression_test (ncs_word_equal_expression cache expected) (Entry ge locals temps memory) (Int.eq value expected).
Proof.
  intro CACHE; exists (Val.of_bool (Int.eq value expected)); split; [|apply bool_of_bool].
  eapply eval_Ebinop; [constructor; exact CACHE|constructor|reflexivity].
Qed.

(** Both reads here are initialized private temporaries. No header/pointer
    comparison or memory access is introduced by this residual check. *)
Theorem ncs_same_word_check_execution fe ge locals temps memory shape word result root child :
  temps!(ncs_root_cache shape) = Some (Vint root) ->
  temps!(ncs_child_cache shape) = Some (Vint child) ->
  exec_stmt fe ge locals temps memory (ncs_same_word_check shape word result)
    E0 (ncs_same_word_check_temps shape word result ge locals memory temps) memory Out_normal.
Proof.
  intros ROOT CHILD.
  destruct (@ncs_word_equal_expression_test ge locals temps memory (ncs_root_cache shape)
    root (Int.add word (ncs_delta shape)) ROOT) as [rv [REVAL RBOOL]].
  destruct (@ncs_word_equal_expression_test ge locals temps memory (ncs_child_cache shape)
    child (Int.add word (ncs_child_delta shape)) CHILD) as [cv [CEVAL CBOOL]].
  unfold ncs_same_word_check, ncs_same_word_check_temps, ncs_same_word_flag.
  cbn [entry_temps]; unfold temp_word; rewrite ROOT, CHILD.
  destruct (Int.eq root (Int.add word (ncs_delta shape))) eqn:R;
    destruct (Int.eq child (Int.add word (ncs_child_delta shape))) eqn:C; cbn.
  all: eapply exec_Sifthenelse; [exact REVAL|exact RBOOL|]; cbn.
  all: try (eapply exec_Sifthenelse; [exact CEVAL|exact CBOOL|]; cbn).
  all: constructor; constructor.
Qed.

Theorem ncs_same_word_check_frame shape word result ge locals memory temps ports :
  ~In result ports ->
  temp_agree ports temps (ncs_same_word_check_temps shape word result ge locals memory temps).
Proof.
  intro PRIVATE; unfold ncs_same_word_check_temps; apply temp_agree_set; exact PRIVATE.
Qed.

Theorem ncs_same_word_check_result shape word result ge locals memory temps :
  (ncs_same_word_check_temps shape word result ge locals memory temps)!result =
    Some (Val.of_bool (ncs_same_word_flag shape word (Entry ge locals temps memory))).
Proof. unfold ncs_same_word_check_temps; apply PTree.gss. Qed.

Section PREPARED.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.
Variable word : int.
Hypothesis BODY : check_constant_word_statement word (ncs_leaf shape) = true.

(** The model remains anchored before the residual check. Its live ports
    agree with the actual check exit; scratch state need not agree. *)
Theorem ncs_prepared_same_word_check fe ge locals checked memory checked_source_after final
  (receipt : ncs_prepared_receipt source parameters live proposal shape fe ge locals checked memory checked_source_after final) :
  exists after,
    exec_stmt fe ge locals (ncs_prepared_temps shape checked) memory
      (ncs_same_word_check shape word (affine_proposed_result proposal)) E0 after memory Out_normal /\
    temp_agree (ncs_ports source parameters live shape) (ncs_prepared_temps shape checked) after /\
    after!(affine_proposed_result proposal) = Some (Val.of_bool
      (ncs_same_word_flag shape word (Entry ge locals (ncs_prepared_temps shape checked) memory))) /\
    (after!(affine_proposed_result proposal) = Some (Vint Int.one) -> exists model_after,
      exec_stmt fe ge locals (ncs_prepared_temps shape checked) memory (ncs_model shape)
        E0 model_after final Out_normal /\
      temp_agree (ncs_scope source live) checked_source_after model_after /\
      ncs_numeric_flag parameters proposal shape
        (Entry ge locals (ncs_prepared_temps shape checked) memory) = true).
Proof.
  set (after := ncs_same_word_check_temps shape word (affine_proposed_result proposal)
    ge locals memory (ncs_prepared_temps shape checked)).
  assert (RESULT : after!(affine_proposed_result proposal) = Some (Val.of_bool
    (ncs_same_word_flag shape word (Entry ge locals (ncs_prepared_temps shape checked) memory)))).
  { apply ncs_same_word_check_result. }
  destruct (ncs_prepare_observers receipt) as [block [offset [raw [child_raw HEADERS]]]].
  destruct (ncs_receipt_ready HEADERS) as [ROOT CHILD].
  destruct ROOT as [b [o [r [P [READ CACHE]]]]].
  destruct CHILD as [b' [o' [r' [P' [READ' CACHE']]]]].
  exists after; split.
  - apply ncs_same_word_check_execution with
      (root:=Int.add r (ncs_delta shape)) (child:=Int.add r' (ncs_child_delta shape)); assumption.
  - split.
    + apply ncs_same_word_check_frame; intro BAD; apply (ncs_scan_flag_private site).
      apply in_or_app; right; exact BAD.
    + split; [exact RESULT|].
      intro ACCEPT.
      assert (FLAG : ncs_same_word_flag shape word
        (Entry ge locals (ncs_prepared_temps shape checked) memory) = true).
      { destruct (ncs_same_word_flag shape word
          (Entry ge locals (ncs_prepared_temps shape checked) memory)) eqn:FLAG; [reflexivity|].
        rewrite RESULT in ACCEPT; cbn [Val.of_bool] in ACCEPT; discriminate. }
      destruct (@ncs_same_word_accepted_model source parameters live proposal shape site word BODY
        fe ge locals checked memory checked_source_after final receipt FLAG) as [model_after [MODEL PUBLIC]].
      exists model_after; split; [exact MODEL|split; [exact PUBLIC|exact (ncs_prepare_accept receipt)]].
Qed.
End PREPARED.

Print Assumptions ncs_word_equal_expression_test.
Print Assumptions ncs_same_word_check_execution.
Print Assumptions ncs_same_word_check_frame.
Print Assumptions ncs_same_word_check_result.
Print Assumptions ncs_prepared_same_word_check.
