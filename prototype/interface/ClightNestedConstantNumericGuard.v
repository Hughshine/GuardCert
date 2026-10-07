From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet ClightTempFrame ClightTempFootprint
  ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode
  AffineNestGuardPackage AffineNestPackageGuard AffineNestNamespace AffineNestMathDomain.
From GuardInterface Require Import ClightConstantBoundModel ClightNestedExpressionCapture ClightNestedConstantModel
  ClightNestedConstantNumericInputs ClightCapturedAffineNumericGuard ClightAffineNestMaterialized.
Import ListNotations.
Set Implicit Arguments.

Definition nested_constant_numeric_code root_cache child_cache result numeric_code :=
  Sifthenelse(register_positive_expr root_cache)
    (Sifthenelse(register_positive_expr child_cache) numeric_code
      (Sset result(Econst_int Int.zero type_int32s)))
    (Sset result(Econst_int Int.zero type_int32s)).
Definition nested_constant_numeric_flag root_cache child_cache parameters proposal entry :=
  if register_positive root_cache entry then
    if register_positive child_cache entry then affine_package_guard_flag parameters proposal entry else false
  else false.

(** The gates are actual read-only Clight tests. Inactive roots need no
    child receipt; inactive children need no parameter or memory-leaf receipt. *)
Theorem nested_constant_numeric_guard_execution row root_cache column child_cache child_helper iterator component_helper
  upper body parameters live proposal
  (package:affine_guard_package
    (nested_constant_model_source row root_cache column child_cache child_helper iterator component_helper upper body)
    parameters live proposal)
  fe ge locals bound child_bound root_word temps memory source_after source_final :
  affine_proposal_nest proposal=nested_constant_model_nest row root_cache column child_cache child_helper
    iterator component_helper upper body(AffineSourceLeaf body) ->
  typeof bound=type_int32s -> typeof child_bound=type_int32s -> ~In column(expression_temps child_bound) ->
  temps!row=Some(Vint Int.zero) -> temps!root_cache=Some(Vint root_word) ->
  eval_expr ge locals temps memory bound(Vint root_word) ->
  (register_positive root_cache(Entry ge locals temps memory)=true -> exists child_word,
    temps!child_cache=Some(Vint child_word) /\ eval_expr ge locals temps memory child_bound(Vint child_word)) ->
  Int.lt Int.zero(Int.repr upper)=true ->
  exec_stmt fe ge locals temps memory
    (nested_expression_source row bound column child_bound(constant_body_source iterator(Int.repr upper) body))
    E0 source_after source_final Out_normal ->
  exists after,
    exec_stmt fe ge locals temps memory
      (nested_constant_numeric_code root_cache child_cache(affine_proposed_result proposal)(affine_package_guard_code package))
      E0 after memory Out_normal /\
    temp_agree(affine_single_materialized_ports parameters proposal live) temps after /\
    after!(affine_proposed_result proposal)=Some(Vint(if nested_constant_numeric_flag root_cache child_cache
      parameters proposal(Entry ge locals temps memory) then Int.one else Int.zero)) /\
    (nested_constant_numeric_flag root_cache child_cache parameters proposal(Entry ge locals temps memory)=true ->
      Forall(fun identifier=>register_domain identifier(Entry ge locals temps memory)) parameters /\
      affine_math_domain(affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)
        (affine_proposal_nest proposal)(affine_word_valuation temps) 0).
Proof.
  intros NEST TYPE CHILD_TYPE COLUMN_PRIVATE ROW CACHE ROOT CHILD LITERAL_ACTIVE SOURCE.
  assert (IDS : affine_proposed_iterator proposal=row /\ affine_proposed_bound proposal=root_cache).
  { unfold affine_proposal_nest,nested_constant_model_nest in NEST; inversion NEST; auto. }
  destruct IDS as [ITERATOR BOUND].
  assert (PRIVATE : ~In(affine_proposed_result proposal)(affine_single_materialized_ports parameters proposal live))
    by exact(affine_names_result_private(affine_package_namespace package)).
  assert (ROW_VALUE : affine_word_valuation temps row=0%Z).
  { unfold affine_word_valuation,temp_word; rewrite ROW,Int.signed_zero; reflexivity. }
  pose proof(@register_positive_test root_cache(Entry ge locals temps memory) ltac:(exists root_word; exact CACHE))
    as [root_result [ROOT_TEST ROOT_BOOL]].
  unfold nested_constant_numeric_flag,nested_constant_numeric_code.
  destruct(register_positive root_cache(Entry ge locals temps memory)) eqn:ROOT_ACTIVE.
  - destruct(CHILD eq_refl) as [child_word [CHILD_WORD CHILD_EVAL]].
    pose proof(@register_positive_test child_cache(Entry ge locals temps memory) ltac:(exists child_word; exact CHILD_WORD))
      as [child_result [CHILD_TEST CHILD_BOOL]].
    destruct(register_positive child_cache(Entry ge locals temps memory)) eqn:CHILD_ACTIVE.
    + assert (ROOT_MACHINE : Int.lt(temp_word row temps) root_word=true).
      { unfold register_positive in ROOT_ACTIVE; cbn [entry_temps] in ROOT_ACTIVE.
        unfold temp_word in *; rewrite CACHE in ROOT_ACTIVE; rewrite ROW; exact ROOT_ACTIVE. }
      assert (CHILD_MACHINE : Int.lt Int.zero child_word=true).
      { unfold register_positive,temp_word in CHILD_ACTIVE; cbn [entry_temps] in CHILD_ACTIVE.
        rewrite CHILD_WORD in CHILD_ACTIVE; exact CHILD_ACTIVE. }
      pose proof(@nested_constant_original_parameter_domains row root_cache column child_cache child_helper iterator
        component_helper upper body parameters live proposal package fe ge locals bound child_bound root_word child_word
        temps memory source_after source_final NEST TYPE CHILD_TYPE COLUMN_PRIVATE CACHE CHILD_WORD ROOT CHILD_EVAL
        ROOT_MACHINE CHILD_MACHINE LITERAL_ACTIVE SOURCE) as PARAMETERS.
      destruct(@affine_captured_package_guard_execution _ parameters live proposal package fe ge locals temps memory
        ltac:(rewrite ITERATOR; exists Int.zero; exact ROW)
        ltac:(rewrite BOUND; exists root_word; exact CACHE) PARAMETERS) as [after [GUARD [FRAME [RESULT DOMAIN]]]].
      exists after; split.
      * eapply exec_Sifthenelse; [exact ROOT_TEST|exact ROOT_BOOL|].
        eapply exec_Sifthenelse; [exact CHILD_TEST|exact CHILD_BOOL|exact GUARD].
      * split; [exact FRAME|split; [exact RESULT|]].
        intro ACCEPT; split; [exact PARAMETERS|].
        rewrite <-ROW_VALUE,<-ITERATOR; apply DOMAIN; exact ACCEPT.
    + exists(PTree.set(affine_proposed_result proposal)(Vint Int.zero)temps); split.
      * eapply exec_Sifthenelse; [exact ROOT_TEST|exact ROOT_BOOL|].
        eapply exec_Sifthenelse; [exact CHILD_TEST|exact CHILD_BOOL|constructor; constructor].
      * split; [apply temp_agree_set; exact PRIVATE|split; [apply PTree.gss|discriminate]].
  - exists(PTree.set(affine_proposed_result proposal)(Vint Int.zero)temps); split.
    + eapply exec_Sifthenelse; [exact ROOT_TEST|exact ROOT_BOOL|constructor; constructor].
    + split; [apply temp_agree_set; exact PRIVATE|split; [apply PTree.gss|discriminate]].
Qed.

Theorem nested_constant_numeric_root_refusal fe ge locals temps memory root_cache child_cache result numeric :
  register_domain root_cache(Entry ge locals temps memory) ->
  register_positive root_cache(Entry ge locals temps memory)=false ->
  exec_stmt fe ge locals temps memory(nested_constant_numeric_code root_cache child_cache result numeric)
    E0(PTree.set result(Vint Int.zero)temps) memory Out_normal.
Proof.
  intros DOMAIN INACTIVE.
  destruct(@register_positive_test root_cache(Entry ge locals temps memory) DOMAIN) as [value [EVAL BOOL]].
  rewrite INACTIVE in BOOL; unfold nested_constant_numeric_code.
  eapply exec_Sifthenelse; [exact EVAL|exact BOOL|constructor; constructor].
Qed.

Theorem nested_constant_numeric_child_refusal fe ge locals temps memory root_cache child_cache result numeric :
  register_domain root_cache(Entry ge locals temps memory) -> register_domain child_cache(Entry ge locals temps memory) ->
  register_positive root_cache(Entry ge locals temps memory)=true ->
  register_positive child_cache(Entry ge locals temps memory)=false ->
  exec_stmt fe ge locals temps memory(nested_constant_numeric_code root_cache child_cache result numeric)
    E0(PTree.set result(Vint Int.zero)temps) memory Out_normal.
Proof.
  intros DOMAIN CHILD ACTIVE INACTIVE.
  destruct(@register_positive_test root_cache(Entry ge locals temps memory) DOMAIN) as [value [EVAL BOOL]].
  destruct(@register_positive_test child_cache(Entry ge locals temps memory) CHILD) as [child_value [CHILD_EVAL CHILD_BOOL]].
  rewrite ACTIVE in BOOL; rewrite INACTIVE in CHILD_BOOL; unfold nested_constant_numeric_code.
  eapply exec_Sifthenelse; [exact EVAL|exact BOOL|].
  eapply exec_Sifthenelse; [exact CHILD_EVAL|exact CHILD_BOOL|constructor; constructor].
Qed.

Print Assumptions nested_constant_numeric_guard_execution.
Print Assumptions nested_constant_numeric_root_refusal.
Print Assumptions nested_constant_numeric_child_refusal.
