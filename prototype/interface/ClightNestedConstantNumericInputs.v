From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightNoWrap ClightRegionProgress
  ClightPureExpr ClightRedundantSet ClightRectangularGuard.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode AffineNestLeafModel
  AffineNestUsedWords AffineNestGuardWords AffineNestBoundWords AffineNestGuardParameterCheck
  AffineNestGuardPackage AffineNestPackageGuard AffineNestValuation AffineNestMathDomain AffineNestNamespace.
From GuardInterface Require Import ClightConstantBoundModel ClightNestedExpressionCapture ClightNestedExpressionPrefix ClightNestedConstantModel
  ClightNestedConstantFirstLeaf ClightCapturedAffineNumericGuard ClightAffineNestMaterialized.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Every parameter the old checker admits is either an actual captured
    header word or used by the actual first leaf. This producer needs only
    the original source, even when its first store changes a later bound. *)
Theorem nested_constant_original_parameter_domains row root_cache column child_cache child_helper iterator component_helper
  upper body parameters live proposal
  (package:affine_guard_package
    (nested_constant_model_source row root_cache column child_cache child_helper iterator component_helper upper body)
    parameters live proposal)
  fe ge locals bound child_bound root_word child_word temps memory after final :
  affine_proposal_nest proposal=nested_constant_model_nest row root_cache column child_cache child_helper
    iterator component_helper upper body(AffineSourceLeaf body) ->
  typeof bound=type_int32s -> typeof child_bound=type_int32s -> ~In column(expression_temps child_bound) ->
  temps!root_cache=Some(Vint root_word) -> temps!child_cache=Some(Vint child_word) ->
  eval_expr ge locals temps memory bound(Vint root_word) ->
  eval_expr ge locals temps memory child_bound(Vint child_word) ->
  Int.lt(temp_word row temps) root_word=true -> Int.lt Int.zero child_word=true ->
  Int.lt Int.zero(Int.repr upper)=true ->
  exec_stmt fe ge locals temps memory
    (nested_expression_source row bound column child_bound(constant_body_source iterator(Int.repr upper) body))
    E0 after final Out_normal ->
  Forall(fun identifier=>register_domain identifier(Entry ge locals temps memory)) parameters.
Proof.
  intros NEST TYPE CHILD_TYPE COLUMN_PRIVATE CACHE CHILD_CACHE ROOT CHILD ROOT_ACTIVE CHILD_ACTIVE LITERAL_ACTIVE SOURCE.
  pose proof(affine_package_leaf package) as LEAF_CERTIFICATE; rewrite NEST in LEAF_CERTIFICATE.
  cbn [nested_constant_model_nest affine_nest_leaf] in LEAF_CERTIFICATE.
  destruct(@nested_constant_original_first_leaf fe ge locals row bound column child_bound iterator(Int.repr upper)
    body temps memory after final root_word child_word TYPE CHILD_TYPE
    (affine_leaf_normal LEAF_CERTIFICATE)(affine_leaf_quiet LEAF_CERTIFICATE)
    COLUMN_PRIVATE ROOT CHILD ROOT_ACTIVE CHILD_ACTIVE LITERAL_ACTIVE SOURCE)
    as [leaf_after [leaf_final LEAF_SOURCE]].
  apply Forall_forall; intros identifier MEMBER.
  destruct(peq identifier root_cache) as [SAME|NOT_ROOT]; [subst; exists root_word; exact CACHE|].
  destruct(peq identifier child_cache) as [SAME|NOT_CHILD]; [subst; exists child_word; exact CHILD_CACHE|].
  destruct(@check_affine_guard_parameters_sound _ _ _ _ _ (affine_package_used package) identifier MEMBER)
    as [USED UNWRITTEN]; rewrite NEST in USED,UNWRITTEN.
  cbn [affine_guard_register_used affine_tail_bound_reads memory_source_affine_reads nested_constant_model_nest] in USED.
  destruct USED as [SAME|[BOUND|LEAF_USED]]; [contradiction|cbn in BOUND; intuition congruence|].
  destruct(@affine_leaf_actual_used_word _ _ _ _ _ _ _ _ LEAF_CERTIFICATE fe ge locals
    (PTree.set iterator(Vint Int.zero)(PTree.set column(Vint Int.zero)temps)) memory
    leaf_after leaf_final identifier LEAF_USED LEAF_SOURCE) as [word WORD].
  exists word.
  rewrite !PTree.gso in WORD by
    (intro SAME; subst identifier; apply UNWRITTEN;
      cbn [nested_constant_model_nest affine_nest_mutated affine_nest_controls List.In]; intuition congruence).
  exact WORD.
Qed.

Definition nested_constant_point_valuation temps row column i j :=
  memory_source_set_valuation(memory_source_set_valuation(affine_word_valuation temps) row i) column j.

Lemma nested_constant_point_words parameters temps row column i j ge locals memory :
  row<>column -> ~In row parameters -> ~In column parameters ->
  Forall(fun identifier=>register_domain identifier(Entry ge locals temps memory)) parameters ->
  affine_word_view([row;column]++parameters)(nested_constant_point_valuation temps row column i j)
    (PTree.set column(Vint(Int.repr j))(PTree.set row(Vint(Int.repr i))temps)).
Proof.
  intros DISTINCT ROW_PRIVATE COLUMN_PRIVATE DEFINED identifier MEMBER.
  unfold nested_constant_point_valuation,memory_source_set_valuation.
  destruct(peq identifier column) as [SAME|NOT_COLUMN]; [subst; apply PTree.gss|].
  rewrite PTree.gso by congruence.
  destruct(peq identifier row) as [SAME|NOT_ROW]; [subst; apply PTree.gss|].
  rewrite PTree.gso by congruence.
  cbn in MEMBER; destruct MEMBER as [SAME|[SAME|PARAMETER]]; [congruence|congruence|].
  apply Forall_forall with(x:=identifier) in DEFINED; [|exact PARAMETER].
  destruct DEFINED as [word WORD]; cbn [entry_temps] in WORD.
  unfold affine_word_valuation,temp_word; rewrite WORD,Int.repr_signed; reflexivity.
Qed.

Lemma nested_constant_inner_point_words parameters entry row column i j :
  row<>column -> ~In row parameters -> ~In column parameters ->
  Forall(fun identifier=>register_domain identifier entry) parameters ->
  affine_word_view([row;column]++parameters)(nested_constant_point_valuation(entry_temps entry) row column i j)
    (PTree.set column(Vint(Int.repr j))(entry_temps(nested_expression_inner_entry row column i entry))).
Proof.
  destruct entry as [ge locals temps memory]; intros DISTINCT ROW_PRIVATE COLUMN_PRIVATE DEFINED.
  cbn [nested_expression_inner_entry entry_temps]; rewrite PTree.set2.
  eapply nested_constant_point_words; eassumption.
Qed.

Lemma nested_constant_point_column temps row column i j :
  nested_constant_point_valuation temps row column i j column=j.
Proof.
  unfold nested_constant_point_valuation,memory_source_set_valuation.
  destruct(peq column column); congruence.
Qed.

Lemma nested_constant_point_other temps row column i j identifier :
  identifier<>column -> nested_constant_point_valuation temps row column i j identifier=
    nested_constant_point_valuation temps row column i 0 identifier.
Proof.
  intro DISTINCT; unfold nested_constant_point_valuation,memory_source_set_valuation.
  destruct(peq identifier column); congruence.
Qed.

Lemma nested_constant_numeric_point_domain row root_cache column child_cache child_helper iterator component_helper
  upper body bounds parameters temps i j :
  row<>child_cache ->
  affine_math_domain bounds([row;column;iterator]++parameters)
    (nested_constant_model_nest row root_cache column child_cache child_helper iterator component_helper upper body
      (AffineSourceLeaf body)) (affine_word_valuation temps) 0 ->
  0<=i<affine_word_valuation temps root_cache -> 0<=j<affine_word_valuation temps child_cache ->
  affine_math_domain bounds([row;column;iterator]++parameters)
    (AffineSourceAxis iterator component_helper(MemorySourceConstant upper) body(AffineSourceLeaf body))
    (nested_constant_point_valuation temps row column i j) 0.
Proof.
  intros DISTINCT DOMAIN ROWS COLUMNS.
  cbn [nested_constant_model_nest affine_math_domain memory_source_affine_math] in DOMAIN.
  destruct DOMAIN as [_ [_ ALL_ROWS]]; specialize(ALL_ROWS i ROWS).
  destruct ALL_ROWS as [_ [_ ALL_COLUMNS]].
  unfold memory_source_set_valuation in ALL_COLUMNS at 1.
  destruct(peq child_cache row); [congruence|].
  exact(ALL_COLUMNS j COLUMNS).
Qed.

Definition nested_constant_scan_inputs row root_cache column child_cache iterator component_helper upper body
  parameters bounds entry := forall i j,
  0<=i<affine_word_valuation(entry_temps entry) root_cache ->
  0<=j<affine_word_valuation(entry_temps entry) child_cache ->
  affine_math_domain bounds([row;column;iterator]++parameters)
    (AffineSourceAxis iterator component_helper(MemorySourceConstant upper) body(AffineSourceLeaf body))
    (nested_constant_point_valuation(entry_temps entry) row column i j) 0 /\
  affine_word_view([row;column]++parameters)
    (nested_constant_point_valuation(entry_temps entry) row column i j)
    (PTree.set column(Vint(Int.repr j))(entry_temps(nested_expression_inner_entry row column i entry))).

(** Package layout uniqueness supplies coordinate/parameter separation.
    These are the DOMAIN and SOURCE_WORDS inputs of the existing outer scan. *)
Theorem nested_constant_package_scan_inputs row root_cache column child_cache child_helper iterator component_helper
  upper body parameters live proposal
  (package:affine_guard_package
    (nested_constant_model_source row root_cache column child_cache child_helper iterator component_helper upper body)
    parameters live proposal) entry :
  affine_proposal_nest proposal=nested_constant_model_nest row root_cache column child_cache child_helper
    iterator component_helper upper body(AffineSourceLeaf body) ->
  row<>child_cache ->
  Forall(fun identifier=>register_domain identifier entry) parameters ->
  affine_math_domain(affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)
    (affine_proposal_nest proposal)(affine_word_valuation(entry_temps entry)) 0 ->
  nested_constant_scan_inputs row root_cache column child_cache iterator component_helper upper body
    parameters(affine_proposed_leaf_bounds proposal) entry.
Proof.
  intros NEST DISTINCT DEFINED DOMAIN.
  pose proof(affine_leaf_unique(affine_package_leaf package)) as FRESH.
  unfold affine_proposal_layout in FRESH,DOMAIN; rewrite NEST in FRESH,DOMAIN.
  cbn [nested_constant_model_nest affine_nest_iterators app] in FRESH.
  rewrite app_nil_r in FRESH.
  apply NoDup_cons_iff in FRESH as [ROW_PRIVATE REST].
  apply NoDup_cons_iff in REST as [COLUMN_PRIVATE REST].
  assert (ROW_COLUMN : row<>column) by(intro SAME; subst column; apply ROW_PRIVATE; cbn; auto).
  assert (ROW_PARAMETERS : ~In row parameters) by(cbn in ROW_PRIVATE; tauto).
  assert (COLUMN_PARAMETERS : ~In column parameters) by(cbn in COLUMN_PRIVATE; tauto).
  intros i j ROWS COLUMNS; split.
  - eapply nested_constant_numeric_point_domain with (root_cache:=root_cache)
      (child_cache:=child_cache)(child_helper:=child_helper); eassumption.
  - eapply nested_constant_inner_point_words; eassumption.
Qed.

Print Assumptions nested_constant_original_parameter_domains.
Print Assumptions nested_constant_point_words.
Print Assumptions nested_constant_inner_point_words.
Print Assumptions nested_constant_point_column.
Print Assumptions nested_constant_point_other.
Print Assumptions nested_constant_numeric_point_domain.
Print Assumptions nested_constant_package_scan_inputs.
