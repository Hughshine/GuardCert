From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightCountedLoop
  ClightRedundantSet ClightStraightLine.
From GuardMemory Require Import GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext GuardMemoryParametricSourceDomain
  GuardMemoryParametricSourceClight GuardMemoryPointerSequence GuardMemoryMultiPointerSequence
  GuardMemoryMultiPointerIdentifiers GuardMemoryPointerSourceWords GuardMemoryAffineInnerPointerRegionSource
  GuardMemoryMultiPointerCompute.
From GuardInterface Require Import ClightLeadingEmptyRows ClightAffineSnapshotSyntax
  ClightAffineSnapshotSourceInputs ClightAffineSnapshotPreparation ClightAffineSnapshotRows
  ClightAffineSnapshotPrefix ClightAffinePreparedState ClightLoadedBoundSyntax ClightWordReadSnapshots
  ClightAffineHeaderSnapshots.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section SOURCE.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let source:=snapshot_cached_source site.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Let row:=affine_inner_pointer_row shape.
Let column:=affine_inner_pointer_column shape.
Let inner_bound:=affine_inner_pointer_inner_bound shape.
Let cache:=affine_inner_pointer_bound shape.
Let root:=snapshot_root site.
Let child:=snapshot_child site.
Let child_cache:=snapshot_child_cache site.
Let header:=snapshot_original_header site.
Let body:=affine_inner_pointer_body shape.
Let expression:=affine_inner_pointer_expression package.
Let stable:=affine_snapshot_stable package root child.
Let CERT:=affine_inner_pointer_syntax package.
Let body_inputs:=affine_inner_pointer_body_parameters package++affine_inner_pointer_scalars package.

Lemma snapshot_later_protected identifier : In identifier stable ->
  identifier<>row /\ identifier<>column /\ identifier<>inner_bound.
Proof.
  exact(@affine_snapshot_protected source package root child
    (snapshot_root_protected site)(snapshot_child_protected site)identifier).
Qed.

Lemma snapshot_later_header_exact : snapshot_word_replace(single_snapshot_binding child child_cache)header=
  memory_source_affine_code expression.
Proof.
  pose proof(affine_inner_pointer_outer_exact CERT)as EXACT.
  unfold shape,package in EXACT.
  rewrite(snapshot_cached_body_exact site)in EXACT.
  apply(f_equal(hd Sskip))in EXACT.
  cbn [affine_snapshot_body affine_setup_child flatten_region memory_parametric_setup app hd]in EXACT.
  inversion EXACT; assumption.
Qed.

(** Header observations and pure parameters are sufficient here. No scalar or
    address input used only by the leaf is assumed to be defined. *)
Theorem snapshot_later_header_value fe entry i current :
  affine_snapshot_original_domain package root child child_cache header fe entry ->
  (entry_temps entry)!row=Some(Vint Int.zero) -> 0<affine_prepared_count package entry ->
  current!row=Some(Vint(Int.repr i)) -> temp_agree stable(entry_temps entry)current ->
  eval_expr(entry_ge entry)(entry_env entry)current(entry_memory entry)header
    (Vint(Int.repr(affine_prepared_upper package entry i))).
Proof.
  intros DOMAIN ZERO COUNT ROW FRAME.
  destruct(@affine_snapshot_header_words source package root child child_cache header
    (snapshot_header_word site)(snapshot_cached_body_exact site)fe entry DOMAIN)as [R [CACHE WORDS]].
  assert(CHILD:cached_signed_read child child_cache entry).
  { apply(proj1(proj2 DOMAIN)); apply(@affine_snapshot_zero_active source package entry CACHE ZERO COUNT). }
  assert(RECEIPTS:snapshot_word_receipts(single_snapshot_binding child child_cache)header
    (entry_ge entry)(entry_env entry)current(entry_memory entry)).
  { exact(@single_snapshot_receipts header child child_cache stable entry current(entry_memory entry)
      (or_introl eq_refl)(snapshot_cache_member site)CHILD FRAME(cached_signed_initial_observations CHILD)). }
  apply(proj2(@snapshot_word_replacement_evaluation header(snapshot_header_word site)
    (single_snapshot_binding child child_cache)(entry_ge entry)(entry_env entry)current(entry_memory entry)
    (Vint(Int.repr(affine_prepared_upper package entry i)))RECEIPTS)).
  rewrite snapshot_later_header_exact,affine_prepared_upper_math.
  eapply memory_source_affine_iteration_value with(base:=entry_temps entry).
  - exact ROW.
  - intros identifier MEMBER; apply memory_source_affine_parameter_member in MEMBER as [READ OTHER].
    destruct(WORDS ZERO COUNT identifier READ)as [word WORD].
    unfold affine_prepared_valuation,temp_word; rewrite WORD,Int.repr_signed; reflexivity.
  - eapply temp_agree_weaken; [|exact FRAME].
    intros identifier MEMBER; apply memory_source_affine_parameter_member in MEMBER as [READ OTHER].
    unfold stable,affine_snapshot_stable,affine_prepared_stable,affine_prepared_body_stable.
    right; right; apply in_or_app; right.
    unfold memory_affine_inner_pointer_region_context; apply in_or_app; left.
    unfold memory_affine_inner_pointer_parameters; apply in_or_app; left.
    apply memory_source_context_read; assumption.
Qed.

Lemma snapshot_later_root_active entry i current :
  cached_signed_read root cache entry -> 0<=i<affine_prepared_count package entry ->
  current!row=Some(Vint(Int.repr i)) -> temp_agree stable(entry_temps entry)current ->
  expression_test(loaded_bound_test row root)(Entry(entry_ge entry)(entry_env entry)current(entry_memory entry))true.
Proof.
  intros ROOT RANGE ROW FRAME.
  destruct(@cached_signed_current_read root cache stable entry current(entry_memory entry)
    (or_intror(or_introl eq_refl))(@affine_snapshot_root_cache_member source package root child)
    ROOT FRAME(cached_signed_initial_observations ROOT))as [word [CACHE READ]].
  assert(ENTRY_CACHE:(entry_temps entry)!cache=Some(Vint word)).
  { rewrite FRAME in CACHE by(apply affine_snapshot_root_cache_member); exact CACHE. }
  unfold affine_prepared_count,affine_prepared_valuation in RANGE; fold shape cache in RANGE.
  unfold temp_word in RANGE; rewrite ENTRY_CACHE in RANGE.
  assert(SAFE:signed_range i).
  { pose proof(Int.signed_range word); unfold signed_range; change Int.min_signed with(-2147483648)in *; lia. }
  assert(FLAG:Int.lt(Int.repr i)word=true).
  { unfold Int.lt; rewrite Int.signed_repr by exact SAFE; destruct(zlt i(Int.signed word)); [reflexivity|lia]. }
  rewrite <-FLAG; destruct(signed_load_inv READ)as [block [offset [POINTER LOAD]]].
  eapply loaded_bound_test_eval; eassumption.
Qed.

(** The ordinary skip count is an optimizer/domain proposal. Its finite empty
    prefix and active next child are word predicates over licensed headers.
    This theorem produces the actual later leaf and its entry-memory receipt. *)
Theorem affine_snapshot_later_leaf_receipt fe entry skip :
  affine_snapshot_original_domain package root child child_cache header fe entry ->
  (entry_temps entry)!row=Some(Vint Int.zero) -> 0<=Z.of_nat skip<affine_prepared_count package entry ->
  (forall i,0<=i<Z.of_nat skip -> Int.lt Int.zero(Int.repr(affine_prepared_upper package entry i))=false) ->
  Int.lt Int.zero(Int.repr(affine_prepared_upper package entry(Z.of_nat skip)))=true ->
  exists leaf after final,temp_agree stable(entry_temps entry)leaf /\
    exec_stmt fe(entry_ge entry)(entry_env entry)leaf(entry_memory entry)body E0 after final Out_normal.
Proof.
  intros DOMAIN ZERO RANGE EMPTY POSITIVE.
  destruct(proj2(proj2 DOMAIN))as [after [final SOURCE]].
  pose proof(@memory_pointer_sequence_quiet(affine_inner_pointer_operations package)body
    (affine_inner_pointer_body_exact CERT))as QUIET.
  destruct(@leading_empty_rows_body_receipt fe(entry_ge entry)(entry_env entry)(entry_temps entry)
    (entry_memory entry)row column inner_bound(loaded_bound_test row root)header body stable
    (affine_prepared_count package entry)(affine_inner_pointer_ck CERT)(affine_inner_pointer_rc CERT)
    (affine_inner_pointer_rk CERT)QUIET snapshot_later_protected
    ltac:(unfold affine_prepared_count,affine_prepared_valuation; exact(proj2(Int.signed_range _)))
    ltac:(intros i current I ROW FRAME; exact(@snapshot_later_root_active entry i current(proj1 DOMAIN)I ROW FRAME))
    skip after final RANGE ZERO
    ltac:(intros i current I ROW FRAME; exists(Int.repr(affine_prepared_upper package entry i)); split;
      [eapply snapshot_later_header_value; [exact DOMAIN|exact ZERO|lia|exact ROW|exact FRAME]|apply EMPTY; exact I])SOURCE)
    as [reached [next [last [ROW [FRAME BODY]]]]].
  destruct(@affine_setup_active_child_receipt fe(entry_ge entry)(entry_env entry)reached(entry_memory entry)
    column inner_bound header body(Int.repr(affine_prepared_upper package entry(Z.of_nat skip)))next last stable
    (affine_inner_pointer_ck CERT)
    (@memory_pointer_sequence_normal(affine_inner_pointer_operations package)body(affine_inner_pointer_body_exact CERT))
    QUIET ltac:(intros identifier MEMBER; exact(proj2(snapshot_later_protected MEMBER)))
    (@snapshot_later_header_value fe entry(Z.of_nat skip)reached DOMAIN ZERO ltac:(lia)ROW FRAME)
    POSITIVE BODY)as [leaf [leaf_after [leaf_final [LEAF_FRAME LEAF]]]].
  exists leaf,leaf_after,leaf_final; split; [eapply temp_agree_trans; eassumption|exact LEAF].
Qed.

Theorem affine_snapshot_later_body_words fe entry skip :
  affine_snapshot_original_domain package root child child_cache header fe entry ->
  (entry_temps entry)!row=Some(Vint Int.zero) -> 0<=Z.of_nat skip<affine_prepared_count package entry ->
  (forall i,0<=i<Z.of_nat skip -> Int.lt Int.zero(Int.repr(affine_prepared_upper package entry i))=false) ->
  Int.lt Int.zero(Int.repr(affine_prepared_upper package entry(Z.of_nat skip)))=true ->
  forall identifier,In identifier body_inputs -> exists word,(entry_temps entry)!identifier=Some(Vint word).
Proof.
  intros DOMAIN ZERO RANGE EMPTY POSITIVE.
  destruct(@affine_snapshot_later_leaf_receipt fe entry skip DOMAIN ZERO RANGE EMPTY POSITIVE)
    as [leaf [after [final [FRAME LEAF]]]].
  pose proof(affine_inner_pointer_body_exact CERT)as BODY_EXACT; fold shape body in BODY_EXACT.
  apply flatten_region_execution in LEAF; rewrite BODY_EXACT in LEAF.
  assert(MEMBER_STABLE:forall identifier,In identifier body_inputs -> In identifier stable).
  { intros identifier MEMBER; unfold stable,affine_snapshot_stable,affine_prepared_stable,affine_prepared_body_stable.
    right; right; apply in_or_app; right; unfold memory_affine_inner_pointer_region_context.
    unfold body_inputs in MEMBER; apply in_app_or in MEMBER as [ADDRESS|SCALAR].
    - apply in_or_app; left; unfold memory_affine_inner_pointer_parameters; apply in_or_app; right; exact ADDRESS.
    - apply in_or_app; right; exact SCALAR. }
  intros identifier MEMBER; pose proof(MEMBER_STABLE identifier MEMBER)as STABLE.
  unfold body_inputs in MEMBER; apply in_app_or in MEMBER as [ADDRESS|SCALAR].
  - destruct(affine_inner_pointer_body_parameters_used CERT identifier ADDRESS)as [operation [USED READ]].
    destruct(@memory_pointer_sequence_address_words _ _ _ _ _ fe(entry_ge entry)(entry_env entry)identifier
      (affine_inner_pointer_operations_valid CERT)leaf(entry_memory entry)after final LEAF operation USED READ)
      as [word WORD].
    exists word; rewrite FRAME in WORD by exact STABLE; exact WORD.
  - destruct(affine_inner_pointer_scalars_used CERT identifier SCALAR)as [operation [index [USED [LOOKUP READ]]]].
    destruct(@memory_multi_pointer_sequence_used_register _ _ _ _ _ fe(entry_ge entry)(entry_env entry)identifier index
      (affine_inner_pointer_operations_valid CERT)LOOKUP leaf(entry_memory entry)after final LEAF operation USED READ)
      as [word WORD].
    exists word; rewrite FRAME in WORD by exact STABLE; exact WORD.
Qed.
End SOURCE.

Print Assumptions snapshot_later_protected.
Print Assumptions snapshot_later_header_exact.
Print Assumptions snapshot_later_header_value.
Print Assumptions snapshot_later_root_active.
Print Assumptions affine_snapshot_later_leaf_receipt.
Print Assumptions affine_snapshot_later_body_words.
