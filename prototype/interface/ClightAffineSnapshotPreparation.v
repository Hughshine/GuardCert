From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightTempFrame
  ClightTempFootprint ClightLoopSyntax ClightRegionProgress ClightStraightLine
  ClightCountedLoop ClightFrontendLoopProtocol ClightRectangularLoops ClightRedundantSet.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryNaryRanges
  GuardMemoryRecursiveSource GuardMemoryScalarPointerBody GuardMemorySourceParameters
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext
  GuardMemoryParametricSourceDomain GuardMemoryParametricSourceClight GuardMemoryParametricFirstBody
  GuardMemoryParametricWidth GuardMemoryParametricGuard GuardMemoryPointerSequence
  GuardMemoryAffinePointerBody GuardMemoryMultiPointerSequence GuardMemoryMultiPointerCells
  GuardMemoryMultiPointerCompute GuardMemoryMultiPointerIdentifiers GuardMemoryPointerSourceWords
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain GuardMemoryAffineInnerPointerRegionSource.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictLoopProgress ClightStrictIteration
  ClightWordReadSnapshots ClightAffineHeaderSnapshots ClightAffineSnapshotRows ClightAffineSnapshotSourceInputs
  ClightExpressionHeaderCapture ClightAffinePreparationEvidence ClightAffineInnerPointerSourceGuard
  ClightReadonlyLoadedTreeSynthesis GuardedRewrite ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ClightAffinePointerGuard ClightAffinePointerSourcePreparation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section PREPARATION.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root child child_cache : ident.
Variable header : expr.
Let shape := affine_inner_pointer_shape package.
Let row := affine_inner_pointer_row shape.
Let bound := affine_inner_pointer_bound shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let body := affine_inner_pointer_body shape.
Let outer_body := affine_inner_pointer_outer_body shape.
Let expression := affine_inner_pointer_expression package.
Let parameters := memory_affine_inner_pointer_parameters shape expression(affine_inner_pointer_body_parameters package).
Let scalars := affine_inner_pointer_scalars package.
Let CERT := affine_inner_pointer_syntax package.
Let D fe := affine_snapshot_original_domain package root child child_cache header fe.
Hypothesis HEADER_WORD : snapshot_word_expression header.
Hypothesis CACHED_BODY : outer_body =
  affine_snapshot_body package(snapshot_word_replace(single_snapshot_binding child child_cache)header).

Lemma affine_snapshot_initial_words fe entry : D fe entry -> register_domain row entry /\ register_domain bound entry.
Proof.
  intros [[block [offset [word [POINTER [CACHE READ]]]]] [CHILD [after [final SOURCE]]]].
  destruct(signed_expression_completed_header SOURCE)as [flag TEST].
  destruct(loaded_bound_test_facts TEST)as [counter [upper [b [o [ROW REST]]]]].
  split; [exists counter; exact ROW|exists word; exact CACHE].
Qed.

(** Only the reached first row is changed for this receipt. No transport of a
    complete cached loop, or preservation of later headers, is assumed. *)
Theorem affine_snapshot_first_cached_row fe entry :
  D fe entry -> Int.lt(temp_word row(entry_temps entry))(temp_word bound(entry_temps entry))=true ->
  exists after final,
    exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      outer_body E0 after final Out_normal.
Proof.
  intros [ROOT [CHILD [after [final SOURCE]]]] ACTIVE.
  pose proof(CHILD ACTIVE)as CHILD_READ.
  destruct ROOT as [block [offset [word [POINTER [CACHE READ]]]]].
  destruct(signed_expression_completed_header SOURCE)as [flag TEST].
  destruct(loaded_bound_test_facts TEST)as [counter [upper [b [o [ROW [POINTER' [READ' FLAG]]]]]]].
  assert(ADDRESS:Vptr b o=Vptr block offset)by congruence.
  injection ADDRESS as BLOCK OFFSET; subst b o.
  assert(UPPER:upper=word)by congruence; subst upper.
  fold shape row in ROW; fold shape bound in CACHE.
  unfold temp_word in ACTIVE; rewrite ROW,CACHE in ACTIVE; rewrite FLAG,ACTIVE in TEST.
  assert(QUIET:quiet_statement body=true).
  { exact(@memory_pointer_sequence_quiet(affine_inner_pointer_operations package)body(affine_inner_pointer_body_exact CERT)). }
  destruct(@strict_active_iteration fe(entry_ge entry)(entry_env entry)row(loaded_bound_test row root)
    (affine_snapshot_body package header)(entry_temps entry)(entry_memory entry)after final
    (@affine_setup_child_normal column inner_bound header body QUIET)
    (@affine_setup_child_quiet column inner_bound header body QUIET)TEST SOURCE)
    as [body_after [body_final [next [next_memory [BODY REST]]]]].
  assert(RECEIPTS:snapshot_word_receipts(single_snapshot_binding child child_cache)header
    (entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)).
  { exact(@single_snapshot_receipts header child child_cache [child;child_cache] entry(entry_temps entry)(entry_memory entry)
      (or_introl eq_refl)(or_intror(or_introl eq_refl))CHILD_READ(temp_agree_refl _ _)
      (cached_signed_initial_observations CHILD_READ)). }
  exists body_after,body_final; rewrite CACHED_BODY; unfold affine_snapshot_body,affine_setup_child in BODY|-*.
  apply(proj1(@snapshot_word_setup_execution fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    inner_bound header(Ssequence(rectangle_reset column)(frontend_counted_loop column inner_bound body))
    (single_snapshot_binding child child_cache)E0 body_after body_final Out_normal HEADER_WORD RECEIPTS)); exact BODY.
Qed.

Lemma affine_snapshot_zero_active entry : register_domain bound entry ->
  (entry_temps entry)!row=Some(Vint Int.zero) -> 0<Int.signed(temp_word bound(entry_temps entry)) ->
  Int.lt(temp_word row(entry_temps entry))(temp_word bound(entry_temps entry))=true.
Proof.
  intros [word CACHE] ZERO POSITIVE; unfold temp_word in *; rewrite CACHE in *; rewrite ZERO.
  unfold Int.lt; rewrite Int.signed_zero; destruct(zlt 0(Int.signed word)); [reflexivity|lia].
Qed.

Theorem affine_snapshot_header_words fe entry : D fe entry ->
  register_domain row entry /\ register_domain bound entry /\
  ((entry_temps entry)!row=Some(Vint Int.zero) -> 0<Int.signed(temp_word bound(entry_temps entry)) ->
    forall identifier,In identifier(memory_source_affine_reads expression) ->
      exists word,(entry_temps entry)!identifier=Some(Vint word)).
Proof.
  intro DOMAIN; destruct(affine_snapshot_initial_words DOMAIN)as [ROW BOUND].
  split; [exact ROW|split; [exact BOUND|]].
  intros ZERO POSITIVE; destruct(affine_snapshot_first_cached_row DOMAIN
    (affine_snapshot_zero_active BOUND ZERO POSITIVE))as [after [final BODY]].
  eapply memory_parametric_outer_source_words;
    [exact(affine_inner_pointer_ck CERT)|exact(affine_inner_pointer_outer_exact CERT)|exact BODY].
Qed.

Theorem affine_snapshot_body_words fe entry :
  D fe entry -> memory_affine_inner_pointer_header_accept shape(affine_inner_pointer_row_limit package)entry=true ->
  memory_affine_inner_pointer_width_property shape expression(affine_inner_pointer_column_limit package)entry ->
  forall identifier,In identifier(affine_inner_pointer_body_parameters package++scalars) ->
    exists word,(entry_temps entry)!identifier=Some(Vint word).
Proof.
  intros DOMAIN ACCEPT WIDTH.
  destruct(affine_snapshot_header_words DOMAIN)as [ROW [BOUND WORDS]].
  assert(ROW_CAP:signed_range(affine_inner_pointer_row_limit package)).
  { pose proof(affine_inner_pointer_control_limits CERT)as CAPS; inversion CAPS; subst; tauto. }
  assert(COLUMN_CAP:signed_range(affine_inner_pointer_column_limit package)).
  { pose proof(affine_inner_pointer_control_limits CERT)as CAPS.
    apply Forall_forall with(x:=affine_inner_pointer_column_limit package)in CAPS;
      [exact(proj2 CAPS)|right; left; reflexivity]. }
  destruct(@memory_affine_inner_pointer_header_sound shape(affine_inner_pointer_row_limit package)entry
    ROW_CAP ROW BOUND ACCEPT)as [ZERO [_ POSITIVE]].
  destruct BOUND as [n NLOOK].
  set(valuation:=memory_source_word_valuation(entry_temps entry)).
  set(rows:=Int.signed n).
  set(upper:=memory_source_affine_math(memory_source_set_valuation valuation row 0)expression).
  assert(N:valuation bound=rows)by(unfold valuation,rows,memory_source_word_valuation; rewrite NLOOK; reflexivity).
  assert(POS:0<rows).
  { change(0<Int.signed(temp_word bound(entry_temps entry))<=affine_inner_pointer_row_limit package)in POSITIVE.
    unfold temp_word in POSITIVE; rewrite NLOOK in POSITIVE; tauto. }
  assert(INNER:0<upper /\ signed_range upper).
  { change(0<upper /\ forall i,0<=i<valuation bound ->
      0<=memory_source_affine_math(memory_source_set_valuation valuation row i)expression
        <=affine_inner_pointer_column_limit package)in WIDTH.
    destruct WIDTH as [FIRST ALL]; pose proof(ALL 0 ltac:(rewrite N; lia))as RANGE.
    unfold signed_range in *; change Int.min_signed with(-2147483648)in *; split; [exact FIRST|lia]. }
  assert(VALUE:eval_expr(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (memory_source_affine_code expression)(Vint(Int.repr upper))).
  { eapply memory_source_affine_iteration_value with(base:=entry_temps entry)(value:=0)(valuation:=valuation).
    - exact ZERO.
    - intros identifier MEMBER; apply memory_source_affine_parameter_member in MEMBER.
      destruct(WORDS ZERO(proj1 POSITIVE)identifier(proj1 MEMBER))as [word LOOK].
      unfold valuation,memory_source_word_valuation; rewrite LOOK,Int.repr_signed; reflexivity.
    - apply temp_agree_refl. }
  destruct(affine_snapshot_first_cached_row DOMAIN
    (affine_snapshot_zero_active ltac:(exists n; exact NLOOK)ZERO(proj1 POSITIVE)))as [after [final BODY]].
  assert(PROTECTED:forall identifier,In identifier(affine_inner_pointer_body_parameters package++scalars) ->
    identifier<>column /\ identifier<>inner_bound).
  { intros identifier MEMBER.
    assert(ALL:In identifier(affine_inner_pointer_pointers package++(parameters++scalars))).
    { apply in_or_app; right; apply in_app_or in MEMBER as [BODY_PARAM|SCALAR].
      - apply in_or_app; left; unfold parameters,memory_affine_inner_pointer_parameters;
          apply in_or_app; right; exact BODY_PARAM.
      - apply in_or_app; right; exact SCALAR. }
    pose proof(affine_inner_pointer_protected CERT ALL)as FRESH.
    split; intro SAME; apply FRESH; subst identifier; cbn; auto. }
  destruct(@memory_parametric_first_inner_body fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    column inner_bound(memory_source_affine_code expression)upper body outer_body after final
    (affine_inner_pointer_body_parameters package++scalars)(affine_inner_pointer_ck CERT)
    (@memory_pointer_sequence_normal(affine_inner_pointer_operations package)body(affine_inner_pointer_body_exact CERT))
    (@memory_pointer_sequence_writes(affine_inner_pointer_operations package)body(affine_inner_pointer_body_exact CERT))
    (memory_source_affine_pure expression)VALUE(proj1 INNER)(proj2 INNER)PROTECTED
    (affine_inner_pointer_outer_exact CERT)BODY)
    as [leaf [leaf_after [leaf_final [FRAME LEAF]]]].
  pose proof(affine_inner_pointer_body_exact CERT)as BODY_EXACT; fold shape body in BODY_EXACT.
  apply flatten_region_execution in LEAF; rewrite BODY_EXACT in LEAF.
  intros identifier MEMBER; apply in_app_iff in MEMBER as [ADDRESS|SCALAR].
  - destruct(affine_inner_pointer_body_parameters_used CERT identifier ADDRESS)as [operation [USED READ]].
    destruct(@memory_pointer_sequence_address_words _ _ _ _ _ fe(entry_ge entry)(entry_env entry)identifier
      (affine_inner_pointer_operations_valid CERT)leaf(entry_memory entry)leaf_after leaf_final LEAF operation USED READ)
      as [word WORD].
    exists word; rewrite FRAME in WORD by(apply in_or_app; left; exact ADDRESS); exact WORD.
  - destruct(affine_inner_pointer_scalars_used CERT identifier SCALAR)as [operation [index [USED [LOOKUP READ]]]].
    destruct(@memory_multi_pointer_sequence_used_register _ _ _ _ _ fe(entry_ge entry)(entry_env entry)identifier index
      (affine_inner_pointer_operations_valid CERT)LOOKUP leaf(entry_memory entry)leaf_after leaf_final LEAF operation USED READ)
      as [word WORD].
    exists word; rewrite FRAME in WORD by(apply in_or_app; right; exact SCALAR); exact WORD.
Qed.

Definition affine_snapshot_preparation_evidence fe :
  affine_preparation_evidence shape expression(affine_inner_pointer_row_limit package)(affine_inner_pointer_column_limit package)
    (affine_inner_pointer_body_parameters package)scalars(D fe) :=
  {| preparation_entry_words:=@affine_snapshot_header_words fe;
     preparation_body_words:=@affine_snapshot_body_words fe |}.
End PREPARATION.

Section CONDITION.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root child child_cache : ident.
Variable header : expr.
Hypothesis HEADER_WORD : snapshot_word_expression header.
Hypothesis CACHED_BODY : affine_inner_pointer_outer_body(affine_inner_pointer_shape package)=
  affine_snapshot_body package(snapshot_word_replace(single_snapshot_binding child child_cache)header).
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variable width_tree : decision_tree.
Hypothesis WIDTH : compile_memory_source_width(affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row(affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header(affine_inner_pointer_shape package)(affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds(affine_inner_pointer_row_limit package)(affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package)=Some width_tree.
Let D := affine_snapshot_original_domain package root child child_cache header fe.
Let E := @affine_snapshot_preparation_evidence source package root child child_cache header HEADER_WORD CACHED_BODY fe.

(** The original-source producer now feeds the existing ordered arithmetic
    guard, rather than merely exposing a record that callers must fill. *)
Definition affine_snapshot_preparation_condition :
  readonly_condition(readonly_clight_host fe observe)D(affine_inner_pointer_ready package)
    (affine_inner_pointer_package_preparation_tree package width_tree).
Proof.
  pose proof(@affine_evidence_preparation_condition source(affine_inner_pointer_shape package)
    (affine_inner_pointer_expression package)(affine_inner_pointer_encoded package)
    (affine_inner_pointer_row_limit package)(affine_inner_pointer_column_limit package)
    (affine_inner_pointer_header_limits package)(affine_inner_pointer_body_limits package)
    (affine_inner_pointer_body_parameters package)(affine_inner_pointer_pointers package)
    (affine_inner_pointer_scalars package)(affine_inner_pointer_extent package)(affine_inner_pointer_operations package)
    (affine_inner_pointer_syntax package)fe O observe D E width_tree WIDTH)as PREP.
  apply readonly_completed_tree_condition.
  - intros entry DOMAIN; destruct(readonly_available PREP entry DOMAIN)as [answer [checked [RUN SAME]]].
    exists answer; exact RUN.
  - intros entry DOMAIN RUN.
    destruct(@affine_evidence_preparation_ranges source(affine_inner_pointer_shape package)
      (affine_inner_pointer_expression package)(affine_inner_pointer_encoded package)
      (affine_inner_pointer_row_limit package)(affine_inner_pointer_column_limit package)
      (affine_inner_pointer_header_limits package)(affine_inner_pointer_body_limits package)
      (affine_inner_pointer_body_parameters package)(affine_inner_pointer_pointers package)
      (affine_inner_pointer_scalars package)(affine_inner_pointer_extent package)(affine_inner_pointer_operations package)
      (affine_inner_pointer_syntax package)fe O observe D E width_tree WIDTH entry DOMAIN RUN)
      as [HEADER [LIMIT [RANGES VIEW]]].
    constructor; assumption.
Defined.
End CONDITION.

Print Assumptions affine_snapshot_initial_words.
Print Assumptions affine_snapshot_first_cached_row.
Print Assumptions affine_snapshot_header_words.
Print Assumptions affine_snapshot_body_words.
Print Assumptions affine_snapshot_preparation_evidence.
Print Assumptions affine_snapshot_preparation_condition.
