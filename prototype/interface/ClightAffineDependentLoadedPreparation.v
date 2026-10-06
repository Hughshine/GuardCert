From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightPureExpr ClightNoWrap ClightStraightLine ClightRedundantSet
  ClightRectangularGuard ClightCountedLoop ClightTempFrame ClightFrontendLoopProtocol.
From Guard Require Import ClightRegionProgress ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryNaryCompute
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext
  GuardMemoryParametricSourceClight GuardMemoryParametricSourceDomain GuardMemoryParametricGuard GuardMemoryPointerSequence
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffinePointerLoadedSource GuardMemoryRecursiveSource GuardMemoryScalarPointerBody GuardMemoryAffineDependentSourceWords GuardMemoryParametricWidth.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictIteration ClightPreloadSnapshot ClightDependentBoundSyntax ClightDependentHeaderObservations
  ClightAffineDependentLoadedPrefix ClightAffinePreparedRows ClightAffinePreparationEvidence
  GuardedRewrite ClightReadonlyRewrite ClightReadonlyCompletedCondition ClightConditionComposition
  ClightAffinePointerGuard ClightAffinePointerSourcePreparation ClightReadonlyLoadedTreeSynthesis
  ClightAffineInnerPointerSourceGuard.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma affine_dependent_preload_active row cache root pointer_cache entry :
  dependent_cached_header root pointer_cache cache entry ->
  (entry_temps entry) ! row = Some (Vint Int.zero) -> 0 < Int.signed (temp_word cache (entry_temps entry)) ->
  expression_test (dependent_bound_test row root) entry true.
Proof.
  intros [block [offset [target [address [bound [ROOT [POINTER [CACHE [READ_POINTER READ_BOUND]]]]]]]]]
    ZERO POSITIVE.
  unfold temp_word in POSITIVE; rewrite CACHE in POSITIVE.
  replace true with (Int.lt Int.zero bound).
  - destruct entry as [ge locals temps memory]; eapply dependent_bound_test_eval;
      [exact ZERO|exact ROOT|exact READ_POINTER|exact READ_BOUND].
  - unfold Int.lt; rewrite Int.signed_zero; destruct (zlt 0 (Int.signed bound)); [reflexivity|lia].
Qed.

Section SOURCE.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root pointer_cache : ident.
Let shape := affine_inner_pointer_shape package.
Let expression := affine_inner_pointer_expression package.
Let encoded := affine_inner_pointer_encoded package.
Let row_limit := affine_inner_pointer_row_limit package.
Let column_limit := affine_inner_pointer_column_limit package.
Let body_parameters := affine_inner_pointer_body_parameters package.
Let scalars := affine_inner_pointer_scalars package.
Let operations := affine_inner_pointer_operations package.
Let extent := affine_inner_pointer_extent package.
Let CERT := affine_inner_pointer_syntax package.
Let row := affine_inner_pointer_row shape.
Let bound := affine_inner_pointer_bound shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let body := affine_inner_pointer_body shape.
Let outer_body := affine_inner_pointer_outer_body shape.
Let header := memory_affine_inner_pointer_header shape expression.
Let parameters := memory_affine_inner_pointer_parameters shape expression body_parameters.
Let layout := memory_affine_inner_pointer_layout shape expression body_parameters.
Let limits := memory_affine_inner_pointer_limits row_limit column_limit
  (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package).
Let D := affine_dependent_loaded_completed package root pointer_cache.

Theorem affine_dependent_header_words fe entry :
  D fe entry -> register_domain row entry /\ register_domain bound entry /\
  ((entry_temps entry) ! row = Some (Vint Int.zero) ->
    0 < Int.signed (temp_word bound (entry_temps entry)) ->
    forall identifier, In identifier (memory_source_affine_reads expression) ->
      exists word, (entry_temps entry) ! identifier = Some (Vint word)).
Proof.
  intros [ROW [CACHED [OBSERVED [after [final SOURCE]]]]].
  assert (CACHE : register_domain bound entry).
  { destruct CACHED as [block [offset [target [address [word [ROOT [POINTER [CACHE REST]]]]]]]];
      exists word; exact CACHE. }
  split; [exact ROW|split; [exact CACHE|]].
  intros ZERO POSITIVE; destruct entry as [ge locals temps memory].
  pose proof (@affine_dependent_preload_active row bound root pointer_cache (Entry ge locals temps memory)
    CACHED ZERO POSITIVE) as ACTIVE.
  destruct (@strict_active_iteration fe ge locals row (dependent_bound_test row root) outer_body temps memory
    after final (@affine_prepared_outer_normal source package) (@affine_prepared_outer_quiet source package)
    ACTIVE SOURCE) as [middle [last [next [rest [BODY _]]]]].
  eapply memory_parametric_outer_source_words;
    [exact (affine_inner_pointer_ck CERT)|exact (affine_inner_pointer_outer_exact CERT)|exact BODY].
Qed.

Theorem affine_dependent_body_words fe entry :
  D fe entry -> memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
  memory_affine_inner_pointer_width_property shape expression column_limit entry ->
  forall identifier, In identifier (body_parameters++scalars) ->
    exists word, (entry_temps entry) ! identifier = Some (Vint word).
Proof.
  intros SOURCE ACCEPT WIDTH.
  destruct (affine_dependent_header_words SOURCE) as [ROW [BOUND WORDS]].
  assert (ROW_CAP : signed_range row_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  assert (COLUMN_CAP : signed_range column_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS.
    apply Forall_forall with (x:=column_limit) in CAPS; [exact (proj2 CAPS)|right; left; reflexivity]. }
  destruct (@memory_affine_inner_pointer_header_sound shape row_limit entry ROW_CAP ROW BOUND ACCEPT)
    as [ZERO [_ POSITIVE]].
  destruct BOUND as [n NLOOK].
  pose proof SOURCE as DOMAIN; destruct SOURCE as [ROW_DOMAIN [CACHED [OBSERVED [after [final SOURCE]]]]];
  destruct entry as [ge locals temps memory].
  cbn [entry_temps] in ZERO,NLOOK,WORDS.
  set (valuation := memory_source_word_valuation temps).
  set (rows := Int.signed n).
  set (upper := memory_source_affine_math (memory_source_set_valuation valuation row 0) expression).
  assert (N : valuation bound = rows).
  { unfold valuation,rows,memory_source_word_valuation; rewrite NLOOK; reflexivity. }
  assert (POS : 0 < rows).
  { change (0 < Int.signed (temp_word bound temps) <= row_limit) in POSITIVE.
    unfold temp_word in POSITIVE; rewrite NLOOK in POSITIVE; tauto. }
  assert (INNER : 0 < upper /\ signed_range upper).
  { change (0 < upper /\ forall i, 0 <= i < valuation bound ->
      0 <= memory_source_affine_math (memory_source_set_valuation valuation row i) expression <= column_limit) in WIDTH.
    destruct WIDTH as [FIRST ALL]; pose proof (ALL 0 ltac:(rewrite N; lia)) as RANGE.
    unfold signed_range in *; change Int.min_signed with (-2147483648) in *; split; [exact FIRST|lia]. }
  assert (VALUE : eval_expr ge locals temps memory (memory_source_affine_code expression) (Vint (Int.repr upper))).
  { eapply memory_source_affine_iteration_value with (base := temps) (value := 0) (valuation := valuation).
    - exact ZERO.
    - intros identifier MEMBER; apply memory_source_affine_parameter_member in MEMBER.
      destruct (WORDS ZERO (proj1 POSITIVE) identifier (proj1 MEMBER)) as [word LOOK].
      unfold valuation,memory_source_word_valuation; rewrite LOOK,Int.repr_signed; reflexivity.
    - apply temp_agree_refl. }
  eapply (@memory_affine_header_first_words fe ge locals temps memory row (dependent_bound_test row root) column inner_bound
    (memory_source_affine_code expression) upper body outer_body after final body_parameters scalars
    limits layout extent operations).
  - exact (affine_inner_pointer_ck CERT).
  - apply memory_source_affine_pure.
  - eapply affine_dependent_preload_active; [exact (proj1 (proj2 DOMAIN))|exact ZERO|exact (proj1 POSITIVE)].
  - exact VALUE.
  - exact (proj1 INNER).
  - exact (proj2 INNER).
  - intros identifier MEMBER; assert (ALL : In identifier
      (affine_inner_pointer_pointers package++(parameters++scalars))).
    { apply in_or_app; right; apply in_app_or in MEMBER as [BODY_PARAM|SCALAR].
      - apply in_or_app; left; unfold parameters,memory_affine_inner_pointer_parameters; apply in_or_app; right; exact BODY_PARAM.
      - apply in_or_app; right; exact SCALAR. }
    pose proof (affine_inner_pointer_protected CERT ALL) as FRESH.
    split; intro SAME; apply FRESH; subst identifier; cbn; auto.
  - exact (affine_inner_pointer_outer_exact CERT).
  - exact (affine_inner_pointer_body_exact CERT).
  - exact (affine_inner_pointer_operations_valid CERT).
  - exact (affine_inner_pointer_body_parameters_used CERT).
  - exact (affine_inner_pointer_scalars_used CERT).
  - exact SOURCE.
Qed.

End SOURCE.

Definition affine_dependent_preparation_evidence source (package : memory_affine_inner_pointer_package source) root pointer_cache fe :
  affine_preparation_evidence (affine_inner_pointer_shape package) (affine_inner_pointer_expression package)
    (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_body_parameters package) (affine_inner_pointer_scalars package)
    (affine_dependent_loaded_completed package root pointer_cache fe).
Proof.
  constructor.
  - exact (@affine_dependent_header_words source package root pointer_cache fe).
  - exact (@affine_dependent_body_words source package root pointer_cache fe).
Defined.

Section CONDITION.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variables root pointer_cache : ident.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Variable width_tree : decision_tree.
Hypothesis WIDTH : compile_memory_source_width (affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row (affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package) = Some width_tree.
Let D := affine_dependent_loaded_completed package root pointer_cache fe.
Let E := affine_dependent_preparation_evidence package root pointer_cache fe.

Definition affine_dependent_preparation_condition :
  readonly_condition (readonly_clight_host fe observe) D (affine_inner_pointer_ready package)
    (affine_inner_pointer_package_preparation_tree package width_tree).
Proof.
  pose proof (@affine_evidence_preparation_condition source (affine_inner_pointer_shape package)
    (affine_inner_pointer_expression package) (affine_inner_pointer_encoded package)
    (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
    (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package)
    (affine_inner_pointer_body_parameters package) (affine_inner_pointer_pointers package)
    (affine_inner_pointer_scalars package) (affine_inner_pointer_extent package) (affine_inner_pointer_operations package)
    (affine_inner_pointer_syntax package) fe O observe D E width_tree WIDTH) as PREP.
  apply readonly_completed_tree_condition.
  - intros entry DOMAIN; destruct (readonly_available PREP entry DOMAIN) as [answer [checked [RUN SAME]]].
    exists answer; exact RUN.
  - intros entry DOMAIN RUN.
    destruct (@affine_evidence_preparation_ranges source (affine_inner_pointer_shape package)
      (affine_inner_pointer_expression package) (affine_inner_pointer_encoded package)
      (affine_inner_pointer_row_limit package) (affine_inner_pointer_column_limit package)
      (affine_inner_pointer_header_limits package) (affine_inner_pointer_body_limits package)
      (affine_inner_pointer_body_parameters package) (affine_inner_pointer_pointers package)
      (affine_inner_pointer_scalars package) (affine_inner_pointer_extent package) (affine_inner_pointer_operations package)
      (affine_inner_pointer_syntax package) fe O observe D E width_tree WIDTH entry DOMAIN RUN)
      as [HEADER [LIMIT [RANGES VIEW]]].
    constructor; assumption.
Defined.
End CONDITION.

Print Assumptions affine_dependent_preparation_condition.

Print Assumptions affine_dependent_preload_active.
Print Assumptions affine_dependent_header_words.
Print Assumptions affine_dependent_body_words.
Print Assumptions affine_dependent_preparation_evidence.
