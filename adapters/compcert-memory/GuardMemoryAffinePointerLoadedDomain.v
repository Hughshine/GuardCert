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
  GuardMemoryAffinePointerLoadedSource GuardMemoryRecursiveSource GuardMemoryScalarPointerBody.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictIteration ClightPreloadSnapshot.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_pointer_loaded_source source (package : memory_affine_inner_pointer_package source) pointer :=
  loaded_bound_loop (affine_inner_pointer_row (affine_inner_pointer_shape package)) pointer
    (affine_inner_pointer_outer_body (affine_inner_pointer_shape package)).
Definition memory_affine_pointer_loaded_completed source (package : memory_affine_inner_pointer_package source) pointer fe entry :=
  loaded_preload_domain (affine_inner_pointer_row (affine_inner_pointer_shape package))
    (affine_inner_pointer_bound (affine_inner_pointer_shape package)) pointer
    (affine_inner_pointer_pointers package) entry /\ exists after final,
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (memory_affine_pointer_loaded_source package pointer) E0 after final Out_normal.

Lemma loaded_preload_active iterator cache pointer pointers ge locals temps memory :
  loaded_preload_domain iterator cache pointer pointers (Entry ge locals temps memory) ->
  temps ! iterator = Some (Vint Int.zero) -> 0 < Int.signed (temp_word cache temps) ->
  expression_test (loaded_bound_test iterator pointer) (Entry ge locals temps memory) true.
Proof.
  intros [ROW [[word [block [offset [CACHE [POINTER READ]]]]] OBSERVED]] ZERO POSITIVE.
  cbn [entry_temps entry_memory] in CACHE,POINTER,READ.
  unfold temp_word in POSITIVE; rewrite CACHE in POSITIVE.
  replace true with (Int.lt Int.zero word).
  - eapply loaded_bound_test_eval; [exact ZERO|exact POINTER|exact READ].
  - unfold Int.lt; rewrite Int.signed_zero; destruct (zlt 0 (Int.signed word)); [reflexivity|lia].
Qed.

Section SOURCE.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable pointer : ident.
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
Let D := memory_affine_pointer_loaded_completed package pointer.

Theorem memory_affine_pointer_loaded_header_words fe entry :
  D fe entry -> register_domain row entry /\ register_domain bound entry /\
  ((entry_temps entry) ! row = Some (Vint Int.zero) ->
    0 < Int.signed (temp_word bound (entry_temps entry)) ->
    forall identifier, In identifier (memory_source_affine_reads expression) ->
      exists word, (entry_temps entry) ! identifier = Some (Vint word)).
Proof.
  intros [DOMAIN [after [final SOURCE]]].
  pose proof DOMAIN as ORIGINAL_DOMAIN.
  destruct DOMAIN as [ROW [[word [block [offset [CACHE [POINTER READ]]]]] OBSERVED]].
  split; [exact ROW|split; [exists word; exact CACHE|]].
  intros ZERO POSITIVE.
  destruct entry as [ge locals temps memory].
  assert (ACTIVE : expression_test (loaded_bound_test row pointer) (Entry ge locals temps memory) true).
  { exact (@loaded_preload_active row bound pointer (affine_inner_pointer_pointers package)
      ge locals temps memory ORIGINAL_DOMAIN ZERO POSITIVE). }
  assert (QUIET : quiet_statement outer_body = true).
  { unfold outer_body,shape; apply flatten_quiet_certificate; rewrite (affine_inner_pointer_outer_exact CERT).
    constructor; [reflexivity|constructor; [reflexivity|constructor; [|constructor]]].
    cbn [quiet_statement frontend_counted_loop counter_increment];
      rewrite (@memory_pointer_sequence_quiet (affine_inner_pointer_operations package)
        (affine_inner_pointer_body (affine_inner_pointer_shape package)) (affine_inner_pointer_body_exact CERT)); reflexivity. }
  assert (NORMAL : normal_statement outer_body = true).
  { eapply memory_parametric_outer_normal; [eapply memory_pointer_sequence_quiet;
      exact (affine_inner_pointer_body_exact CERT)|exact (affine_inner_pointer_outer_exact CERT)]. }
  destruct (@strict_active_iteration fe ge locals row (loaded_bound_test row pointer) outer_body temps memory
    after final NORMAL QUIET ACTIVE SOURCE) as [middle [last [next [rest [BODY _]]]]].
  eapply memory_parametric_outer_source_words;
    [exact (affine_inner_pointer_ck CERT)|exact (affine_inner_pointer_outer_exact CERT)|exact BODY].
Qed.

Theorem memory_affine_pointer_loaded_header_view fe entry :
  D fe entry -> memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
  MemoryNested.A.typed_view header (memory_source_parameter_values header entry) (entry_temps entry).
Proof.
  intros SOURCE ACCEPT.
  destruct (memory_affine_pointer_loaded_header_words SOURCE) as [ROW [BOUND WORDS]].
  assert (CAP : signed_range row_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  destruct (@memory_affine_inner_pointer_header_sound shape row_limit entry CAP ROW BOUND ACCEPT)
    as [ZERO [_ RANGE]].
  apply memory_source_parameter_view; intros identifier MEMBER.
  apply memory_source_context_member in MEMBER as [->|MEMBER]; [exact BOUND|].
  apply WORDS; [exact ZERO|exact (proj1 RANGE)|exact MEMBER].
Qed.

Theorem memory_affine_pointer_loaded_body_words fe entry :
  D fe entry -> memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
  memory_affine_inner_pointer_width_property shape expression column_limit entry ->
  forall identifier, In identifier (body_parameters++scalars) ->
    exists word, (entry_temps entry) ! identifier = Some (Vint word).
Proof.
  intros SOURCE ACCEPT WIDTH.
  destruct (memory_affine_pointer_loaded_header_words SOURCE) as [ROW [BOUND WORDS]].
  assert (ROW_CAP : signed_range row_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  assert (COLUMN_CAP : signed_range column_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS.
    apply Forall_forall with (x:=column_limit) in CAPS; [exact (proj2 CAPS)|right; left; reflexivity]. }
  destruct (@memory_affine_inner_pointer_header_sound shape row_limit entry ROW_CAP ROW BOUND ACCEPT)
    as [ZERO [_ POSITIVE]].
  destruct BOUND as [n NLOOK].
  destruct SOURCE as [DOMAIN [after [final SOURCE]]]; destruct entry as [ge locals temps memory].
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
  eapply (@memory_affine_pointer_loaded_first_words fe ge locals temps memory row pointer column inner_bound
    (memory_source_affine_code expression) upper body outer_body after final body_parameters scalars
    limits layout extent operations).
  - exact (affine_inner_pointer_ck CERT).
  - apply memory_source_affine_pure.
  - eapply loaded_preload_active; [exact DOMAIN|exact ZERO|exact (proj1 POSITIVE)].
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

Theorem memory_affine_pointer_loaded_context_view fe entry :
  D fe entry -> memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
  memory_affine_inner_pointer_width_property shape expression column_limit entry ->
  MemoryNested.A.typed_view (parameters++scalars)
    (memory_source_parameter_values (parameters++scalars) entry) (entry_temps entry).
Proof.
  intros SOURCE HEADER WIDTH; apply memory_source_parameter_view; intros identifier MEMBER.
  unfold parameters,memory_affine_inner_pointer_parameters in MEMBER; rewrite <-app_assoc in MEMBER.
  apply in_app_or in MEMBER as [HEAD|BODY].
  - eapply memory_source_typed_word; [eapply memory_affine_pointer_loaded_header_view; eassumption|exact HEAD].
  - eapply memory_affine_pointer_loaded_body_words; eassumption.
Qed.
End SOURCE.

Print Assumptions loaded_preload_active.
Print Assumptions memory_affine_pointer_loaded_header_words.
Print Assumptions memory_affine_pointer_loaded_header_view.
Print Assumptions memory_affine_pointer_loaded_body_words.
Print Assumptions memory_affine_pointer_loaded_context_view.
