From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightPureExpr ClightRedundantSet
  ClightRectangularGuard ClightCountedLoop ClightTempFrame ClightFrontendLoopProtocol ClightMatrixGuard ClightNoWrap.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryNaryCompute GuardMemoryArrayBackend GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext GuardMemoryParametricSourceClight
  GuardMemoryParametricSourceDomain GuardMemoryParametricGuard GuardMemoryPointerSequence GuardMemoryAffinePointerBody
  GuardMemoryAffineInnerPointerSyntax GuardMemoryRecursiveSource GuardMemoryScalarPointerBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This finite source domain contains no typing guesses for inactive body
    parameters, no pointer non-alias assumption, and no candidate correctness. *)
Definition memory_affine_inner_pointer_completed fe shape entry := exists after final,
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (memory_affine_inner_pointer_source shape) E0 after final Out_normal.
Definition memory_affine_inner_pointer_header_accept shape row_limit entry :=
  register_flag (affine_inner_pointer_row shape) Int.zero entry &&
  register_range_flag (affine_inner_pointer_bound shape) row_limit entry.
Definition memory_affine_inner_pointer_width_property shape expression column_limit entry :=
  let valuation := memory_source_word_valuation (entry_temps entry) in
  0 < memory_source_affine_math (memory_source_set_valuation valuation (affine_inner_pointer_row shape) 0) expression /\
  forall i, 0 <= i < valuation (affine_inner_pointer_bound shape) ->
    0 <= memory_source_affine_math (memory_source_set_valuation valuation (affine_inner_pointer_row shape) i) expression <= column_limit.

Lemma memory_affine_inner_pointer_header_sound shape row_limit entry :
  signed_range row_limit -> register_domain (affine_inner_pointer_row shape) entry ->
  register_domain (affine_inner_pointer_bound shape) entry ->
  memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
  (entry_temps entry) ! (affine_inner_pointer_row shape) = Some (Vint Int.zero) /\
  register_range (affine_inner_pointer_bound shape) row_limit entry.
Proof.
  intros LIMIT ROW BOUND ACCEPT; apply andb_true_iff in ACCEPT as [ZERO RANGE].
  split; [eapply register_flag_evidence; eassumption|eapply register_range_sound; eassumption].
Qed.

Section SOURCE.
Variable source : statement.
Variable shape : memory_affine_inner_pointer_shape.
Variable expression : memory_source_affine.
Variable encoded : L.expr.
Variable row_limit column_limit : Z.
Variable header_limits body_limits : list Z.
Variable body_parameters pointers scalars : list ident.
Variable extent : Z.
Variable operations : list memory_nary_compute.
Variable CERT : memory_affine_inner_pointer_certificate source shape expression encoded row_limit column_limit
  header_limits body_parameters body_limits pointers extent scalars operations.
Let row := affine_inner_pointer_row shape.
Let bound := affine_inner_pointer_bound shape.
Let column := affine_inner_pointer_column shape.
Let inner_bound := affine_inner_pointer_inner_bound shape.
Let body := affine_inner_pointer_body shape.
Let outer_body := affine_inner_pointer_outer_body shape.
Let header := memory_affine_inner_pointer_header shape expression.
Let parameters := memory_affine_inner_pointer_parameters shape expression body_parameters.
Let layout := memory_affine_inner_pointer_layout shape expression body_parameters.
Let limits := memory_affine_inner_pointer_limits row_limit column_limit header_limits body_limits.

Theorem memory_affine_inner_pointer_source_header_words fe entry :
  memory_affine_inner_pointer_completed fe shape entry ->
  register_domain row entry /\ register_domain bound entry /\
  ((entry_temps entry) ! row = Some (Vint Int.zero) ->
    0 < Int.signed (temp_word bound (entry_temps entry)) ->
    forall identifier, In identifier (memory_source_affine_reads expression) ->
      exists word, (entry_temps entry) ! identifier = Some (Vint word)).
Proof.
  intros [after [final SOURCE]]; destruct entry as [ge locals temps memory].
  eapply memory_parametric_source_words;
    [exact (affine_inner_pointer_rn CERT)|exact (affine_inner_pointer_rc CERT)|exact (affine_inner_pointer_rk CERT)|
     exact (affine_inner_pointer_nc CERT)|exact (affine_inner_pointer_nk CERT)|exact (affine_inner_pointer_ck CERT)| | | |exact SOURCE].
  - eapply memory_parametric_outer_normal;
      [eapply memory_pointer_sequence_quiet; exact (affine_inner_pointer_body_exact CERT)|exact (affine_inner_pointer_outer_exact CERT)].
  - eapply memory_parametric_outer_writes;
      [eapply memory_pointer_sequence_writes; exact (affine_inner_pointer_body_exact CERT)|exact (affine_inner_pointer_outer_exact CERT)].
  - exact (affine_inner_pointer_outer_exact CERT).
Qed.

Theorem memory_affine_inner_pointer_source_header_view fe entry :
  memory_affine_inner_pointer_completed fe shape entry ->
  memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
  MemoryNested.A.typed_view header (memory_source_parameter_values header entry) (entry_temps entry).
Proof.
  intros SOURCE ACCEPT.
  destruct (@memory_affine_inner_pointer_source_header_words fe entry SOURCE) as [ROW [BOUND WORDS]].
  assert (CAP : signed_range row_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  destruct (@memory_affine_inner_pointer_header_sound shape row_limit entry CAP ROW BOUND ACCEPT)
    as [ZERO [_ RANGE]].
  apply memory_source_parameter_view; intros identifier MEMBER.
  apply memory_source_context_member in MEMBER as [->|MEMBER]; [exact BOUND|].
  apply WORDS; [exact ZERO|exact (proj1 RANGE)|exact MEMBER].
Qed.

Theorem memory_affine_inner_pointer_source_body_words fe entry :
  memory_affine_inner_pointer_completed fe shape entry ->
  memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
  memory_affine_inner_pointer_width_property shape expression column_limit entry ->
  forall identifier, In identifier (body_parameters++scalars) ->
    exists word, (entry_temps entry) ! identifier = Some (Vint word).
Proof.
  intros SOURCE ACCEPT WIDTH.
  destruct (@memory_affine_inner_pointer_source_header_words fe entry SOURCE) as [ROW [BOUND WORDS]].
  assert (ROW_CAP : signed_range row_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  assert (COLUMN_CAP : signed_range column_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst.
    match goal with REST : Forall _ [column_limit] |- _ => inversion REST; subst; tauto end. }
  destruct (@memory_affine_inner_pointer_header_sound shape row_limit entry ROW_CAP ROW BOUND ACCEPT)
    as [ZERO [_ POSITIVE]].
  destruct BOUND as [n NLOOK].
  destruct SOURCE as [after [final SOURCE]]; destruct entry as [ge locals temps memory].
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
  eapply (@memory_affine_pointer_source_first_words fe ge locals temps memory row bound column inner_bound
    (memory_source_affine_code expression) rows upper body outer_body after final body_parameters scalars
    limits layout extent operations).
  - exact (affine_inner_pointer_rn CERT).
  - exact (affine_inner_pointer_rc CERT).
  - exact (affine_inner_pointer_rk CERT).
  - exact (affine_inner_pointer_nc CERT).
  - exact (affine_inner_pointer_nk CERT).
  - exact (affine_inner_pointer_ck CERT).
  - apply memory_source_affine_pure.
  - exact ZERO.
  - unfold rows; rewrite Int.repr_signed; exact NLOOK.
  - exact POS.
  - apply Int.signed_range.
  - exact VALUE.
  - exact (proj1 INNER).
  - exact (proj2 INNER).
  - intros identifier MEMBER; assert (ALL : In identifier (pointers++(parameters++scalars))).
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

Theorem memory_affine_inner_pointer_source_context_view fe entry :
  memory_affine_inner_pointer_completed fe shape entry ->
  memory_affine_inner_pointer_header_accept shape row_limit entry = true ->
  memory_affine_inner_pointer_width_property shape expression column_limit entry ->
  MemoryNested.A.typed_view (parameters++scalars)
    (memory_source_parameter_values (parameters++scalars) entry) (entry_temps entry).
Proof.
  intros SOURCE HEADER WIDTH; apply memory_source_parameter_view; intros identifier MEMBER.
  unfold parameters,memory_affine_inner_pointer_parameters in MEMBER; rewrite <-app_assoc in MEMBER.
  apply in_app_or in MEMBER as [HEAD|BODY].
  - eapply memory_source_typed_word;
      [eapply memory_affine_inner_pointer_source_header_view; eassumption|exact HEAD].
  - eapply memory_affine_inner_pointer_source_body_words; eassumption.
Qed.
End SOURCE.

Print Assumptions memory_affine_inner_pointer_header_sound.
Print Assumptions memory_affine_inner_pointer_source_header_words.
Print Assumptions memory_affine_inner_pointer_source_header_view.
Print Assumptions memory_affine_inner_pointer_source_body_words.
Print Assumptions memory_affine_inner_pointer_source_context_view.
