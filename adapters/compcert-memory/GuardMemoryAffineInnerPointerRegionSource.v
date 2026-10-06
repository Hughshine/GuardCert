From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightGuard ClightNoWrap ClightCountedLoop ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryNaryCompute
  GuardMemoryNaryRanges GuardMemoryRecursiveSource GuardMemoryRecursiveDomain GuardMemoryScalarPointerBody
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext
  GuardMemoryAffineSourceLoop GuardMemoryParametricGuard GuardMemoryParametricSourceDomain
  GuardMemoryParametricSourceClight GuardMemoryAffineParameterLoops GuardMemoryAffinePointerBody
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain GuardMemoryMultiPointerCells
  GuardMemoryInstructionPadding.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_affine_inner_pointer_region_context source (package : memory_affine_inner_pointer_package source) :=
  memory_affine_inner_pointer_parameters (affine_inner_pointer_shape package) (affine_inner_pointer_expression package)
    (affine_inner_pointer_body_parameters package) ++ affine_inner_pointer_scalars package.
Definition memory_affine_inner_pointer_region_instructions source (package : memory_affine_inner_pointer_package source) :=
  memory_pad_instructions (length (affine_inner_pointer_scalars package))
    (map memory_nary_compute_instruction (affine_inner_pointer_operations package)).
Definition memory_affine_inner_pointer_region_model source (package : memory_affine_inner_pointer_package source) :=
  memory_affine_parameter_sequence (length (memory_affine_inner_pointer_region_context package))
    (affine_inner_pointer_encoded package) (memory_affine_inner_pointer_region_instructions package).

Lemma memory_affine_inner_pointer_word_math temps row i expression :
  memory_source_affine_math (memory_source_set_valuation (memory_source_word_valuation temps) row i) expression =
  memory_source_affine_math (memory_source_set_valuation (fun id => Int.signed (temp_word id temps)) row i) expression.
Proof.
  induction expression; cbn [memory_source_affine_math]; try (rewrite IHexpression1,IHexpression2; reflexivity);
    try (rewrite IHexpression; reflexivity); [|reflexivity].
  unfold memory_source_set_valuation; destruct (peq identifier row); [reflexivity|apply memory_source_word_temp].
Qed.

(** Source correspondence assembled from one checked normalized package.
    No non-alias is needed to decode a source execution. Accepted geometry
    ranges and width facts are explicit inputs until the guard is connected. *)
Theorem memory_affine_inner_pointer_region_source_under_ranges source (package : memory_affine_inner_pointer_package source)
  fe ge locals temps memory after final :
  let shape := affine_inner_pointer_shape package in
  let expression := affine_inner_pointer_expression package in
  let encoded := affine_inner_pointer_encoded package in
  let parameters := memory_affine_inner_pointer_parameters shape expression (affine_inner_pointer_body_parameters package) in
  let values := memory_source_parameter_values (memory_affine_inner_pointer_region_context package) (Entry ge locals temps memory) in
  memory_affine_inner_pointer_header_accept shape (affine_inner_pointer_row_limit package) (Entry ge locals temps memory) = true ->
  memory_affine_inner_pointer_width_property shape expression (affine_inner_pointer_column_limit package) (Entry ge locals temps memory) ->
  memory_nary_ranges ((affine_inner_pointer_row_limit package+1)::affine_inner_pointer_header_limits package++affine_inner_pointer_body_limits package)
    (memory_source_parameter_values parameters (Entry ge locals temps memory)) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  L.loop_semantics (memory_affine_inner_pointer_region_model package) values
    (RuntimeState (memory_multi_pointer_locations temps (affine_inner_pointer_extent package)) memory)
    (RuntimeState (memory_multi_pointer_locations temps (affine_inner_pointer_extent package)) final) /\
  after = PTree.set (affine_inner_pointer_row shape) (Vint (Int.repr (Int.signed (temp_word (affine_inner_pointer_bound shape) temps))))
    (memory_parametric_settle (affine_inner_pointer_column shape) (affine_inner_pointer_inner_bound shape)
      (fun i => L.eval_expr (i::values) encoded) (Int.signed (temp_word (affine_inner_pointer_bound shape) temps)-1) temps).
Proof.
  destruct package as [shape expression encoded row_limit column_limit header_limits body_parameters body_limits
    pointers extent scalars operations CERT]; cbn; intros HEADER WIDTH GEOMETRY_RANGE SOURCE.
  set (row := affine_inner_pointer_row shape); set (bound := affine_inner_pointer_bound shape).
  set (column := affine_inner_pointer_column shape); set (inner_bound := affine_inner_pointer_inner_bound shape).
  set (geometry := memory_source_other_parameters row bound expression++body_parameters).
  set (valuation := fun identifier => Int.signed (temp_word identifier temps)).
  set (N := valuation bound); set (rows := Z.to_nat N).
  set (geometry_values := map valuation geometry); set (scalar_values := map valuation scalars).
  set (values := (Z.of_nat rows::geometry_values)++scalar_values).
  set (upper := fun i => L.eval_expr (i::values) encoded).
  assert (DOMAIN : memory_affine_inner_pointer_completed fe shape (Entry ge locals temps memory)).
  { exists after,final; rewrite <- (affine_inner_pointer_source_exact CERT); exact SOURCE. }
  assert (SOURCE_SHAPE : exec_stmt fe ge locals temps memory
    (memory_affine_inner_pointer_source shape) E0 after final Out_normal).
  { rewrite <- (affine_inner_pointer_source_exact CERT); exact SOURCE. }
  destruct (@memory_affine_inner_pointer_source_header_words source shape expression encoded row_limit column_limit
    header_limits body_limits body_parameters pointers scalars extent operations CERT fe _ DOMAIN) as [ROW [BOUND WORDS]].
  assert (ROW_CAP : signed_range row_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst; tauto. }
  assert (COLUMN_CAP : signed_range column_limit).
  { pose proof (affine_inner_pointer_control_limits CERT) as CAPS; inversion CAPS; subst.
    match goal with REST : Forall _ [column_limit] |- _ => inversion REST; subst; tauto end. }
  destruct (@memory_affine_inner_pointer_header_sound shape row_limit _ ROW_CAP ROW BOUND HEADER) as [ZERO [_ N_RANGE]].
  assert (NPOS : 0 < N) by exact (proj1 N_RANGE).
  assert (RZ : Z.of_nat rows = N) by (unfold rows; apply Z2Nat.id; exact (Z.lt_le_incl _ _ (proj1 N_RANGE))).
  assert (FULL_VALUES : map valuation (memory_affine_inner_pointer_parameters shape expression body_parameters++scalars) = values).
  { unfold values,geometry_values,scalar_values,geometry,memory_affine_inner_pointer_parameters,
      memory_affine_inner_pointer_header,memory_source_context; rewrite !map_app; cbn; rewrite RZ; reflexivity. }
  pose proof (@memory_affine_inner_pointer_source_context_view source shape expression encoded row_limit column_limit
    header_limits body_limits body_parameters pointers scalars extent operations CERT fe _ DOMAIN HEADER WIDTH) as FULL_VIEW.
  assert (FULL_WORDS : forall identifier, In identifier (memory_affine_inner_pointer_parameters shape expression body_parameters++scalars) ->
    exists word, temps ! identifier = Some (Vint word)).
  { intros identifier MEMBER; exact (@memory_source_typed_word _ _ _ identifier FULL_VIEW MEMBER). }
  assert (PARAMETERS : memory_nest_bindings (bound::geometry) (Z.of_nat rows::geometry_values) temps).
  { rewrite RZ; change (memory_nest_bindings (bound::geometry) (map valuation (bound::geometry)) temps).
    apply memory_scalar_register_bindings; intros identifier MEMBER; apply FULL_WORDS.
    apply in_or_app; left; exact MEMBER. }
  assert (SCALARS : memory_nest_bindings scalars scalar_values temps).
  { apply memory_scalar_register_bindings; intros identifier MEMBER; apply FULL_WORDS; apply in_or_app; right; exact MEMBER. }
  assert (ENCODED_VALUE : forall i, upper i = memory_source_affine_math (memory_source_set_valuation valuation row i) expression).
  { intro i; unfold upper; rewrite <-FULL_VALUES; apply memory_source_loop_expression_value.
    exact (affine_inner_pointer_full_encoding CERT). }
  assert (MATH_WIDTH : 0 < memory_source_affine_math (memory_source_set_valuation valuation row 0) expression /\
    forall i, 0 <= i < N -> 0 <= memory_source_affine_math (memory_source_set_valuation valuation row i) expression <= column_limit).
  { change (memory_affine_inner_pointer_width_property shape expression column_limit (Entry ge locals temps memory)) in WIDTH.
    unfold memory_affine_inner_pointer_width_property in WIDTH; cbn [entry_temps] in WIDTH; split.
    - unfold valuation; rewrite <-memory_affine_inner_pointer_word_math; exact (proj1 WIDTH).
    - intros i I; unfold valuation; rewrite <-memory_affine_inner_pointer_word_math; apply (proj2 WIDTH).
      rewrite memory_source_word_temp; exact I. }
  assert (INNER : forall i, 0 <= i < Z.of_nat rows -> 0 <= upper i <= column_limit /\ signed_range (upper i)).
  { intros i I; rewrite ENCODED_VALUE; pose proof (proj2 MATH_WIDTH i ltac:(rewrite <-RZ; exact I)) as RANGE.
    unfold signed_range in *; change Int.min_signed with (-2147483648) in *; split; [exact RANGE|lia]. }
  assert (PROTECTED : forall identifier, In identifier (pointers++((bound::geometry)++scalars)) ->
    identifier <> row /\ identifier <> column /\ identifier <> inner_bound).
  { intros identifier MEMBER; pose proof (affine_inner_pointer_protected CERT MEMBER) as FRESH.
    repeat split; intro SAME; apply FRESH; subst identifier; cbn; auto. }
  assert (VALUE : forall i current before, 0 <= i < Z.of_nat rows ->
    current ! row = Some (Vint (Int.repr i)) ->
    temp_agree (pointers++((bound::geometry)++scalars)) temps current ->
    eval_expr ge locals current before (memory_source_affine_code expression) (Vint (Int.repr (upper i)))).
  { intros i current before I CURRENT FRAME; rewrite ENCODED_VALUE.
    eapply memory_source_affine_iteration_value; [exact CURRENT| |].
    - intros identifier MEMBER; destruct (FULL_WORDS identifier
        ltac:(apply in_or_app; left; apply in_or_app; left; apply memory_source_context_read;
          apply memory_source_affine_parameter_member in MEMBER; tauto)) as [word LOOK].
      unfold valuation,temp_word; rewrite LOOK,Int.repr_signed; reflexivity.
    - eapply temp_agree_weaken; [|exact FRAME].
      intros identifier MEMBER; apply in_or_app; right; apply in_or_app; left.
      change (In identifier (memory_source_context row bound expression++body_parameters));
      apply in_or_app; left; apply memory_source_context_read;
        apply memory_source_affine_parameter_member in MEMBER; tauto. }
  destruct (@memory_affine_pointer_source_decode fe ge locals row bound column inner_bound
    (memory_source_affine_code expression) encoded (affine_inner_pointer_body shape) (affine_inner_pointer_outer_body shape)
    geometry scalars pointers ((row_limit+1)::header_limits++body_limits) row_limit column_limit extent operations
    (affine_inner_pointer_rn CERT) (affine_inner_pointer_rc CERT) (affine_inner_pointer_nc CERT) (affine_inner_pointer_rk CERT)
    (affine_inner_pointer_nk CERT) (affine_inner_pointer_ck CERT) PROTECTED (affine_inner_pointer_unique CERT)
    (affine_inner_pointer_operations_valid CERT) (affine_inner_pointer_operations_covered CERT)
    (affine_inner_pointer_body_exact CERT) (affine_inner_pointer_outer_exact CERT) rows geometry_values scalar_values temps
    ltac:(intro EMPTY; rewrite EMPTY in RZ; cbn in RZ; lia) ltac:(rewrite RZ; apply Int.signed_range)
    ltac:(rewrite RZ; exact (proj2 N_RANGE)) INNER
    ltac:(rewrite RZ; exact GEOMETRY_RANGE) PARAMETERS SCALARS (memory_source_affine_pure expression) VALUE
    temps memory after final ZERO (temp_agree_refl _ _) SOURCE_SHAPE)
    as [MODEL EXIT].
  rewrite RZ in EXIT.
  split.
  2: { change (after = PTree.set row (Vint (Int.repr N))
    (memory_parametric_settle column inner_bound
      (fun i => L.eval_expr (i::N::map valuation (geometry++scalars)) encoded) (N-1) temps)).
    rewrite map_app; exact EXIT. }
  unfold memory_affine_inner_pointer_region_model,memory_affine_inner_pointer_region_context,
    memory_affine_inner_pointer_region_instructions; cbn.
  change (L.loop_semantics (memory_affine_parameter_sequence
    (length (memory_affine_inner_pointer_parameters shape expression body_parameters++scalars)) encoded
    (memory_pad_instructions (length scalars) (map memory_nary_compute_instruction operations)))
    (map valuation (memory_affine_inner_pointer_parameters shape expression body_parameters++scalars))
    (RuntimeState (memory_multi_pointer_locations temps extent) memory)
    (RuntimeState (memory_multi_pointer_locations temps extent) final)).
  rewrite FULL_VALUES.
  replace (length (memory_affine_inner_pointer_parameters shape expression body_parameters++scalars)) with (length values)
    by (rewrite <-FULL_VALUES,length_map; reflexivity).
  exact MODEL.
Qed.
Print Assumptions memory_affine_inner_pointer_region_source_under_ranges.
