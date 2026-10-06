From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightCondition ClightPureExpr ClightRectangularStore.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceEndpoints GuardMemoryNaryAffineExpressions
  GuardMemoryParametricWidth GuardMemoryParametricGuard.
From GuardInterface Require Import AffineBoxEnvelope ClightAffineEnvelope.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma affine_dot_polcert coefficients values : affine_dot coefficients values = dot_product coefficients values.
Proof. revert values; induction coefficients; intros [|value values]; cbn; auto; rewrite IHcoefficients; reflexivity. Qed.
Lemma affine_value_source term values : affine_value term values = memory_nary_index_value term values.
Proof. unfold affine_value,memory_nary_index_value; rewrite affine_dot_polcert; reflexivity. Qed.

Lemma envelope_source_instance expression row context form valuation coordinate :
  ~ In row context -> memory_encode_nary_index (row::context) expression = Some form ->
  affine_value form (coordinate::map valuation context) =
    memory_source_affine_math (memory_source_set_valuation valuation row coordinate) expression.
Proof.
  intros FRESH ENCODE; rewrite affine_value_source.
  rewrite (@memory_encode_nary_index_value expression (row::context) form
    (memory_source_set_valuation valuation row coordinate) ENCODE).
  f_equal; cbn [map]; unfold memory_source_set_valuation.
  destruct (peq row row); [|congruence]; f_equal.
  apply map_ext_in; intros identifier MEMBER; destruct (peq identifier row); [subst; contradiction|reflexivity].
Qed.

Definition zero_coordinate_form (form : affine_form) : affine_form := (0::skipn 1 (fst form),snd form).
Lemma zero_coordinate_value form count parameters :
  affine_value (zero_coordinate_form form) (count::parameters) = affine_value form (0::parameters).
Proof. destruct form as [[|coefficient coefficients] bias]; unfold affine_value,zero_coordinate_form; cbn; ring. Qed.
Definition envelope_constant arity value : affine_form := (repeat 0 arity,value).
Lemma affine_dot_zero values : forall arity, affine_dot (repeat 0 arity) values = 0.
Proof. induction values; intros [|arity]; cbn; auto; rewrite IHvalues; ring. Qed.
Lemma envelope_constant_value arity value values : affine_value (envelope_constant arity value) values = value.
Proof. unfold affine_value,envelope_constant; cbn; rewrite affine_dot_zero; ring. Qed.
Definition envelope_bounds bounds := map (fun interval => (MemoryNested.A.lower interval,MemoryNested.A.upper interval)) bounds.

Definition compile_envelope_forms_width registers ranges stride form lower upper : option decision_tree :=
  let zero := envelope_constant (length registers) 0 in
  let maximum := envelope_constant (length registers) stride in
  match compile_affine_interval_comparison registers ranges zero (zero_coordinate_form form),
    compile_affine_interval_comparison registers ranges lower zero,
    compile_affine_interval_comparison registers ranges maximum upper with
  | Some positive,Some below,Some above =>
    Some (Test positive (Test below (Decision false)
      (Test above (Decision false) (Decision true))) (Decision false))
  | _,_,_ => None end.
Lemma compile_envelope_forms_width_pure registers ranges stride form lower upper tree :
  compile_envelope_forms_width registers ranges stride form lower upper = Some tree -> pure_tree tree.
Proof.
  unfold compile_envelope_forms_width.
  destruct (compile_affine_interval_comparison registers ranges
    (envelope_constant (length registers) 0) (zero_coordinate_form form)) as [positive|] eqn:POSITIVE; [|discriminate].
  destruct (compile_affine_interval_comparison registers ranges lower
    (envelope_constant (length registers) 0)) as [below|] eqn:BELOW; [|discriminate].
  destruct (compile_affine_interval_comparison registers ranges
    (envelope_constant (length registers) stride) upper) as [above|] eqn:ABOVE; [|discriminate].
  intro SAME; injection SAME as <-; repeat constructor;
    eapply compiled_affine_interval_comparison_pure; eassumption.
Qed.
Theorem compile_envelope_forms_width_correct registers ranges stride form lower upper tree values ge locals temps memory :
  compile_envelope_forms_width registers ranges stride form lower upper = Some tree ->
  affine_registers_view registers values temps ->
  Forall2 (fun value range => fst range <= value <= snd range) values ranges ->
  (exists answer, decision_run (Entry ge locals temps memory) tree answer) /\
  (decision_run (Entry ge locals temps memory) tree true ->
    0 < affine_value (zero_coordinate_form form) values /\
    0 <= affine_value lower values /\ affine_value upper values <= stride).
Proof.
  unfold compile_envelope_forms_width.
  destruct (compile_affine_interval_comparison registers ranges
    (envelope_constant (length registers) 0) (zero_coordinate_form form)) as [positive|] eqn:POSITIVE; [|discriminate].
  destruct (compile_affine_interval_comparison registers ranges lower
    (envelope_constant (length registers) 0)) as [below|] eqn:BELOW; [|discriminate].
  destruct (compile_affine_interval_comparison registers ranges
    (envelope_constant (length registers) stride) upper) as [above|] eqn:ABOVE; [|discriminate].
  intro SAME; injection SAME as <-; intros WORDS RANGES.
  set (first_value := affine_value (zero_coordinate_form form) values).
  set (low_value := affine_value lower values).
  set (high_value := affine_value upper values).
  assert (TESTS : expression_test positive (Entry ge locals temps memory) (0 <? first_value) /\
    expression_test below (Entry ge locals temps memory) (low_value <? 0) /\
    expression_test above (Entry ge locals temps memory) (stride <? high_value)).
  { repeat split; (eapply compiled_affine_interval_comparison_exact;
      [eassumption|exact WORDS|exact RANGES|]); rewrite ?envelope_constant_value; reflexivity. }
  destruct TESTS as [POS [LOW HIGH]].
  assert (RUN : decision_run (Entry ge locals temps memory)
    (Test positive (Test below (Decision false) (Test above (Decision false) (Decision true))) (Decision false))
    ((0 <? first_value) && negb (low_value <? 0) && negb (stride <? high_value))).
  { eapply run_test; [exact POS|].
    destruct (0 <? first_value); cbn; [|constructor].
    eapply run_test; [exact LOW|].
    destruct (low_value <? 0); cbn; [constructor|].
    eapply run_test; [exact HIGH|]; destruct (stride <? high_value); constructor. }
  split; [eexists; exact RUN|].
  intro ACCEPT; assert (FLAG : (0 <? first_value) && negb (low_value <? 0) && negb (stride <? high_value) = true).
  { eapply pure_tree_determinate; [eapply compile_envelope_forms_width_pure;
      unfold compile_envelope_forms_width; rewrite POSITIVE,BELOW,ABOVE; reflexivity|exact RUN|exact ACCEPT]. }
  rewrite !andb_true_iff,!negb_true_iff,Z.ltb_lt,!Z.ltb_ge in FLAG; tauto.
Qed.

(** Counts precede parameters in the generic envelope. For a one-row source
    the count register is also the first ordinary parameter, hence the repeated
    bound register. This representation is explicit, without a ghost value. *)
Definition compile_parametric_envelope_width stride row context bounds expression : option decision_tree :=
  if in_dec peq row context then None else
  match context,bounds,memory_encode_nary_index (row::context) expression with
  | bound::_,interval::_,Some form =>
    match synthesize_affine_envelope 1 form with
    | Some (lower,upper) =>
      compile_envelope_forms_width (bound::context) (envelope_bounds (interval::bounds)) stride form lower upper
    | None => None end
  | _,_,_ => None end.

Lemma envelope_typed_view context values temps :
  length context = length values -> MemoryNested.A.typed_view context values temps ->
  affine_registers_view context values temps.
Proof.
  revert values; induction context as [|identifier context IH]; intros [|value values] LENGTH VIEW;
    cbn in LENGTH; try discriminate; [constructor|].
  constructor.
  - destruct (VIEW O identifier eq_refl) as [word [WORD SIGNED]]; cbn in SIGNED.
    rewrite <- SIGNED,Int.repr_signed; exact WORD.
  - apply IH; [lia|]; intros n parameter POSITION; apply (VIEW (S n) parameter POSITION).
Qed.
Lemma envelope_within bounds values :
  length bounds = length values -> MemoryNested.A.env_within bounds values ->
  Forall2 (fun value range => fst range <= value <= snd range) values (envelope_bounds bounds).
Proof.
  revert values; induction bounds as [|interval bounds IH]; intros [|value values] LENGTH WITHIN;
    cbn in LENGTH; try discriminate; [constructor|].
  constructor.
  - apply (WITHIN O interval eq_refl).
  - apply IH; [lia|]; intros n next POSITION; apply (WITHIN (S n) next POSITION).
Qed.

Theorem compile_parametric_envelope_width_pure stride row context bounds expression tree :
  compile_parametric_envelope_width stride row context bounds expression = Some tree -> pure_tree tree.
Proof.
  unfold compile_parametric_envelope_width; destruct (in_dec peq row context); [discriminate|].
  destruct context as [|bound parameters],bounds as [|interval bounds]; try discriminate.
  destruct (memory_encode_nary_index _ _) as [form|]; [|discriminate].
  destruct (synthesize_affine_envelope _ _) as [[lower upper]|]; [|discriminate].
  apply compile_envelope_forms_width_pure.
Qed.

(** C_derive and C_guard meet here: actual Boolean execution both terminates
    and, upon acceptance, establishes every iteration's width obligation. *)
Theorem compile_parametric_envelope_width_correct stride row bound parameters bounds expression tree valuation ge locals temps memory :
  compile_parametric_envelope_width stride row (bound::parameters) bounds expression = Some tree ->
  length bounds = length (bound::parameters) ->
  MemoryNested.A.typed_view (bound::parameters) (map valuation (bound::parameters)) temps ->
  MemoryNested.A.env_within bounds (map valuation (bound::parameters)) ->
  0 < valuation bound ->
  (exists answer, decision_run (Entry ge locals temps memory) tree answer) /\
  (decision_run (Entry ge locals temps memory) tree true ->
    0 < memory_source_affine_math (memory_source_set_valuation valuation row 0) expression /\
    forall coordinate, 0 <= coordinate < valuation bound ->
      0 <= memory_source_affine_math (memory_source_set_valuation valuation row coordinate) expression <= stride).
Proof.
  unfold compile_parametric_envelope_width; destruct (in_dec peq row (bound::parameters)) as [|FRESH]; [discriminate|].
  destruct bounds as [|interval bounds]; [discriminate|].
  destruct (memory_encode_nary_index (row::bound::parameters) expression) as [form|] eqn:ENCODE; [|discriminate].
  destruct (synthesize_affine_envelope 1 form) as [[lower upper]|] eqn:ENVELOPE; [|discriminate].
  intro COMPILE; change (compile_envelope_forms_width (bound::bound::parameters)
    (envelope_bounds (interval::interval::bounds)) stride form lower upper = Some tree) in COMPILE.
  intros LENGTH VIEW WITHIN COUNT.
  set (values := map valuation (bound::parameters)).
  assert (WORDS : affine_registers_view (bound::bound::parameters) (valuation bound::values) temps).
  { constructor.
    - destruct (VIEW O bound eq_refl) as [word [WORD SIGNED]]; cbn in SIGNED.
      rewrite <- SIGNED,Int.repr_signed; exact WORD.
    - apply envelope_typed_view; [apply eq_sym,length_map|exact VIEW]. }
  assert (RANGES : Forall2 (fun value range => fst range <= value <= snd range)
    (valuation bound::values) (envelope_bounds (interval::interval::bounds))).
  { apply envelope_within; [unfold values; cbn [length]; rewrite length_map; cbn [length] in LENGTH |- *; lia|].
    apply MemoryNested.A.env_within_cons; [apply (WITHIN O interval eq_refl)|exact WITHIN]. }
  destruct (@compile_envelope_forms_width_correct _ _ _ _ _ _ _ _ ge locals temps memory COMPILE WORDS RANGES)
    as [TOTAL SOUND].
  split; [exact TOTAL|].
  intro ACCEPT; destruct (SOUND ACCEPT) as [POSITIVE [LOW HIGH]].
  split.
  - rewrite zero_coordinate_value in POSITIVE.
    rewrite <- (@envelope_source_instance expression row (bound::parameters) form valuation 0 FRESH ENCODE).
    exact POSITIVE.
  - intros coordinate BOX.
    pose proof (@synthesized_affine_envelope_covers 1 form lower upper [coordinate] [valuation bound] values
      ENVELOPE eq_refl ltac:(constructor; [exact BOX|constructor])) as COVER.
    cbn [app] in COVER.
    rewrite <- (@envelope_source_instance expression row (bound::parameters) form valuation coordinate FRESH ENCODE).
    split; [exact (Z.le_trans _ _ _ LOW (proj1 COVER))|exact (Z.le_trans _ _ _ (proj2 COVER) HIGH)].
Qed.

Print Assumptions envelope_source_instance.
Print Assumptions compile_envelope_forms_width_correct.
Print Assumptions compile_parametric_envelope_width_correct.

Theorem parametric_envelope_refines_width stride row bound parameters bounds expression replacement original valuation ge locals temps memory :
  compile_parametric_envelope_width stride row (bound::parameters) bounds expression = Some replacement ->
  compile_memory_source_width stride row (bound::parameters) bounds expression = Some original ->
  length bounds = length (bound::parameters) ->
  MemoryNested.A.typed_view (bound::parameters) (map valuation (bound::parameters)) temps ->
  MemoryNested.A.env_within bounds (map valuation (bound::parameters)) ->
  0 < valuation bound ->
  decision_run (Entry ge locals temps memory) replacement true ->
  decision_run (Entry ge locals temps memory) original true.
Proof.
  intros NEW OLD ARITY VIEW WITHIN COUNT ACCEPT.
  destruct (@compile_parametric_envelope_width_correct stride row bound parameters bounds expression replacement
    valuation ge locals temps memory NEW ARITY VIEW WITHIN COUNT) as [_ SOUND].
  destruct (SOUND ACCEPT) as [POSITIVE WIDTH].
  unfold compile_memory_source_width,memory_source_endpoints in OLD.
  destruct (memory_source_endpoint_expression row (bound::parameters) (L.Constant 0) expression)
    as [first|] eqn:FIRST; [|discriminate].
  destruct (memory_source_endpoint_expression row (bound::parameters) (L.Sum (L.Var O) (L.Constant (-1))) expression)
    as [last|] eqn:LAST; [|discriminate].
  apply (@MemoryNested.A.lower_test_exact (memory_source_endpoint_test stride first last)
    (bound::parameters) bounds original (map valuation (bound::parameters)) temps ge locals memory true OLD WITHIN VIEW).
  pose proof (@memory_source_endpoint_value expression row (bound::parameters) (L.Constant 0) first valuation FIRST) as FIRST_VALUE.
  pose proof (@memory_source_endpoint_value expression row (bound::parameters)
    (L.Sum (L.Var O) (L.Constant (-1))) last valuation LAST) as LAST_VALUE.
  cbn [L.eval_expr map nth] in FIRST_VALUE,LAST_VALUE.
  replace (valuation bound + -1) with (valuation bound-1) in LAST_VALUE by ring.
  unfold memory_source_endpoint_test; cbn [L.eval_test L.eval_expr map]; rewrite FIRST_VALUE,LAST_VALUE.
  symmetry; rewrite !andb_true_iff,!Z.leb_le.
  pose proof (WIDTH 0 ltac:(lia)); pose proof (WIDTH (valuation bound-1) ltac:(lia)); lia.
Qed.
Print Assumptions parametric_envelope_refines_width.
