From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr ClightRedundantSet ClightMatrixGuard
  ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion ClightRegionProgress
  ClightStraightLine ClightFrontendLoopProtocol.
From GuardInterface Require Import GuardInterface GuardedRewrite ReadonlyConditionComposition
  ClightReadonlyRewrite ClightReadonlyLoadedTreeSynthesis ClightConditionComposition
  ClightLoadedBoundSyntax ClightLoadedBoundGuard ClightLoadedRectangleRow ClightLoadedRectangleAtoms
  ClightLoadedRectangleGuard ClightLoadedStrideTransport ClightRuntimeStrideBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_stride_preliminary row bound columns :=
  Test (register_guard row Int.zero)
    (Test (loaded_rectangle_active_expr bound 0)
      (Test (register_positive_expr columns) (Decision true) (Decision false)) (Decision false)) (Decision false).
Definition loaded_stride_preliminary_accept row bound columns entry :=
  register_flag row Int.zero entry && loaded_rectangle_active_flag bound 0 entry && register_positive columns entry.
Definition loaded_stride_preliminary_property row bound columns stride entry :=
  register_equals row Int.zero tt entry /\ 0 < Int.signed (loaded_rectangle_word bound entry) /\
  0 < Int.signed (temp_word columns (entry_temps entry)) /\ register_domain stride entry.

Lemma loaded_stride_preliminary_run d array row bound column columns stride body outer_body entry :
  column <> columns -> stride <> column -> flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_stride_domain row bound outer_body entry ->
  decision_run entry (loaded_stride_preliminary row bound columns) (loaded_stride_preliminary_accept row bound columns entry).
Proof.
  intros CM SC BODY OUTER DOMAIN.
  destruct DOMAIN as [[word [upper [q [qofs [ITER [BOUND READ]]]]]] COMPLETE].
  assert (DOMAIN : loaded_stride_domain row bound outer_body entry) by
    (split; [do 4 eexists; repeat split; eassumption|exact COMPLETE]).
  unfold loaded_stride_preliminary, loaded_stride_preliminary_accept.
  eapply run_test; [apply register_expression_test; exists word; exact ITER|].
  destruct (register_flag row Int.zero entry) eqn:ZERO; cbn; [|constructor].
  eapply run_test; [eapply loaded_rectangle_active_test;
    [change (-2147483648 <= 0 <= 2147483647); lia|exact BOUND|exact READ]|].
  destruct (loaded_rectangle_active_flag bound 0 entry) eqn:ACTIVE; cbn; [|constructor].
  assert (N_POS : 0 < Int.signed (loaded_rectangle_word bound entry))
    by (unfold loaded_rectangle_active_flag in ACTIVE; apply Z.ltb_lt in ACTIVE; exact ACTIVE).
  destruct (@loaded_stride_active_domains d array row bound column columns stride body outer_body entry CM SC BODY OUTER DOMAIN
    (@register_flag_evidence row Int.zero entry ltac:(exists word; exact ITER) ZERO) N_POS) as [COLS STRIDE].
  eapply run_test; [apply register_positive_test; exact COLS|].
  destruct (register_positive columns entry); constructor.
Qed.

Lemma loaded_stride_preliminary_sound d array row bound column columns stride body outer_body entry :
  column <> columns -> stride <> column -> flatten_region body = [runtime_stride_store d array row column stride] ->
  flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body] ->
  loaded_stride_domain row bound outer_body entry -> loaded_stride_preliminary_accept row bound columns entry = true ->
  loaded_stride_preliminary_property row bound columns stride entry.
Proof.
  intros CM SC BODY OUTER DOMAIN ACCEPT.
  unfold loaded_stride_preliminary_accept in ACCEPT; repeat rewrite andb_true_iff in ACCEPT.
  destruct ACCEPT as [[ZERO N_POS] M_POS].
  destruct (proj1 DOMAIN) as [word [upper [q [qofs [ITER REST]]]]].
  assert (ROW : register_equals row Int.zero tt entry) by (apply register_flag_evidence; [exists word; exact ITER|exact ZERO]).
  unfold loaded_rectangle_active_flag in N_POS; apply Z.ltb_lt in N_POS.
  apply register_positive_sound in M_POS.
  destruct (@loaded_stride_active_domains d array row bound column columns stride body outer_body entry CM SC BODY OUTER DOMAIN ROW N_POS)
    as [COLS STRIDE].
  unfold loaded_stride_preliminary_property; repeat split; auto.
Qed.

Definition loaded_stride_preliminary_condition (d : rectangle_shape) fe O (observe : fragment_observation -> O -> Prop)
  (array row bound column columns stride : ident) (body outer_body : statement)
  (CM : column <> columns) (SC : stride <> column)
  (BODY : flatten_region body = [runtime_stride_store d array row column stride])
  (OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body]) :
  readonly_condition (readonly_clight_host fe observe) (loaded_stride_domain row bound outer_body)
    (loaded_stride_preliminary_property row bound columns stride) (loaded_stride_preliminary row bound columns).
Proof.
  constructor.
  - intros entry DOMAIN; apply readonly_decision_run_safe with (answer := loaded_stride_preliminary_accept row bound columns entry).
    exact (@loaded_stride_preliminary_run d array row bound column columns stride body outer_body entry CM SC BODY OUTER DOMAIN).
  - intros entry DOMAIN; exists (loaded_stride_preliminary_accept row bound columns entry), entry; split; [|reflexivity].
    exact (@loaded_stride_preliminary_run d array row bound column columns stride body outer_body entry CM SC BODY OUTER DOMAIN).
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    apply (@loaded_stride_preliminary_sound d array row bound column columns stride body outer_body entry CM SC BODY OUTER DOMAIN).
    eapply readonly_decision_determinate;
      [exact (@loaded_stride_preliminary_run d array row bound column columns stride body outer_body entry CM SC BODY OUTER DOMAIN)|exact RUN].
Defined.

Record loaded_stride_model (d : rectangle_shape) := LoadedStrideModel {
  model_stride : Z;
  model_layout_valid : rectangle_layout_valid (loaded_stride_shape d model_stride)
}.
Definition decide_loaded_stride_layout d : {rectangle_layout_valid d}+{~ rectangle_layout_valid d}.
Proof.
  destruct (rectangle_layout_check d) eqn:CHECK.
  - left; exact (rectangle_layout_check_sound d CHECK).
  - right; intro VALID.
    assert (ACCEPT : rectangle_layout_check d = true).
    { unfold rectangle_layout_check, rectangle_layout_valid in *; rewrite !andb_true_iff, !Z.ltb_lt, !Z.leb_le; tauto. }
    congruence.
Defined.
Definition checked_loaded_stride_model d (step : Z) : option (loaded_stride_model d) :=
  match decide_loaded_stride_layout (loaded_stride_shape d step) with
  | left VALID => Some (@LoadedStrideModel d step VALID) | right _ => None end.
Definition checked_loaded_stride_models d steps :=
  fold_right (fun step rest => match checked_loaded_stride_model d (Z.of_nat step) with
    Some model => model :: rest | None => rest end) [] steps.
Definition enumerate_loaded_stride_models d := checked_loaded_stride_models d (seq 1 (Z.to_nat (rectangle_extent d))).
Lemma checked_loaded_stride_model_complete d step : rectangle_layout_valid (loaded_stride_shape d step) ->
  exists model, checked_loaded_stride_model d step = Some model /\ model_stride model = step.
Proof.
  intro VALID.
  unfold checked_loaded_stride_model; destruct (decide_loaded_stride_layout (loaded_stride_shape d step)) as [P|NO];
    [eexists; split; reflexivity|contradiction].
Qed.
Lemma checked_loaded_stride_models_member d steps step model :
  checked_loaded_stride_model d (Z.of_nat step) = Some model -> In step steps ->
  In model (checked_loaded_stride_models d steps).
Proof.
  induction steps as [|head rest IH]; intros CHECK IN; [inversion IN|].
  change (In model (match checked_loaded_stride_model d (Z.of_nat head) with
    Some current => current :: checked_loaded_stride_models d rest | None => checked_loaded_stride_models d rest end)).
  destruct IN as [SAME|IN].
  - subst head; rewrite CHECK; left; reflexivity.
  - destruct (checked_loaded_stride_model d (Z.of_nat head)); [right|]; apply IH; assumption.
Qed.
Theorem enumerate_loaded_stride_models_complete d step : rectangle_layout_valid (loaded_stride_shape d step) ->
  exists model, In model (enumerate_loaded_stride_models d) /\ model_stride model = step.
Proof.
  intro VALID; destruct (@checked_loaded_stride_model_complete d step VALID) as [model [CHECK SAME]].
  pose proof VALID as [E [EM [S [SE PTR]]]]; cbn [loaded_stride_shape rectangle_extent rectangle_stride] in *.
  assert (REPR : Z.of_nat (Z.to_nat step) = step) by (apply Z2Nat.id; lia).
  assert (LOW : (1 <= Z.to_nat step)%nat).
  { change (Z.to_nat 1 <= Z.to_nat step)%nat; apply Z2Nat.inj_le; lia. }
  assert (HIGH : (Z.to_nat step <= Z.to_nat (rectangle_extent d))%nat) by (apply Z2Nat.inj_le; lia).
  exists model; split; [|exact SAME]; unfold enumerate_loaded_stride_models.
  eapply checked_loaded_stride_models_member with (step := Z.to_nat step);
    [rewrite REPR; exact CHECK|apply in_seq; lia].
Qed.

Section MODELS.
Variable d : rectangle_shape.
Variables array row bound column columns stride : ident.
Variables body outer_body : statement.
Hypotheses (RQ : row <> bound) (RC : row <> column) (QC : bound <> column)
  (RM : row <> columns) (CM : column <> columns) (SR : stride <> row) (SC : stride <> column).
Hypotheses (BODY : flatten_region body = [runtime_stride_store d array row column stride])
  (OUTER : flatten_region outer_body = [rectangle_reset column; frontend_counted_loop column columns body]).
Definition loaded_stride_model_guard (model : loaded_stride_model d) :=
  @loaded_rectangle_generated_tree (loaded_stride_shape d (model_stride model)) (model_layout_valid model)
    array row bound column columns (rect_store (loaded_stride_shape d (model_stride model)) array row column)
    (loaded_stride_constant_outer (loaded_stride_shape d (model_stride model)) array row column columns)
    RQ RC QC RM CM eq_refl eq_refl.
Definition loaded_stride_model_property (model : loaded_stride_model d) entry :=
  register_equals stride (Int.repr (model_stride model)) tt entry /\
    loaded_rectangle_property (loaded_stride_shape d (model_stride model)) array row bound columns entry.
Definition loaded_stride_ready entry := loaded_stride_domain row bound outer_body entry /\
  loaded_stride_preliminary_property row bound columns stride entry.

Lemma loaded_stride_model_domain (model : loaded_stride_model d) entry : loaded_stride_ready entry ->
  register_equals stride (Int.repr (model_stride model)) tt entry ->
  loaded_rectangle_domain row bound
    (loaded_stride_constant_outer (loaded_stride_shape d (model_stride model)) array row column columns) entry.
Proof.
  intros [DOMAIN PRELIMINARY] MATCH.
  exact (@loaded_stride_domain_constant (loaded_stride_shape d (model_stride model)) array row bound column columns stride body outer_body entry
    SR SC BODY OUTER DOMAIN MATCH).
Qed.
Definition loaded_stride_model_condition fe O (observe : fragment_observation -> O -> Prop) (model : loaded_stride_model d) :
  readonly_condition (readonly_clight_host fe observe)
    (loaded_rectangle_domain row bound (loaded_stride_constant_outer (loaded_stride_shape d (model_stride model)) array row column columns))
    (loaded_rectangle_property (loaded_stride_shape d (model_stride model)) array row bound columns) (loaded_stride_model_guard model).
Proof. unfold loaded_stride_model_guard; apply loaded_rectangle_generated_condition. Defined.

Fixpoint loaded_stride_dispatch (models : list (loaded_stride_model d)) :=
  match models with [] => Decision false | model :: rest =>
    Test (register_guard stride (Int.repr (model_stride model))) (loaded_stride_model_guard model) (loaded_stride_dispatch rest) end.
Definition loaded_stride_dispatch_property models entry :=
  exists model, In model models /\ loaded_stride_model_property model entry.

Lemma loaded_stride_dispatch_available models entry : loaded_stride_ready entry ->
  exists answer, decision_run entry (loaded_stride_dispatch models) answer.
Proof.
  induction models as [|model rest IH]; intro READY; [exists false; constructor|].
  destruct (proj2 READY) as [_ [_ [_ STRIDE]]].
  pose proof (@register_expression_test stride (Int.repr (model_stride model)) entry STRIDE) as TEST.
  destruct (register_flag stride (Int.repr (model_stride model)) entry) eqn:MATCH.
  - pose proof (@loaded_stride_model_domain model entry READY (@register_flag_evidence stride _ entry STRIDE MATCH)) as DOMAIN.
    destruct (readonly_available (loaded_stride_model_condition (adapter_entry true) eq model) entry DOMAIN) as [answer [checked [RUN SAME]]].
    exists answer; eapply run_test with (b := true); [exact TEST|exact RUN].
  - destruct (IH READY) as [answer RUN]; exists answer; eapply run_test with (b := false); [exact TEST|exact RUN].
Qed.

Lemma loaded_stride_dispatch_sound models entry : loaded_stride_ready entry ->
  decision_run entry (loaded_stride_dispatch models) true -> loaded_stride_dispatch_property models entry.
Proof.
  induction models as [|model rest IH]; intros READY RUN; cbn [loaded_stride_dispatch] in RUN; [inversion RUN|].
  destruct (proj2 READY) as [_ [_ [_ STRIDE]]].
  inversion RUN; subst.
  match goal with TEST : expression_test _ entry ?choice, LEAF : decision_run entry (if ?choice then _ else _) true |- _ =>
    assert (FLAG : choice = register_flag stride (Int.repr (model_stride model)) entry)
      by (eapply readonly_test_determinate; [exact TEST|apply register_expression_test; exact STRIDE]);
    destruct choice end.
  - assert (MATCH : register_equals stride (Int.repr (model_stride model)) tt entry)
      by (apply register_flag_evidence; [exact STRIDE|symmetry; exact FLAG]).
    exists model; split; [left; reflexivity|split; [exact MATCH|]].
    exact (proj2 (readonly_sound (loaded_stride_model_condition (adapter_entry true) eq model) entry true entry
      (@loaded_stride_model_domain model entry READY MATCH) ltac:(split; [assumption|reflexivity])) eq_refl).
  - destruct (IH READY ltac:(assumption)) as [chosen [IN PROP]].
    exists chosen; split; [right; exact IN|exact PROP].
Qed.
Definition loaded_stride_dispatch_condition fe O (observe : fragment_observation -> O -> Prop) models :
  readonly_condition (readonly_clight_host fe observe) loaded_stride_ready
    (loaded_stride_dispatch_property models) (loaded_stride_dispatch models).
Proof.
  constructor.
  - intros entry READY; destruct (loaded_stride_dispatch_available models READY) as [answer RUN].
    eapply readonly_decision_run_safe; exact RUN.
  - intros entry READY; destruct (loaded_stride_dispatch_available models READY) as [answer RUN].
    exists answer, entry; split; [exact RUN|reflexivity].
  - intros entry answer checked READY [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    exact (loaded_stride_dispatch_sound models READY RUN).
Defined.
Definition loaded_stride_tree models :=
  decision_bind (loaded_stride_preliminary row bound columns) (loaded_stride_dispatch models) (Decision false).
Definition loaded_stride_property models entry :=
  loaded_stride_preliminary_property row bound columns stride entry /\ loaded_stride_dispatch_property models entry.
Definition loaded_stride_condition fe O (observe : fragment_observation -> O -> Prop) models :
  readonly_condition (readonly_clight_host fe observe) (loaded_stride_domain row bound outer_body)
    (loaded_stride_property models) (loaded_stride_tree models).
Proof.
  unfold loaded_stride_tree, loaded_stride_property.
  exact (@sequence_readonly_conditions clight_entry (readonly_clight_host fe observe) (clight_readonly_check_algebra fe observe)
    (loaded_stride_domain row bound outer_body) (loaded_stride_preliminary_property row bound columns stride)
    (loaded_stride_dispatch_property models) (loaded_stride_preliminary row bound columns) (loaded_stride_dispatch models)
    (@loaded_stride_preliminary_condition d fe O observe array row bound column columns stride body outer_body CM SC BODY OUTER)
    (loaded_stride_dispatch_condition fe observe models)).
Defined.
End MODELS.

Print Assumptions loaded_stride_preliminary_condition.
Print Assumptions checked_loaded_stride_model_complete.
Print Assumptions checked_loaded_stride_models_member.
Print Assumptions enumerate_loaded_stride_models_complete.
Print Assumptions loaded_stride_model_domain.
Print Assumptions loaded_stride_dispatch_available.
Print Assumptions loaded_stride_dispatch_sound.
Print Assumptions loaded_stride_dispatch_condition.
Print Assumptions loaded_stride_condition.
