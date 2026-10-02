From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightGuard ClightSyntaxEquality ClightRegionRewrite ClightCountedLoop ClightRegionRule
  ClightProgressClassifier CompCertMemoryEquivalence.
Import ListNotations.
Set Implicit Arguments.

Definition counter_domain iterator bound (s : clight_entry) : Prop :=
  exists x upper, (entry_temps s) ! iterator = Some (Vint x) /\
    (entry_temps s) ! bound = Some (Vint upper).

Lemma counter_condition_pure iterator bound : pure_scalar (counter_condition iterator bound).
Proof. unfold counter_condition; repeat constructor. Qed.

Lemma counter_test_run iterator bound s x upper :
  (entry_temps s) ! iterator = Some (Vint x) ->
  (entry_temps s) ! bound = Some (Vint upper) ->
  expression_test (counter_condition iterator bound) s (Int.lt x upper).
Proof.
  intros X UP; unfold expression_test. exists (Val.of_bool (Int.lt x upper)); split.
  - eapply eval_Ebinop; [constructor; exact X | constructor; exact UP | reflexivity].
  - destruct (Int.lt x upper); reflexivity.
Qed.

Lemma counter_test_domain iterator bound s flag :
  expression_test (counter_condition iterator bound) s flag -> counter_domain iterator bound s.
Proof.
  intros [v [EVAL BOOL]]. apply scalar_binary_inv in EVAL.
  destruct EVAL as [x [upper [X [UP OP]]]].
  apply scalar_temp_inv in X, UP.
  destruct x; destruct upper; try discriminate OP.
  exists i, i0; auto.
Qed.

Lemma counted_loop_entry_test fe ge locals le m iterator bound body le' m' :
  exec_stmt fe ge locals le m (counted_loop iterator bound body) E0 le' m' Out_normal ->
  exists flag, expression_test (counter_condition iterator bound) (Entry ge locals le m) flag.
Proof.
  intro RUN; inversion RUN; subst;
    match goal with HEADER : exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ |- _ =>
      inversion HEADER; subst; eexists; eexists; split; eassumption
    end.
Qed.

Lemma false_header_result fe ge locals le m iterator bound body trace le' m' outcome :
  exec_stmt fe ge locals le m
    (Sifthenelse (counter_condition iterator bound) body Sbreak) trace le' m' outcome ->
  expression_test (counter_condition iterator bound) (Entry ge locals le m) false ->
  trace = E0 /\ le' = le /\ m' = m /\ outcome = Out_break.
Proof.
  intros RUN TEST; inversion RUN; subst.
  assert (HEADER_TEST : expression_test (counter_condition iterator bound)
    (Entry ge locals le m) b) by (eexists; split; eassumption).
  pose proof (pure_test_determinate (counter_condition_pure iterator bound) HEADER_TEST TEST) as FLAG.
  subst b.
  match goal with BREAK : exec_stmt _ _ _ _ _ Sbreak _ _ _ _ |- _ => inversion BREAK; subst end.
  repeat split; reflexivity.
Qed.

Lemma zero_trip_result fe ge locals le m iterator bound body le' m' :
  exec_stmt fe ge locals le m (counted_loop iterator bound body) E0 le' m' Out_normal ->
  expression_test (counter_condition iterator bound) (Entry ge locals le m) false ->
  le' = le /\ m' = m.
Proof.
  intros RUN TEST. inversion RUN; subst.
  all: match goal with HEADER : exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) ?tr ?leH ?mH ?outH |- _ =>
      pose proof (@false_header_result fe ge locals le m iterator bound body tr leH mH outH HEADER TEST)
        as [TRACE [TEMPS [MEMORY OUTCOME]]]
    end.
  all: subst; try solve [split; reflexivity].
  all:
    match goal with BAD : out_normal_or_continue Out_break |- _ => inversion BAD end.
Qed.

Definition zero_trip_decide iterator bound (_ : unit) (s : clight_entry) : option bool :=
  match (entry_temps s) ! iterator, (entry_temps s) ! bound with
  | Some (Vint x), Some (Vint upper) => Some (negb (Int.lt x upper))
  | _, _ => None
  end.

Definition zero_trip_dimension iterator bound :
  property_dimension clight_entry unit (counter_domain iterator bound).
Proof.
  refine {| atom_property := fun _ s => expression_test (counter_condition iterator bound) s false;
    decide_atom := zero_trip_decide iterator bound |}.
  intros atom s flag [x [upper [X UP]]] CHECK.
  unfold zero_trip_decide in CHECK; rewrite X, UP in CHECK; inversion CHECK; subst flag.
  pose proof (@counter_test_run iterator bound s x upper X UP) as RUN.
  destruct (Int.lt x upper) eqn:LT; cbn [negb decision_evidence].
  - intro FALSE. pose proof (pure_test_determinate (counter_condition_pure iterator bound) RUN FALSE).
    discriminate.
  - exact RUN.
Defined.

Definition zero_trip_primitives iterator bound :
  check_primitives decision_test_language (counter_domain iterator bound)
    (decide_atom (zero_trip_dimension iterator bound)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language (counter_domain iterator bound)
    (decide_atom (zero_trip_dimension iterator bound)) (fun _ => Decision true)
    (fun _ => Test (counter_condition iterator bound) (Decision false) (Decision true)) _ _).
  - intros atom s result [x [upper [X UP]]]. cbn [decision_test_language].
    change (decision_run s (Decision true) result <->
      result = checked_valid (zero_trip_decide iterator bound atom s)).
    unfold zero_trip_decide; rewrite X, UP. cbn [checked_valid].
    split; intro RUN; [inversion RUN; reflexivity | subst; constructor].
  - intros atom s result expected [x [upper [X UP]]] CHECK.
    cbn [decision_test_language].
    change (zero_trip_decide iterator bound atom s = Some expected) in CHECK.
    unfold zero_trip_decide in CHECK; rewrite X, UP in CHECK; inversion CHECK; subst expected.
    assert (RUN : decision_run s
      (Test (counter_condition iterator bound) (Decision false) (Decision true))
      (negb (Int.lt x upper))).
    { eapply run_test; [eapply counter_test_run; eauto |].
      destruct (Int.lt x upper); constructor. }
    split.
    + intro OTHER. eapply pure_tree_determinate;
        [constructor; [apply counter_condition_pure | constructor | constructor] | exact OTHER | exact RUN].
    + intro EQ; subst; exact RUN.
Defined.

Definition zero_trip_rule iterator bound body :
  encoded_region_rule (counted_loop iterator bound body) Sskip.
Proof.
  refine {| region_rule_atoms := unit;
    region_rule_domain := counter_domain iterator bound;
    region_rule_dimension := zero_trip_dimension iterator bound;
    region_rule_primitives := zero_trip_primitives iterator bound;
    region_rule_formula := Fact tt |}.
  - intros temps p locals le m le' m' RUN.
    destruct (@counted_loop_entry_test (adapter_entry temps) (globalenv p) locals le m
      iterator bound body le' m' RUN) as [flag TEST].
    eapply counter_test_domain; exact TEST.
  - intros temps p locals le m le' m' RUN EMPTY.
    change (expression_test (counter_condition iterator bound) (Entry (globalenv p) locals le m) false)
      in EMPTY.
    destruct (@zero_trip_result (adapter_entry temps) (globalenv p) locals le m
      iterator bound body le' m' RUN EMPTY) as [TEMPS MEMORY]; subst.
    exists m; split; [constructor | apply memory_equivalent_refl].
Defined.

Definition select_zero_trip (source : statement) : option statement :=
  match propose_counted_shape source with
  | Some (iterator, bound, body) =>
      if statement_eq source (counted_loop iterator bound body)
      then Some (generated_region (zero_trip_rule iterator bound body)) else None
  | None => None
  end.

Theorem select_zero_trip_sound source target : select_zero_trip source = Some target ->
  region_contract source target.
Proof.
  unfold select_zero_trip; destruct (propose_counted_shape source) as [[[iterator bound] body]|];
    try discriminate.
  destruct (statement_eq source (counted_loop iterator bound body)) as [EQ|NE]; try discriminate.
  intro TARGET; inversion TARGET; subst; apply encoded_region_rule_sound.
Qed.

Print Assumptions select_zero_trip_sound.
