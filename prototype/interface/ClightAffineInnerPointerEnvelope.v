From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import ClightCondition ClightSameAddress ClightPureExpr.
From GuardMemory Require Import GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions
  GuardMemoryAffinePointerPairs GuardMemoryLinearPointerSyntax.
From GuardInterface Require Import AffineBoxEnvelope AffineBoxConstants ClightAffineEnvelope
  ClightAffinePointerEnvelope ClightPointerEnvelopePairs ClightParametricEnvelope ClightSourceObservation
  ClightReadonlyLoadedTreeSynthesis ClightConditionComposition.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** C_guard: the second count is supplied by the domain certificate, not by
    an entry temporary. Existing language range checks certify the specialized
    endpoint expressions before the compiler can emit their comparisons. *)
Definition compile_fixed_column_separation column_cap registers limits first second : option decision_tree :=
  match synthesize_affine_envelope 2 first,synthesize_affine_envelope 2 second with
  | Some (first_lower,first_upper),Some (second_lower,second_upper) =>
    match compile_affine_comparison registers limits
        (affine_fix_second column_cap first_upper) (affine_fix_second column_cap second_lower),
      compile_affine_comparison registers limits
        (affine_fix_second column_cap second_upper) (affine_fix_second column_cap first_lower) with
    | Some forward,Some backward => Some (Test forward (Decision true)
        (Test backward (Decision true) (Decision false)))
    | _,_ => None end
  | _,_ => None end.

Theorem compiled_fixed_column_separation_exact column_cap registers limits first second tree
  ge locals temps memory rows parameters answer :
  compile_fixed_column_separation column_cap registers limits first second = Some tree ->
  affine_registers_view registers (rows::parameters) temps ->
  Forall2 (fun value limit => 0 <= value < limit) (rows::parameters) limits ->
  (decision_run (Entry ge locals temps memory) tree answer <->
    answer = affine_box_separation 2 first second (rows::column_cap::parameters)).
Proof.
  unfold compile_fixed_column_separation.
  destruct (synthesize_affine_envelope 2 first) as [[first_lower first_upper]|] eqn:FIRST; [|discriminate].
  destruct (synthesize_affine_envelope 2 second) as [[second_lower second_upper]|] eqn:SECOND; [|discriminate].
  destruct (compile_affine_comparison registers limits
    (affine_fix_second column_cap first_upper) (affine_fix_second column_cap second_lower)) as [forward|] eqn:FORWARD; [|discriminate].
  destruct (compile_affine_comparison registers limits
    (affine_fix_second column_cap second_upper) (affine_fix_second column_cap first_lower)) as [backward|] eqn:BACKWARD; [|discriminate].
  intros ENCODE VIEW RANGES; injection ENCODE as <-.
  unfold affine_box_separation; rewrite FIRST,SECOND; unfold affine_envelopes_disjoint; cbn [fst snd].
  set (up_down := affine_value first_upper (rows::column_cap::parameters) <?
    affine_value second_lower (rows::column_cap::parameters)).
  set (down_up := affine_value second_upper (rows::column_cap::parameters) <?
    affine_value first_lower (rows::column_cap::parameters)).
  assert (FWD : expression_test forward (Entry ge locals temps memory) up_down).
  { apply (proj2 (@compiled_affine_comparison_exact ge locals temps memory registers limits
      (rows::parameters) _ _ forward up_down FORWARD VIEW RANGES)).
    rewrite !affine_fix_second_value; reflexivity. }
  assert (BWD : expression_test backward (Entry ge locals temps memory) down_up).
  { apply (proj2 (@compiled_affine_comparison_exact ge locals temps memory registers limits
      (rows::parameters) _ _ backward down_up BACKWARD VIEW RANGES)).
    rewrite !affine_fix_second_value; reflexivity. }
  assert (RUN : decision_run (Entry ge locals temps memory)
    (Test forward (Decision true) (Test backward (Decision true) (Decision false))) (up_down || down_up)).
  { eapply run_test; [exact FWD|]; destruct up_down; cbn; [constructor|].
    eapply run_test; [exact BWD|]; destruct down_up; constructor. }
  split; [intro ACTUAL; eapply readonly_decision_determinate; eassumption|intros ->; exact RUN].
Qed.

Definition compile_observed_fixed_column_separation column_cap registers limits first_id second_id first second :=
  option_map (fun tree => Test (observed_base_equal first_id second_id) tree (Decision false))
    (compile_fixed_column_separation column_cap registers limits first second).

Theorem compiled_observed_fixed_column_separation_sound column_cap registers limits first_id second_id first second tree
  ge locals temps memory rows parameters :
  compile_observed_fixed_column_separation column_cap registers limits first_id second_id first second = Some tree ->
  observed_pointer_domain [first_id;second_id] (Entry ge locals temps memory) ->
  affine_registers_view registers (rows::parameters) temps ->
  Forall2 (fun value limit => 0 <= value < limit) (rows::parameters) limits ->
  (exists answer, decision_run (Entry ge locals temps memory) tree answer) /\
  (decision_run (Entry ge locals temps memory) tree true ->
    exists block base, temps ! first_id = Some (Vptr block base) /\ temps ! second_id = Some (Vptr block base) /\
    forall left right,
      Forall2 (fun coordinate count => 0 <= coordinate < count) left [rows;column_cap] ->
      Forall2 (fun coordinate count => 0 <= coordinate < count) right [rows;column_cap] ->
      affine_value first (left++parameters) <> affine_value second (right++parameters)).
Proof.
  unfold compile_observed_fixed_column_separation.
  destruct (compile_fixed_column_separation column_cap registers limits first second) as [inner|] eqn:INNER;
    cbn; [|discriminate].
  intros ENCODE OBSERVED VIEW RANGES; injection ENCODE as <-.
  pose proof (proj2 (@compiled_fixed_column_separation_exact column_cap registers limits first second inner
    ge locals temps memory rows parameters
    (affine_box_separation 2 first second (rows::column_cap::parameters)) INNER VIEW RANGES) eq_refl) as RUN.
  pose proof (proj2 (@observed_base_equal_exact first_id second_id (Entry ge locals temps memory)
    (address_accept first_id second_id (Entry ge locals temps memory)) OBSERVED) eq_refl) as TEST.
  split.
  - destruct (address_accept first_id second_id (Entry ge locals temps memory));
      eexists; eapply run_test; [exact TEST|exact RUN|exact TEST|constructor].
  - intro ACCEPT; inversion ACCEPT; subst.
    match goal with LEAF : decision_run _ (if ?choice then inner else Decision false) true |- _ =>
      destruct choice eqn:CHOICE; [|inversion LEAF] end.
    match goal with TEST : expression_test (observed_base_equal _ _) _ true |- _ =>
      apply (proj1 (@observed_base_equal_exact _ _ _ _ OBSERVED)) in TEST;
      symmetry in TEST; apply address_accept_sound in TEST end.
    match goal with SAME : addresses_equal _ _ _ _ |- _ => destruct SAME as [pointer [P1 P2]] end.
    destruct (OBSERVED first_id ltac:(cbn; auto)) as [block [base [BINDING VALID]]].
    assert (POINTER : pointer = Vptr block base) by congruence; subst pointer.
    exists block,base; split; [exact P1|split; [exact P2|]].
    intros left right LEFT RIGHT.
    assert (DISJOINT : affine_box_separation 2 first second (rows::column_cap::parameters) = true)
      by (eapply readonly_decision_determinate; eassumption).
    unfold affine_box_separation in DISJOINT.
    destruct (synthesize_affine_envelope 2 first) as [first_bounds|] eqn:FIRST; [|discriminate].
    destruct (synthesize_affine_envelope 2 second) as [second_bounds|] eqn:SECOND; [|discriminate].
    eapply (@synthesized_affine_envelopes_disjoint 2 first second first_bounds second_bounds
      [rows;column_cap] parameters left right); eassumption || reflexivity.
Qed.

Fixpoint compile_fixed_column_pointer_pairs column_cap registers limits pairs : option decision_tree :=
  match pairs with
  | [] => Some (Decision true)
  | (first,second)::rest =>
    match compile_observed_fixed_column_separation column_cap registers limits
      (memory_nary_access_array first) (memory_nary_access_array second)
      (memory_nary_access_index first) (memory_nary_access_index second),
      compile_fixed_column_pointer_pairs column_cap registers limits rest with
    | Some first,Some rest => Some (decision_bind first rest (Decision false))
    | _,_ => None end
  end.

Definition compile_affine_inner_pointer_envelopes column_cap registers limits operations :=
  compile_fixed_column_pointer_pairs column_cap registers limits
    (memory_affine_access_pairs (memory_linear_pointer_accesses operations)).

Theorem compiled_fixed_column_pointer_pairs_sound column_cap registers limits pairs tree
  ge locals temps memory rows parameters :
  compile_fixed_column_pointer_pairs column_cap registers limits pairs = Some tree ->
  affine_registers_view registers (rows::parameters) temps ->
  Forall2 (fun value limit => 0 <= value < limit) (rows::parameters) limits ->
  (forall pair, In pair pairs -> observed_pointer_domain
    [memory_nary_access_array (fst pair);memory_nary_access_array (snd pair)] (Entry ge locals temps memory)) ->
  (exists answer, decision_run (Entry ge locals temps memory) tree answer) /\
  (decision_run (Entry ge locals temps memory) tree true ->
    Forall (pointer_envelope_pair_separated temps [rows;column_cap] parameters) pairs).
Proof.
  revert tree; induction pairs as [|[first second] rest IH]; intros tree ENCODE VIEW RANGES OBSERVED.
  - injection ENCODE as <-; split; [exists true; constructor|intros; constructor].
  - cbn [compile_fixed_column_pointer_pairs] in ENCODE.
    destruct (compile_observed_fixed_column_separation column_cap registers limits
      (memory_nary_access_array first) (memory_nary_access_array second)
      (memory_nary_access_index first) (memory_nary_access_index second)) as [head|] eqn:HEAD; [|discriminate].
    destruct (compile_fixed_column_pointer_pairs column_cap registers limits rest) as [tail|] eqn:TAIL; [|discriminate].
    injection ENCODE as <-.
    destruct (@compiled_observed_fixed_column_separation_sound column_cap registers limits
      (memory_nary_access_array first) (memory_nary_access_array second)
      (memory_nary_access_index first) (memory_nary_access_index second) head
      ge locals temps memory rows parameters HEAD (OBSERVED (first,second) ltac:(left; reflexivity))
      VIEW RANGES) as [[choice RUN] SOUND].
    destruct (IH tail eq_refl VIEW RANGES
      ltac:(intros pair MEMBER; apply OBSERVED; right; exact MEMBER)) as [[last LAST] REST].
    split.
    + destruct choice; [exists last|exists false]; eapply decision_bind_run;
        [exact RUN|exact LAST|exact RUN|constructor].
    + intro ACCEPT; apply decision_bind_inv in ACCEPT as [[|] [FIRST SECOND]]; [|inversion SECOND].
      constructor; [|apply REST; exact SECOND].
      destruct (SOUND FIRST) as [block [base [P1 [P2 DIFFERENT]]]].
      exists block,base; split; [exact P1|split; [exact P2|]].
      intros left right LEFT RIGHT; rewrite <- !affine_value_source; apply DIFFERENT; assumption.
Qed.

Print Assumptions compiled_fixed_column_separation_exact.
Print Assumptions compiled_observed_fixed_column_separation_sound.
Print Assumptions compiled_fixed_column_pointer_pairs_sound.
