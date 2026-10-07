From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightRedundantSet ClightCountedLoop.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryRecursiveDomain GuardMemoryIntervalBox
  GuardMemoryIntervalGuard GuardMemoryWindowParameterGuard GuardMemoryTripleGuard GuardMemoryTensorBoxExpressions
  GuardMemoryTensorSourceRegion.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeFacts.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition tensor_profile_interval bound := MemoryNested.A.Interval(fst bound)(snd bound-1).
Definition tensor_profile_valid profile := forallb(fun bound=>MemoryNested.A.interval_valid(tensor_profile_interval bound))profile.
Lemma tensor_profile_signed profile : tensor_profile_valid profile=true ->
  Forall(fun bound=>signed_range(fst bound) /\ signed_range(snd bound-1))profile.
Proof.
  intro VALID; apply Forall_forall; intros [lower upper] MEMBER; unfold tensor_profile_valid in VALID.
  apply forallb_forall with(x:=(lower,upper))in VALID; [|exact MEMBER].
  unfold MemoryNested.A.interval_valid,tensor_profile_interval in VALID; cbn in VALID.
  repeat rewrite andb_true_iff in VALID; repeat rewrite Z.leb_le in VALID; unfold signed_range; cbn; lia.
Qed.
Lemma tensor_profile_within profile values : interval_ranges profile values ->
  MemoryNested.A.env_within(map tensor_profile_interval profile)values.
Proof.
  intro RANGES; induction RANGES as [|[lower upper] value profile values RANGE RANGES IH];
    intros [|index] bound LOOKUP; cbn in LOOKUP; try discriminate.
  - inversion LOOKUP; subst bound; unfold MemoryNested.A.contains,tensor_profile_interval; cbn; cbn in RANGE; lia.
  - exact(IH index bound LOOKUP).
Qed.
Lemma tensor_parameter_view layout entry : Forall(fun identifier=>register_domain identifier entry)layout ->
  MemoryNested.A.typed_view layout(memory_recursive_parameters layout(entry_temps entry))(entry_temps entry).
Proof.
  intros WORDS index identifier LOOKUP; apply Forall_forall with(x:=identifier)in WORDS; [|eapply nth_error_In; exact LOOKUP].
  destruct WORDS as [word WORD]; exists word; split; [exact WORD|].
  unfold memory_recursive_parameters.
  assert(VALUE:nth_error(map(fun identifier=>Int.signed(temp_word identifier(entry_temps entry)))layout)index=Some(Int.signed word)).
  { rewrite nth_error_map,LOOKUP; cbn; unfold temp_word; rewrite WORD; reflexivity. }
  symmetry; apply nth_error_nth with(d:=0)in VALUE; exact VALUE.
Qed.

(** A terminal arithmetic check needs its input profile only on the accepted
    prefix path.  Requiring it on refused paths would discard short-circuiting. *)
Theorem tensor_profile_tree_exact profile layout terminal entry accepted :
  Forall(fun identifier=>register_domain identifier entry)layout ->
  (window_parameters_accept profile layout entry=true -> forall flag,decision_run entry terminal flag <-> flag=accepted) ->
  forall flag,decision_run entry(window_parameters_tree profile layout terminal)flag <->
    flag=window_parameters_accept profile layout entry && accepted.
Proof.
  revert layout; induction profile as [|[lower upper] profile IH];
    intros [|identifier layout] WORDS TERMINAL flag; cbn [window_parameters_tree window_parameters_accept] in *.
  - apply TERMINAL; reflexivity.
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - inversion WORDS; subst; rewrite <-andb_assoc; apply memory_guard_gate_exact;
      [apply signed_interval_encoding_exact; assumption|].
    intro ACCEPT; apply IH; [assumption|].
    intro ALL; apply TERMINAL; rewrite ACCEPT,ALL; reflexivity.
Qed.
Lemma tensor_profile_tree_pure profile layout terminal : pure_tree terminal ->
  pure_tree(window_parameters_tree profile layout terminal).
Proof.
  revert layout; induction profile as [|[lower upper] profile IH]; intros [|identifier layout] PURE;
    cbn [window_parameters_tree].
  - exact PURE.
  - constructor.
  - constructor.
  - apply pure_decision_bind; [apply signed_interval_pure|apply IH; exact PURE|constructor].
Qed.

Definition compile_tensor_box_guard layout profile axes scalars dimensions accesses :=
  if Nat.eqb(length layout)(length profile)&&tensor_profile_valid profile then
    match tensor_box_entry_test layout axes scalars dimensions accesses with
    | Some test=>MemoryNested.A.lower_test layout(map tensor_profile_interval profile)test
    | None=>None end else None.
Lemma compile_tensor_box_guard_certificate layout profile axes scalars dimensions accesses tree :
  compile_tensor_box_guard layout profile axes scalars dimensions accesses=Some tree ->
  tensor_profile_valid profile=true /\ exists test,
    tensor_box_entry_test layout axes scalars dimensions accesses=Some test /\
    MemoryNested.A.lower_test layout(map tensor_profile_interval profile)test=Some tree.
Proof.
  unfold compile_tensor_box_guard; destruct(Nat.eqb(length layout)(length profile)&&tensor_profile_valid profile)eqn:STATIC;
    [|discriminate].
  apply andb_true_iff in STATIC as [_ VALID].
  destruct(tensor_box_entry_test layout axes scalars dimensions accesses)as [test|]eqn:TEST; [|discriminate].
  intro LOWER; split; [exact VALID|exists test; split; [reflexivity|exact LOWER]].
Qed.
Lemma compile_tensor_box_guard_pure layout profile axes scalars dimensions accesses tree :
  compile_tensor_box_guard layout profile axes scalars dimensions accesses=Some tree -> pure_tree tree.
Proof.
  intro COMPILE; destruct(@compile_tensor_box_guard_certificate layout profile axes scalars dimensions accesses tree COMPILE)as [_ [test [_ LOWER]]].
  eapply MemoryNested.A.lower_test_pure; exact LOWER.
Qed.

Definition tensor_box_word_valuation temps identifier := Int.signed(temp_word identifier temps).
Definition tensor_box_entry_flag (layout:list ident) axes scalars dimensions accesses entry := forallb(fun terms=>
  tensor_coordinate_box_check(tensor_box_ranges axes scalars(tensor_box_word_valuation(entry_temps entry)))
    (map(tensor_box_dimension_value(tensor_box_word_valuation(entry_temps entry)))dimensions)terms)accesses.
Definition tensor_box_checked_tree profile layout tree := window_parameters_tree profile layout tree.
Definition tensor_box_checked_flag profile layout axes scalars dimensions accesses entry :=
  window_parameters_accept profile layout entry && tensor_box_entry_flag layout axes scalars dimensions accesses entry.
Theorem tensor_box_checked_exact layout profile axes scalars dimensions accesses tree entry :
  compile_tensor_box_guard layout profile axes scalars dimensions accesses=Some tree ->
  Forall(fun identifier=>register_domain identifier entry)layout ->
  Forall(fun identifier=>0<tensor_box_word_valuation(entry_temps entry)identifier)axes ->
  forall flag,decision_run entry(tensor_box_checked_tree profile layout tree)flag <->
    flag=tensor_box_checked_flag profile layout axes scalars dimensions accesses entry.
Proof.
  intros COMPILE WORDS POSITIVE; destruct(@compile_tensor_box_guard_certificate layout profile axes scalars dimensions accesses tree COMPILE)as [VALID [test [ENCODE LOWER]]].
  unfold tensor_box_checked_tree,tensor_box_checked_flag; apply tensor_profile_tree_exact; [exact WORDS|].
  intro PROFILE; pose proof(@window_parameters_accept_sound profile layout entry(@tensor_profile_signed profile VALID)PROFILE)as RANGES.
  unfold tensor_box_entry_flag.
  rewrite <-(@tensor_box_entry_value layout axes scalars dimensions accesses test
    (tensor_box_word_valuation(entry_temps entry))POSITIVE ENCODE).
  destruct entry as [ge locals temps memory]; intro flag.
  eapply MemoryNested.A.lower_test_exact; [exact LOWER|apply tensor_profile_within; exact RANGES|apply tensor_parameter_view; exact WORDS].
Qed.
Theorem tensor_box_checked_condition fe O(observe:fragment_observation->O->Prop)
    layout profile axes scalars dimensions accesses tree :
  compile_tensor_box_guard layout profile axes scalars dimensions accesses=Some tree ->
  readonly_condition(readonly_clight_host fe observe)
    (fun entry=>Forall(fun identifier=>register_domain identifier entry)layout /\
      Forall(fun identifier=>0<tensor_box_word_valuation(entry_temps entry)identifier)axes)
    (fun entry=>tensor_box_checked_flag profile layout axes scalars dimensions accesses entry=true)
    (tensor_box_checked_tree profile layout tree).
Proof.
  intro COMPILE; assert(PURE:pure_tree(tensor_box_checked_tree profile layout tree))by
    (apply tensor_profile_tree_pure; eapply compile_tensor_box_guard_pure; exact COMPILE).
  constructor.
  - intros entry [WORDS POSITIVE]; eapply pure_decision_run_safe; [exact PURE|].
    apply tensor_box_checked_exact with(axes:=axes)(scalars:=scalars)(dimensions:=dimensions)(accesses:=accesses);
      [exact COMPILE|exact WORDS|exact POSITIVE|reflexivity].
  - intros entry [WORDS POSITIVE]; exists(tensor_box_checked_flag profile layout axes scalars dimensions accesses entry),entry;
      split; [|reflexivity].
    apply tensor_box_checked_exact with(axes:=axes)(scalars:=scalars)(dimensions:=dimensions)(accesses:=accesses);
      [exact COMPILE|exact WORDS|exact POSITIVE|reflexivity].
  - intros entry flag checked [WORDS POSITIVE] [RUN SAME]; split; [exact SAME|].
    intro ACCEPT; subst flag; symmetry.
    apply tensor_box_checked_exact with(tree:=tree); assumption.
Qed.
Print Assumptions tensor_profile_signed.
Print Assumptions tensor_profile_tree_exact.
Print Assumptions compile_tensor_box_guard_certificate.
Print Assumptions tensor_box_checked_exact.
Print Assumptions tensor_box_checked_condition.
