From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightRedundantSet ClightNoWrap CompCertMemoryActions.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightObservedHeaderPrefix
  ClightAffineJointObservation ClightNestedConstantHeaders ClightZeroRmwObservation
  ClightReadonlyTreeFacts ClightReadonlyLoadedTreeSynthesis ClightNestedIndexedObservers.
Import ListNotations.
Set Implicit Arguments.

(** A successful original addition licenses the scalar check. Empty regions
    have no such witness and must bypass the check or supply another license. *)
Lemma signed_rmw_add_operand_defined alpha address ge locals temps memory value :
  eval_expr ge locals temps memory(zero_rmw_rhs alpha(Ederef address type_int32s))value ->
  exists word,temps!alpha=Some(Vint word).
Proof.
  unfold zero_rmw_rhs; intro RUN; apply scalar_binary_inv in RUN as
    [left [right [LEFT [RIGHT OP]]]].
  apply scalar_temp_inv in RIGHT.
  destruct left,right; try discriminate OP; eexists; exact RIGHT.
Qed.

Theorem zero_rmw_original_assignment_licenses_scalar alpha address
  fe ge locals temps memory trace after final outcome :
  exec_stmt fe ge locals temps memory
    (Sassign(Ederef address type_int32s)(zero_rmw_rhs alpha(Ederef address type_int32s)))
    trace after final outcome -> register_domain alpha(Entry ge locals temps memory).
Proof.
  intro RUN; inversion RUN; subst.
  match goal with VALUE:eval_expr _ _ _ _ (zero_rmw_rhs _ _) _ |- _ =>
    eapply signed_rmw_add_operand_defined; exact VALUE end.
Qed.

Definition zero_rmw_condition alpha := register_tree alpha Int.zero.

Theorem zero_rmw_condition_available alpha entry :
  register_domain alpha entry -> exists answer,decision_run entry(zero_rmw_condition alpha)answer.
Proof. intro DOMAIN; eexists; apply register_tree_run; exact DOMAIN. Qed.

Theorem zero_rmw_condition_accept alpha entry :
  register_domain alpha entry -> decision_run entry(zero_rmw_condition alpha)true ->
  (entry_temps entry)!alpha=Some(Vint Int.zero).
Proof.
  intros [word WORD] ACCEPT.
  pose proof(@register_tree_run alpha Int.zero entry ltac:(exists word; exact WORD))as RUN.
  pose proof(readonly_decision_determinate ACCEPT RUN)as FLAG.
  unfold register_flag,temp_word in FLAG; rewrite WORD in FLAG.
  symmetry in FLAG; apply Int.same_if_eq in FLAG; subst word; exact WORD.
Qed.

Theorem zero_rmw_condition_readonly alpha : pure_tree(zero_rmw_condition alpha).
Proof. apply register_tree_pure. Qed.

Definition zero_rmw_presumption fe (alpha:ident) code entry :=
  forall trace after final outcome,
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    code trace after final outcome -> mint32_words_preserved(entry_memory entry)final.

(** C_encode in the existing framework API. The source certificate is checked
    once; acceptance establishes the semantic effect law, not an alias test. *)
Definition zero_rmw_condition_encoding
  (fe:genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
  (O:Type)(observe:fragment_observation -> O -> Prop) alpha code
  (CHECK:check_zero_rmw_control alpha code=true) :
  readonly_condition(readonly_clight_host fe observe)(register_domain alpha)
    (zero_rmw_presumption fe alpha code)(zero_rmw_condition alpha).
Proof.
  constructor.
  - intros entry DOMAIN; destruct(@zero_rmw_condition_available alpha entry DOMAIN)as [answer RUN].
    eapply pure_decision_run_safe; [apply zero_rmw_condition_readonly|exact RUN].
  - intros entry DOMAIN; destruct(@zero_rmw_condition_available alpha entry DOMAIN)as [answer RUN].
    exists answer,entry; split; [exact RUN|reflexivity].
  - intros entry answer checked DOMAIN [RUN SAME]; subst checked; split; [reflexivity|].
    intro ACCEPT; subst answer; intros trace after final outcome SOURCE.
    exact(proj1(@checked_zero_rmw_control_execution alpha fe(entry_ge entry)(entry_env entry)
      (entry_temps entry)(entry_memory entry)code trace after final outcome SOURCE CHECK
      (@zero_rmw_condition_accept alpha entry DOMAIN RUN))).
Defined.

Definition word_valued_observers observers :=
  Forall(fun observer=>exists word,word_observer_value observer=Vint word)observers.

Lemma mint32_words_preserved_observers before after observers :
  mint32_words_preserved before after -> word_valued_observers observers ->
  header_observations_match(map word_observer_snapshot observers)before ->
  header_observations_match(map word_observer_snapshot observers)after.
Proof.
  intros PRESERVE WORDS OBSERVED.
  unfold header_observations_match in *; rewrite Forall_map in *.
  apply Forall_forall; intros observer MEMBER.
  apply Forall_forall with(x:=observer)in WORDS; [|exact MEMBER].
  apply Forall_forall with(x:=observer)in OBSERVED; [|exact MEMBER].
  destruct WORDS as [word VALUE].
  cbn [word_observer_snapshot word_observer_location fst snd location_load]in OBSERVED|-*.
  rewrite VALUE in OBSERVED|-*; apply PRESERVE; exact OBSERVED.
Qed.

Theorem checked_zero_rmw_condition_preserves_observers alpha
  fe ge locals before memory code trace after final outcome observers :
  check_zero_rmw_control alpha code=true -> register_domain alpha(Entry ge locals before memory) ->
  decision_run(Entry ge locals before memory)(zero_rmw_condition alpha)true ->
  word_valued_observers observers ->
  header_observations_match(map word_observer_snapshot observers)memory ->
  exec_stmt fe ge locals before memory code trace after final outcome ->
  header_observations_match(map word_observer_snapshot observers)final.
Proof.
  intros CHECK DOMAIN ACCEPT WORDS OBSERVED RUN.
  eapply mint32_words_preserved_observers; [|exact WORDS|exact OBSERVED].
  apply(proj1(@checked_zero_rmw_control_execution alpha fe ge locals before memory code trace after final outcome
    RUN CHECK(@zero_rmw_condition_accept alpha(Entry ge locals before memory)DOMAIN ACCEPT))).
Qed.

(** Both loaded headers may alias the output, and their raw words may differ.
    The capability is value preservation, independent of address separation. *)
Theorem checked_zero_rmw_condition_preserves_nested_headers alpha shape block offset raw child_raw
  fe ge locals before memory code trace after final outcome :
  check_zero_rmw_control alpha code=true -> register_domain alpha(Entry ge locals before memory) ->
  decision_run(Entry ge locals before memory)(zero_rmw_condition alpha)true ->
  header_observations_match(map word_observer_snapshot(ncs_observers shape block offset raw child_raw))memory ->
  exec_stmt fe ge locals before memory code trace after final outcome ->
  header_observations_match(map word_observer_snapshot(ncs_observers shape block offset raw child_raw))final.
Proof.
  intros CHECK DOMAIN ACCEPT OBSERVED RUN.
  eapply checked_zero_rmw_condition_preserves_observers; eassumption ||
    (unfold word_valued_observers,ncs_observers,nested_indexed_word_observers;
     repeat constructor; eexists; reflexivity).
Qed.

Print Assumptions signed_rmw_add_operand_defined.
Print Assumptions zero_rmw_original_assignment_licenses_scalar.
Print Assumptions zero_rmw_condition_available.
Print Assumptions zero_rmw_condition_accept.
Print Assumptions zero_rmw_condition_readonly.
Print Assumptions zero_rmw_condition_encoding.
Print Assumptions mint32_words_preserved_observers.
Print Assumptions checked_zero_rmw_condition_preserves_observers.
Print Assumptions checked_zero_rmw_condition_preserves_nested_headers.
