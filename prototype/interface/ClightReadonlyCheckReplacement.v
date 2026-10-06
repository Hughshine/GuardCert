From Stdlib Require Import List.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyPreservation ClightRegionBoundary
  ClightReadonlyProjectedCompiler ClightReadonlyLoadedTreeSynthesis.
Set Implicit Arguments.

(** A domain service can replace the executable check while retaining the
    candidate, entry domain, semantic premise and local correctness proof. *)
Definition replace_readonly_condition fe O (observe : fragment_observation -> O -> Prop)
  domain premise original replacement
  (OLD : readonly_condition (readonly_clight_host fe observe) domain premise original)
  (TOTAL : forall entry, domain entry -> exists answer, decision_run entry replacement answer)
  (ACCEPT : forall entry, domain entry -> decision_run entry replacement true -> decision_run entry original true) :
  readonly_condition (readonly_clight_host fe observe) domain premise replacement.
Proof.
  constructor.
  - intros entry DOMAIN; destruct (TOTAL entry DOMAIN) as [answer RUN].
    eapply readonly_decision_run_safe; exact RUN.
  - intros entry DOMAIN; destruct (TOTAL entry DOMAIN) as [answer RUN].
    exists answer,entry; split; [exact RUN|reflexivity].
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro YES; subst answer].
    destruct (readonly_sound OLD entry true entry DOMAIN
      (conj (ACCEPT entry DOMAIN RUN) eq_refl)) as [_ SOUND].
    apply SOUND; reflexivity.
Defined.

Definition staged_readonly_tree first second middle last :=
  decision_bind first (decision_bind second
    (decision_bind middle last (Decision false)) (Decision false)) (Decision false).

Lemma staged_readonly_tree_accept first second middle last entry :
  decision_run entry (staged_readonly_tree first second middle last) true ->
  decision_run entry first true /\ decision_run entry second true /\
    decision_run entry middle true /\ decision_run entry last true.
Proof.
  unfold staged_readonly_tree; intro RUN.
  apply decision_bind_inv in RUN as [[|] [FIRST RUN]]; [|inversion RUN].
  apply decision_bind_inv in RUN as [[|] [SECOND RUN]]; [|inversion RUN].
  apply decision_bind_inv in RUN as [[|] [MIDDLE LAST]]; [auto|inversion LAST].
Qed.
Lemma staged_readonly_tree_run first second middle last entry answer :
  decision_run entry first true -> decision_run entry second true ->
  decision_run entry middle true -> decision_run entry last answer ->
  decision_run entry (staged_readonly_tree first second middle last) answer.
Proof. intros; unfold staged_readonly_tree; repeat (eapply decision_bind_run with (b:=true); [eassumption|]); assumption. Qed.

(** Replace a middle check on the domain established by two earlier checks.
    The suffix can contain partial observations: it is reached only when the
    replacement has established acceptance of the original middle check. *)
Definition replace_readonly_stage fe O (observe : fragment_observation -> O -> Prop)
  domain premise first second original replacement last
  (OLD : readonly_condition (readonly_clight_host fe observe) domain premise
    (staged_readonly_tree first second original last))
  (TOTAL : forall entry, domain entry -> decision_run entry first true -> decision_run entry second true ->
    exists answer, decision_run entry replacement answer)
  (ACCEPT : forall entry, domain entry -> decision_run entry first true -> decision_run entry second true ->
    decision_run entry replacement true -> decision_run entry original true) :
  readonly_condition (readonly_clight_host fe observe) domain premise
    (staged_readonly_tree first second replacement last).
Proof.
  apply replace_readonly_condition with (original:=staged_readonly_tree first second original last) (OLD:=OLD).
  - intros entry DOMAIN.
    destruct (readonly_available OLD entry DOMAIN) as [answer [checked [RUN SAME]]]; subst checked.
    unfold staged_readonly_tree in RUN |- *.
    apply decision_bind_inv in RUN as [[|] [RUN1 RUN]].
    + apply decision_bind_inv in RUN as [[|] [RUN2 RUN]].
      * destruct (TOTAL entry DOMAIN RUN1 RUN2) as [[|] NEW].
        -- pose proof (ACCEPT entry DOMAIN RUN1 RUN2 NEW) as OLD_TRUE.
           apply decision_bind_inv in RUN as [choice [OLD_RUN RUN]].
           assert (CHOICE : choice = true) by
             exact (@readonly_decision_determinate original entry choice true OLD_RUN OLD_TRUE).
           subst choice; exists answer; repeat (eapply decision_bind_run with (b:=true); [eassumption|]); exact RUN.
        -- exists false; eapply decision_bind_run with (b:=true); [exact RUN1|].
           eapply decision_bind_run with (b:=true); [exact RUN2|].
           eapply decision_bind_run with (b:=false); [exact NEW|constructor].
      * exists false; eapply decision_bind_run with (b:=true); [exact RUN1|].
        eapply decision_bind_run with (b:=false); [exact RUN2|constructor].
    + exists false; eapply decision_bind_run with (b:=false); [exact RUN1|constructor].
  - intros entry DOMAIN RUN; apply staged_readonly_tree_accept in RUN as [RUN1 [RUN2 [NEW SUFFIX]]].
    apply staged_readonly_tree_run; try assumption; apply (ACCEPT entry DOMAIN RUN1 RUN2 NEW).
Defined.

Definition preserving_rule_with_check live source (rule : readonly_preserving_clight_rule live source)
  replacement
  (CHECK : forall temps, readonly_condition
    (readonly_clight_host (adapter_entry temps) (boundary_observe (public_exit_ports live)))
    (preserving_domain rule) (preserving_premise rule) replacement) :
  readonly_preserving_clight_rule live source :=
  {| preserving_candidate := preserving_candidate rule;
     preserving_guard := replacement;
     preserving_domain := preserving_domain rule;
     preserving_premise := preserving_premise rule;
     preserving_writes := preserving_writes rule;
     preserving_source_writes := preserving_source_writes rule;
     preserving_check := CHECK;
     preserving_local := preserving_local rule;
     preserving_entry := preserving_entry rule |}.

Print Assumptions replace_readonly_condition.
Print Assumptions preserving_rule_with_check.
Print Assumptions replace_readonly_stage.
