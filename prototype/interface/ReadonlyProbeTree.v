From Stdlib Require Import Bool List.
From GuardInterface Require Import GuardInterface GuardedRewrite.
Import ListNotations.
Set Implicit Arguments.

(** The framework treats each probe as an opaque key with a partial Boolean
    semantics. Undefined probes need not be made globally available. The
    language owes deterministic results and the concrete compilation bridge. *)
Record readonly_probe_semantics (S Probe : Type) := ReadonlyProbeSemantics {
  probe_test : Probe -> S -> bool -> Prop;
  probe_test_determinate : forall probe entry first second,
    probe_test probe entry first -> probe_test probe entry second -> first = second
}.

Inductive readonly_probe_tree (Probe : Type) :=
| ProbeDecision : bool -> readonly_probe_tree Probe
| ProbeTest : Probe -> readonly_probe_tree Probe -> readonly_probe_tree Probe -> readonly_probe_tree Probe.
Arguments ProbeDecision {Probe} _.
Arguments ProbeTest {Probe} _ _ _.

Inductive probe_tree_run {S Probe} (L : readonly_probe_semantics S Probe) (entry : S) :
  readonly_probe_tree Probe -> bool -> Prop :=
| probe_run_decision : forall answer, probe_tree_run L entry (ProbeDecision answer) answer
| probe_run_test : forall probe yes no choice answer,
    probe_test L probe entry choice -> probe_tree_run L entry (if choice then yes else no) answer ->
    probe_tree_run L entry (ProbeTest probe yes no) answer.

Fixpoint probe_tree_safe {S Probe} (L : readonly_probe_semantics S Probe) tree entry : Prop :=
  match tree with
  | ProbeDecision _ => True
  | ProbeTest probe yes no =>
    (exists choice, probe_test L probe entry choice) /\
    forall choice, probe_test L probe entry choice -> probe_tree_safe L (if choice then yes else no) entry
  end.

Fixpoint lookup_probe_fact {Probe} (equal : forall first second : Probe, {first=second}+{first<>second})
  (probe : Probe) (facts : list (Probe * bool)) : option bool :=
  match facts with
  | [] => None
  | (known,answer)::rest => if equal probe known then Some answer else lookup_probe_fact equal probe rest
  end.
Definition probe_facts_hold {S Probe} (L : readonly_probe_semantics S Probe) facts entry :=
  forall probe answer, In (probe,answer) facts -> probe_test L probe entry answer.

Lemma lookup_probe_fact_sound S Probe (L : readonly_probe_semantics S Probe) equal facts entry probe answer :
  probe_facts_hold L facts entry -> lookup_probe_fact equal probe facts = Some answer -> probe_test L probe entry answer.
Proof.
  induction facts as [|[known value] rest IH]; cbn; intros HOLD LOOKUP; [discriminate|].
  destruct (equal probe known) as [SAME|DIFFERENT].
  - inversion LOOKUP; subst; apply HOLD; left; reflexivity.
  - apply IH; [intros key bit IN; apply HOLD; right; exact IN|exact LOOKUP].
Qed.

Lemma probe_facts_extend S Probe (L : readonly_probe_semantics S Probe) facts entry probe answer :
  probe_facts_hold L facts entry -> probe_test L probe entry answer -> probe_facts_hold L ((probe,answer)::facts) entry.
Proof.
  intros HOLD TEST key bit [SAME|IN]; [inversion SAME; subst; exact TEST|apply HOLD; exact IN].
Qed.

(** Facts are compile-time path evidence. No result cache is inserted into
    the runtime check, and refusal is not interpreted as a negated premise. *)
Fixpoint simplify_probe_tree {Probe} (equal : forall first second : Probe, {first=second}+{first<>second})
  tree facts : readonly_probe_tree Probe :=
  match tree with
  | ProbeDecision answer => ProbeDecision answer
  | ProbeTest probe yes no => match lookup_probe_fact equal probe facts with
    | Some true => simplify_probe_tree equal yes facts
    | Some false => simplify_probe_tree equal no facts
    | None => ProbeTest probe (simplify_probe_tree equal yes ((probe,true)::facts))
        (simplify_probe_tree equal no ((probe,false)::facts))
    end
  end.

Theorem simplified_probe_tree_run S Probe (L : readonly_probe_semantics S Probe) equal tree :
  forall facts entry answer, probe_facts_hold L facts entry ->
  (probe_tree_run L entry (simplify_probe_tree equal tree facts) answer <-> probe_tree_run L entry tree answer).
Proof.
  induction tree as [value|probe yes YES no NO]; intros facts entry answer HOLD; cbn [simplify_probe_tree].
  - reflexivity.
  - destruct (lookup_probe_fact equal probe facts) as [known|] eqn:KNOWN.
    + pose proof (@lookup_probe_fact_sound S Probe L equal facts entry probe known HOLD KNOWN) as TEST.
      destruct known; split.
      * intro RUN; eapply probe_run_test with (choice := true); [exact TEST|apply (proj1 (YES facts entry answer HOLD)); exact RUN].
      * intro RUN; inversion RUN; subst.
        match goal with CHECK : probe_test L probe entry ?choice |- _ =>
          assert (choice = true) by (eapply probe_test_determinate; [exact CHECK|exact TEST]); subst choice end.
        apply (proj2 (YES facts entry answer HOLD)); assumption.
      * intro RUN; eapply probe_run_test with (choice := false); [exact TEST|apply (proj1 (NO facts entry answer HOLD)); exact RUN].
      * intro RUN; inversion RUN; subst.
        match goal with CHECK : probe_test L probe entry ?choice |- _ =>
          assert (choice = false) by (eapply probe_test_determinate; [exact CHECK|exact TEST]); subst choice end.
        apply (proj2 (NO facts entry answer HOLD)); assumption.
    + split; intro RUN; inversion RUN; subst.
      * match goal with CHECK : probe_test L probe entry ?choice,
          LEAF : probe_tree_run L entry (if ?choice then _ else _) answer |- _ =>
          eapply probe_run_test; [exact CHECK|]; destruct choice;
          [apply (proj1 (YES _ entry answer (@probe_facts_extend S Probe L facts entry probe true HOLD CHECK))); exact LEAF|
           apply (proj1 (NO _ entry answer (@probe_facts_extend S Probe L facts entry probe false HOLD CHECK))); exact LEAF] end.
      * match goal with CHECK : probe_test L probe entry ?choice,
          LEAF : probe_tree_run L entry (if ?choice then _ else _) answer |- _ =>
          eapply probe_run_test; [exact CHECK|]; destruct choice;
          [apply (proj2 (YES _ entry answer (@probe_facts_extend S Probe L facts entry probe true HOLD CHECK))); exact LEAF|
           apply (proj2 (NO _ entry answer (@probe_facts_extend S Probe L facts entry probe false HOLD CHECK))); exact LEAF] end.
Qed.

Theorem simplified_probe_tree_safe S Probe (L : readonly_probe_semantics S Probe) equal tree :
  forall facts entry, probe_facts_hold L facts entry -> probe_tree_safe L tree entry ->
  probe_tree_safe L (simplify_probe_tree equal tree facts) entry.
Proof.
  induction tree as [value|probe yes YES no NO]; intros facts entry HOLD SAFE; cbn [simplify_probe_tree]; [exact I|].
  destruct SAFE as [DEFINED NEXT]; destruct (lookup_probe_fact equal probe facts) as [known|] eqn:KNOWN.
  - pose proof (@lookup_probe_fact_sound S Probe L equal facts entry probe known HOLD KNOWN) as TEST.
    destruct known; [apply YES|apply NO];
      [exact HOLD|exact (NEXT true TEST)|exact HOLD|exact (NEXT false TEST)].
  - split; [exact DEFINED|].
    intros choice TEST; destruct choice; [apply YES|apply NO];
      [apply probe_facts_extend; assumption|exact (NEXT true TEST)|
       apply probe_facts_extend; assumption|exact (NEXT false TEST)].
Qed.

Record readonly_probe_compiler S (H : guard_host S) Probe (L : readonly_probe_semantics S Probe) := ReadonlyProbeCompiler {
  compile_probe_tree : readonly_probe_tree Probe -> check H;
  probe_compilation_exact : forall tree entry answer checked,
    checks H (compile_probe_tree tree) entry answer checked <-> probe_tree_run L entry tree answer /\ checked=entry;
  probe_compilation_safe : forall tree entry,
    check_safe H (compile_probe_tree tree) entry <-> probe_tree_safe L tree entry
}.

Definition simplified_probe_condition S (H : guard_host S) Probe (L : readonly_probe_semantics S Probe)
  (C : readonly_probe_compiler H L) equal tree domain premise
  (G : readonly_condition H domain premise (compile_probe_tree C tree)) :
  readonly_condition H domain premise (compile_probe_tree C (simplify_probe_tree equal tree [])).
Proof.
  assert (EMPTY : forall entry, probe_facts_hold L [] entry) by (intros entry probe answer IN; inversion IN).
  constructor.
  - intros entry DOMAIN; apply (proj2 (probe_compilation_safe C _ _)).
    apply simplified_probe_tree_safe; [apply EMPTY|apply (proj1 (probe_compilation_safe C _ _)); apply (readonly_safe G); exact DOMAIN].
  - intros entry DOMAIN; destruct (readonly_available G entry DOMAIN) as [answer [checked CHECK]].
    apply (proj1 (probe_compilation_exact C _ _ _ _)) in CHECK as [RUN SAME]; subst checked.
    exists answer, entry; apply (proj2 (probe_compilation_exact C _ _ _ _)); split; [|reflexivity].
    apply (proj2 (@simplified_probe_tree_run S Probe L equal tree [] entry answer (EMPTY entry))); exact RUN.
  - intros entry answer checked DOMAIN CHECK.
    apply (proj1 (probe_compilation_exact C _ _ _ _)) in CHECK as [RUN SAME].
    apply (readonly_sound G entry answer checked DOMAIN).
    apply (proj2 (probe_compilation_exact C _ _ _ _)); split; [|exact SAME].
    apply (proj1 (@simplified_probe_tree_run S Probe L equal tree [] entry answer (EMPTY entry))); exact RUN.
Defined.

Print Assumptions lookup_probe_fact_sound.
Print Assumptions probe_facts_extend.
Print Assumptions simplified_probe_tree_run.
Print Assumptions simplified_probe_tree_safe.
Print Assumptions simplified_probe_condition.
