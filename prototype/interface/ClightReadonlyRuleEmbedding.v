From Stdlib Require Import List Bool.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightGuard ClightCondition ClightRegionProgress ClightTempFrame ClightTempFootprint ClightStraightLine ClightLoopSyntax.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite ClightRegionBoundary
  ClightReadonlyCompiler ClightReadonlyProjectedCompiler.
Set Implicit Arguments.

(** An exact exit proof is also a proof under any observation relation. The
    actual code/check are unchanged; only the observer is saturated. *)
Lemma exact_clight_local_observed fe O (observe : fragment_observation -> O -> Prop) domain premise source target :
  conditional_equivalence (readonly_clight_host fe (@eq fragment_observation)) domain premise source target ->
  conditional_equivalence (readonly_clight_host fe observe) domain premise source target.
Proof.
  intros LOCAL entry observed DOMAIN; split; intros [raw [RUN OBSERVE]]; exists raw; split; [|exact OBSERVE| |exact OBSERVE].
  - assert (EXACT : runs (readonly_clight_host fe (@eq fragment_observation)) target entry raw)
      by (exists raw; split; [exact RUN|reflexivity]).
    apply (proj1 (LOCAL entry raw DOMAIN)) in EXACT; destruct EXACT as [exit [SOURCE SAME]]; subst exit; exact SOURCE.
  - assert (EXACT : runs (readonly_clight_host fe (@eq fragment_observation)) source entry raw)
      by (exists raw; split; [exact RUN|reflexivity]).
    apply (proj2 (LOCAL entry raw DOMAIN)) in EXACT; destruct EXACT as [exit [TARGET SAME]]; subst exit; exact TARGET.

Qed.

Definition exact_readonly_as_projected live source writes (WRITES : writes_only writes source)
  (rule : readonly_clight_rule source) : readonly_projected_clight_rule live source.
Proof.
  refine {| projected_candidate := readonly_candidate rule; projected_guard := readonly_guard rule;
    projected_domain := readonly_domain rule; projected_premise := readonly_premise rule;
    projected_source_writes := writes; projected_source_write_bound := WRITES |}.
  - intro temps; constructor.
    + exact (readonly_safe (readonly_rule_check rule temps)).
    + exact (readonly_available (readonly_rule_check rule temps)).
    + exact (readonly_sound (readonly_rule_check rule temps)).
  - intro temps; apply exact_clight_local_observed, readonly_rule_local.
  - exact (readonly_rule_entry rule).
Defined.

Theorem exact_projected_replacement live source writes (WRITES : writes_only writes source)
  (rule : readonly_clight_rule source) :
  projected_readonly_replacement (@exact_readonly_as_projected live source writes WRITES rule) =
    readonly_replacement rule.
Proof. reflexivity. Qed.

(** A conservative syntactic temp-write bound for quiet source statements.
    This overapproximates writes by all mentioned temps; it is not a memory
    effect analysis or a minimal liveness certificate. *)
Lemma quiet_source_write_bound source : quiet_statement source = true ->
  writes_only (statement_temps source) source.
Proof.
  induction source; cbn [quiet_statement statement_temps]; intro QUIET; try discriminate; try solve [constructor; cbn; auto].
  - apply andb_true_iff in QUIET as [LEFT RIGHT]; constructor.
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; left; exact IN|apply IHsource1; exact LEFT].
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; right; exact IN|apply IHsource2; exact RIGHT].
  - apply andb_true_iff in QUIET as [LEFT RIGHT]; constructor.
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; right; apply in_or_app; left; exact IN|apply IHsource1; exact LEFT].
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; right; apply in_or_app; right; exact IN|apply IHsource2; exact RIGHT].
  - apply andb_true_iff in QUIET as [LEFT RIGHT]; constructor.
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; left; exact IN|apply IHsource1; exact LEFT].
    + eapply writes_only_weaken; [intros id IN; apply in_or_app; right; exact IN|apply IHsource2; exact RIGHT].
Qed.

Definition embed_quiet_exact_rule live source (rule : readonly_clight_rule source) :
  option (readonly_projected_clight_rule live source).
Proof.
  destruct (Bool.bool_dec (quiet_statement source) true) as [QUIET|]; [|exact None].
  exact (Some (@exact_readonly_as_projected live source (statement_temps source)
    (@quiet_source_write_bound source QUIET) rule)).
Defined.
Print Assumptions exact_clight_local_observed.
Print Assumptions exact_readonly_as_projected.
Print Assumptions exact_projected_replacement.
Print Assumptions quiet_source_write_bound.
