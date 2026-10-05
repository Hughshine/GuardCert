From Stdlib Require Import Bool List.
From GuardInterface Require Import GuardInterface GuardedRewrite.
Import ListNotations.
Set Implicit Arguments.

(** A language supplies only constructors and their dispatch/safety laws.
    The framework does not inspect expressions, memory, or source semantics. *)
Record readonly_check_algebra {S} (H : guard_host S) := ReadonlyCheckAlgebra {
  constant_check : bool -> check H;
  then_check : check H -> check H -> check H;
  constant_check_safe : forall value entry, check_safe H (constant_check value) entry;
  constant_check_exact : forall value entry answer checked,
    checks H (constant_check value) entry answer checked <-> answer = value /\ checked = entry;
  then_check_exact : forall first second entry answer checked,
    checks H (then_check first second) entry answer checked <->
      (exists middle, checks H first entry true middle /\ checks H second middle answer checked) \/
      (answer = false /\ checks H first entry false checked);
  then_check_safe : forall first second entry,
    check_safe H first entry ->
    (forall middle, checks H first entry true middle -> check_safe H second middle) ->
    check_safe H (then_check first second) entry
}.

Definition readonly_constant_condition S (H : guard_host S) (A : readonly_check_algebra H) domain :
  readonly_condition H domain (fun _ => True) (constant_check A true).
Proof.
  constructor.
  - intros; apply constant_check_safe.
  - intros entry DOMAIN; exists true, entry; apply constant_check_exact; auto.
  - intros entry answer checked DOMAIN RUN; apply constant_check_exact in RUN.
    destruct RUN as [ANSWER SAME]; split; [exact SAME|intros; exact I].
Defined.

(** The second check is certified on the stronger domain established by the
    first. A refused first check never runs the second and proves no negation. *)
Definition sequence_readonly_conditions S (H : guard_host S) (A : readonly_check_algebra H)
  domain first_premise second_premise first second
  (FIRST : readonly_condition H domain first_premise first)
  (SECOND : readonly_condition H (fun entry => domain entry /\ first_premise entry) second_premise second) :
  readonly_condition H domain (fun entry => first_premise entry /\ second_premise entry)
    (then_check A first second).
Proof.
  constructor.
  - intros entry DOMAIN; apply then_check_safe; [apply (readonly_safe FIRST); exact DOMAIN|].
    intros middle RUN; destruct (readonly_sound FIRST entry true middle DOMAIN RUN) as [SAME SOUND]; subst middle.
    apply (readonly_safe SECOND); split; [exact DOMAIN|apply SOUND; reflexivity].
  - intros entry DOMAIN.
    destruct (readonly_available FIRST entry DOMAIN) as [answer [middle RUN]].
    destruct (readonly_sound FIRST entry answer middle DOMAIN RUN) as [SAME SOUND]; subst middle.
    destruct answer.
    + destruct (readonly_available SECOND entry (conj DOMAIN (SOUND eq_refl))) as [answer [checked NEXT]].
      exists answer, checked; apply then_check_exact; left; exists entry; auto.
    + exists false, entry; apply then_check_exact; right; auto.
  - intros entry answer checked DOMAIN RUN; apply then_check_exact in RUN.
    destruct RUN as [[middle [RUN NEXT]]|[FALSE RUN]].
    + destruct (readonly_sound FIRST entry true middle DOMAIN RUN) as [SAME FIRST_SOUND]; subst middle.
      pose proof (FIRST_SOUND eq_refl) as PREMISE.
      destruct (readonly_sound SECOND entry answer checked (conj DOMAIN PREMISE) NEXT) as [SAME SECOND_SOUND].
      split; [exact SAME|intro ACCEPT; split; [exact PREMISE|apply SECOND_SOUND; exact ACCEPT]].
    + destruct (readonly_sound FIRST entry false checked DOMAIN RUN) as [SAME _].
      split; [exact SAME|intro ACCEPT; congruence].
Defined.

Record condition_stage {S} (H : guard_host S) := ConditionStage {
  stage_condition : check H;
  stage_property : S -> Prop
}.
Fixpoint stage_requirements {S} {H : guard_host S} (stages : list (condition_stage H)) entry : Prop :=
  match stages with [] => True | first :: rest => stage_property first entry /\ stage_requirements rest entry end.
Fixpoint synthesize_condition_stages {S} {H : guard_host S} (A : readonly_check_algebra H)
  (stages : list (condition_stage H)) : check H :=
  match stages with
  | [] => constant_check A true
  | first :: rest => then_check A (stage_condition first) (synthesize_condition_stages A rest)
  end.

Inductive certified_condition_stages {S} (H : guard_host S) :
  (S -> Prop) -> list (condition_stage H) -> Type :=
| certified_stages_nil : forall domain, @certified_condition_stages S H domain []
| certified_stages_cons : forall domain first rest,
    readonly_condition H domain (stage_property first) (stage_condition first) ->
    @certified_condition_stages S H (fun entry => domain entry /\ stage_property first entry) rest ->
    @certified_condition_stages S H domain (first :: rest).
Arguments certified_condition_stages {S} H _ _.

Definition synthesized_stages_readonly_condition S (H : guard_host S) (A : readonly_check_algebra H)
  domain stages (CERTIFICATES : certified_condition_stages H domain stages) :
  readonly_condition H domain (stage_requirements stages) (synthesize_condition_stages A stages).
Proof.
  induction CERTIFICATES; cbn [stage_requirements synthesize_condition_stages].
  - apply readonly_constant_condition.
  - apply sequence_readonly_conditions; assumption.
Defined.
Print Assumptions readonly_constant_condition.
Print Assumptions sequence_readonly_conditions.
Print Assumptions synthesized_stages_readonly_condition.
