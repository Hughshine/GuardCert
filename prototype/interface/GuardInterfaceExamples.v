From Stdlib Require Import Bool ZArith Lia.
From Guard Require Import AbstractGuard.
From GuardInterface Require Import GuardInterface.
Open Scope Z_scope.
Set Implicit Arguments.

(** A second, small host: commands are mathematical functions, and checks may
    overwrite private scratch. It imports no CompCert or memory definitions. *)
Definition toy_state := (Z * Z)%type.
Definition toy_code := toy_state -> Z.
Definition toy_check := toy_state -> (bool * toy_state).
Definition toy_runs (body : toy_code) state observed := observed = body state.
Definition toy_checks (test : toy_check) state accepted checked :=
  accepted = fst (test state) /\ checked = snd (test state).
Definition toy_check_safe (test : toy_check) state := exists result, test state = result.
Definition toy_select (test : toy_check) (yes no : toy_code) : toy_code :=
  fun state => let '(accepted, checked) := test state in
    (if accepted then yes else no) checked.

Lemma toy_select_exact test yes no state observed :
  toy_runs (toy_select test yes no) state observed <->
  exists accepted checked, toy_checks test state accepted checked /\
    toy_runs (if accepted then yes else no) checked observed.
Proof.
  unfold toy_runs, toy_select, toy_checks.
  destruct (test state) as [accepted checked]; cbn; split.
  - intro RUN; exists accepted, checked; auto.
  - intros [answer [after [[ANSWER AFTER] RUN]]]; subst answer after; exact RUN.
Qed.

Definition toy_host : guard_host toy_state :=
  {| code := toy_code; check := toy_check; observation := Z;
     runs := toy_runs; checks := toy_checks; check_safe := toy_check_safe; select := toy_select;
     select_exact := toy_select_exact |}.

Definition public_entry (entry checked : toy_state) := fst entry = fst checked.
Definition nonnegative (entry : toy_state) := 0 <= fst entry.
Definition absolute_source : toy_code := fun state => Z.abs (fst state).
Definition positive_candidate : toy_code := fun state => fst state.
Definition sign_check : toy_check := fun state => (Z.geb (fst state) 0, (fst state, 42)).

Definition sign_certificate : guard_certificate toy_host (fun _ => True)
  nonnegative public_entry public_entry sign_check.
Proof.
  constructor.
  - intros entry _; exists (sign_check entry); reflexivity.
  - intros entry _; exists (fst (sign_check entry)), (snd (sign_check entry)); split; reflexivity.
  - intros entry accepted checked _ [ANSWER AFTER]; subst accepted checked.
    cbn; destruct (Z.geb (fst entry) 0) eqn:SIGN.
    + split; [apply Z.geb_le in SIGN; exact SIGN|reflexivity].
    + reflexivity.
Defined.

Definition absolute_certificate : conditional_certificate toy_host (fun _ => True)
  nonnegative public_entry public_entry eq absolute_source positive_candidate absolute_source.
Proof.
  constructor.
  - intros entry checked target _ PREMISE ENTRY RUN.
    exists (Z.abs (fst entry)); split; [reflexivity|].
    cbn in RUN; unfold nonnegative in PREMISE; unfold public_entry in ENTRY.
    rewrite Z.abs_eq by exact PREMISE; rewrite RUN; symmetry; exact ENTRY.
  - intros entry checked target _ ENTRY RUN.
    exists (Z.abs (fst entry)); split; [reflexivity|].
    change (target = Z.abs (fst checked)) in RUN.
    change (target = Z.abs (fst entry)).
    unfold public_entry in ENTRY; rewrite RUN, <- ENTRY; reflexivity.
Defined.

Definition absolute_preservation : preservation_certificate toy_host (fun _ => True)
  nonnegative public_entry public_entry eq absolute_source positive_candidate absolute_source.
Proof.
  constructor.
  - intros entry checked original _ PREMISE ENTRY SOURCE.
    exists (fst checked); split; [reflexivity|].
    change (original = Z.abs (fst entry)) in SOURCE.
    change (fst checked = original).
    unfold nonnegative in PREMISE; unfold public_entry in ENTRY.
    rewrite SOURCE, Z.abs_eq by exact PREMISE; symmetry; exact ENTRY.
  - intros entry checked original _ ENTRY SOURCE.
    exists (Z.abs (fst checked)); split; [reflexivity|].
    change (original = Z.abs (fst entry)) in SOURCE.
    change (Z.abs (fst checked) = original).
    unfold public_entry in ENTRY; rewrite SOURCE, <- ENTRY; reflexivity.
Defined.

Theorem absolute_guarded_refinement :
  local_refinement toy_host (fun _ => True) eq
    (select toy_host sign_check positive_candidate absolute_source) absolute_source.
Proof. eapply guardify_refinement; [exact sign_certificate|exact absolute_certificate]. Qed.

Definition toy_context := (toy_state * (Z -> Z))%type.
Definition toy_program := (toy_state * (toy_code * (Z -> Z)))%type.
Definition toy_plug (surrounding : toy_context) (body : toy_code) : toy_program :=
  (fst surrounding, (body, snd surrounding)).
Definition toy_program_runs (p : toy_program) observed :=
  observed = (snd (snd p)) ((fst (snd p)) (fst p)).

Definition toy_context_certificate : context_certificate toy_host eq.
Proof.
  refine (@ContextCertificate toy_state toy_host eq toy_context toy_program Z
    toy_plug toy_program_runs eq
    (fun surrounding _ domain => domain (fst surrounding))
    (fun _ _ _ _ => True) _).
  intros surrounding source target domain DOMAIN _ LOCAL observed RUN.
  destruct (LOCAL (fst surrounding) (target (fst surrounding)) DOMAIN eq_refl)
    as [original [SOURCE RELATED]].
  cbn in SOURCE; rewrite SOURCE in RELATED.
  exists ((snd surrounding) (source (fst surrounding))); split; [reflexivity|].
  change (observed = (snd surrounding) (target (fst surrounding))) in RUN.
  change (observed = (snd surrounding) (source (fst surrounding))).
  rewrite RUN, RELATED; reflexivity.
Defined.

Theorem absolute_guarded_program surrounding observed :
  toy_program_runs (toy_plug surrounding (toy_select sign_check positive_candidate absolute_source)) observed ->
  exists original, toy_program_runs (toy_plug surrounding absolute_source) original /\ observed = original.
Proof.
  eapply (guardify_program_refinement sign_certificate absolute_certificate toy_context_certificate).
  all: exact I.
Qed.

Example positive_path : checks toy_host sign_check (3, 99) true (3, 42).
Proof. split; reflexivity. Qed.
Example refused_path : checks toy_host sign_check (-3, 99) false (-3, 42).
Proof. split; reflexivity. Qed.
Example private_effect : snd (snd (sign_check (3, 99))) = 42.
Proof. reflexivity. Qed.
Example generated_results :
  (toy_select sign_check positive_candidate absolute_source (3, 99),
   toy_select sign_check positive_candidate absolute_source (-3, 99)) = (3, 3).
Proof. reflexivity. Qed.

Definition never_check : toy_check := fun state => (false, (fst state, 42)).
Definition never_certificate : guard_certificate toy_host (fun _ => True)
  (fun _ => False) public_entry public_entry never_check.
Proof.
  constructor.
  - intros entry _; exists (never_check entry); reflexivity.
  - intros entry _; exists false, (fst entry, 42); split; reflexivity.
  - intros entry accepted checked _ [ANSWER AFTER]; subst; reflexivity.
Defined.

Definition never_rule (arbitrary_candidate : toy_code) :
  conditional_certificate toy_host (fun _ => True) (fun _ => False)
    public_entry public_entry eq absolute_source arbitrary_candidate absolute_source.
Proof.
  constructor.
  - intros entry checked target _ IMPOSSIBLE; contradiction.
  - intros entry checked target _ ENTRY RUN.
    exists (Z.abs (fst entry)); split; [reflexivity|].
    change (target = Z.abs (fst checked)) in RUN.
    change (target = Z.abs (fst entry)).
    unfold public_entry in ENTRY; rewrite RUN, <- ENTRY; reflexivity.
Defined.

Theorem dead_candidate_refinement arbitrary_candidate :
  local_refinement toy_host (fun _ => True) eq
    (select toy_host never_check arbitrary_candidate absolute_source) absolute_source.
Proof. eapply guardify_refinement; [exact never_certificate|apply never_rule]. Qed.

Example unknown_under_negation :
  formula_accepts (fun (_ : unit) (_ : toy_state) => None)
    (Complement (Fact tt)) (0, 0) = false.
Proof. reflexivity. Qed.

Theorem preservation_does_not_imply_refinement :
  (forall observed : Z, observed = 0 -> observed = 0 \/ observed = 1) /\
  ~ (forall target : Z, target = 0 \/ target = 1 ->
      exists original : Z, original = 0 /\ target = original).
Proof.
  split; [tauto|].
  intro BACKWARD; destruct (BACKWARD 1 (or_intror eq_refl)) as [original [ZERO SAME]]; lia.
Qed.

Definition always_check : toy_check := fun entry => (true, entry).
Theorem false_acceptance_certificate_impossible
  (G : guard_certificate toy_host (fun _ => True) (fun _ => False)
    public_entry public_entry always_check) : False.
Proof.
  pose proof (check_sound G (0, 0) true (0, 0) I (conj eq_refl eq_refl)) as BAD.
  exact (proj1 BAD).
Qed.

Print Assumptions absolute_guarded_refinement.
Print Assumptions absolute_guarded_program.
Print Assumptions dead_candidate_refinement.
Print Assumptions preservation_does_not_imply_refinement.
Print Assumptions false_acceptance_certificate_impossible.
