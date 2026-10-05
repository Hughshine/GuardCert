From Stdlib Require Import Bool List ZArith Lia RelationClasses.
From Guard Require Import AbstractGuard AbstractSchedule ScheduleInterleave.
From GuardInterface Require Import GuardInterface GuardedRewrite LocalScheduleEquivalence.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

(** A total mathematical language with two integer cells, two input cell
    identifiers, and an unrelated public value. It has no machine pointers,
    faults, external events, or divergent commands. *)
Record cell_state := CellState {
  left_key : bool; right_key : bool;
  zero_cell : Z; one_cell : Z; outside_region : Z
}.
Inductive cell_instruction := WriteCell (address : bool) (value : Z).
Definition cell_address (i : cell_instruction) := match i with WriteCell a _ => a end.
Definition cell_step (i : cell_instruction) (s : cell_state) : cell_state :=
  match i with WriteCell a v =>
    CellState (left_key s) (right_key s)
      (if a then zero_cell s else v) (if a then v else one_cell s) (outside_region s)
  end.

Lemma distinct_writes_commute first second entry :
  cell_address first <> cell_address second ->
  cell_step second (cell_step first entry) = cell_step first (cell_step second entry).
Proof.
  destruct first as [a x], second as [b y], entry; destruct a, b; cbn;
    intro DIFFERENT; try contradiction; reflexivity.
Qed.

Definition cell_schedule_model : scheduling_model cell_state cell_instruction.
Proof.
  refine (@SchedulingModel cell_state cell_instruction (fun _ => True) eq _
    (fun i s t => t = cell_step i s)
    (fun a b => cell_address a <> cell_address b) _ _ _).
  - intros; exact I.
  - intros i s t s' SAME RUN; subst s'; exists t; auto.
  - intros a b s t u _ DIFFERENT FIRST SECOND.
    subst t u; exists (cell_step b s), (cell_step a (cell_step b s)).
    repeat split; try reflexivity; apply distinct_writes_commute; exact DIFFERENT.
Defined.


Lemma cell_independence_symmetric first second :
  independent cell_schedule_model first second -> independent cell_schedule_model second first.
Proof. cbn; congruence. Qed.

Fixpoint cell_execute instructions entry :=
  match instructions with
  | [] => entry
  | head :: tail => cell_execute tail (cell_step head entry)
  end.

Lemma cell_execute_runs instructions : forall entry,
  schedule_run cell_schedule_model instructions entry (cell_execute instructions entry).
Proof.
  induction instructions; intro entry; cbn; [constructor|].
  econstructor; [reflexivity|apply IHinstructions].
Qed.

Lemma cell_run_result instructions entry observed :
  schedule_run cell_schedule_model instructions entry observed ->
  observed = cell_execute instructions entry.
Proof.
  intro RUN; induction RUN; cbn; [reflexivity|].
  cbn in H; subst t; exact IHRUN.
Qed.

Lemma cell_execute_frame instructions : forall entry,
  outside_region (cell_execute instructions entry) = outside_region entry.
Proof.
  induction instructions as [|[address value] tail IH]; intro entry; cbn; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

Definition cell_code := cell_state -> cell_state.
Definition cell_check := cell_state -> (bool * cell_state).
Definition cell_runs (body : cell_code) entry observed := observed = body entry.
Definition cell_checks (test : cell_check) entry accepted checked :=
  accepted = fst (test entry) /\ checked = snd (test entry).
Definition cell_check_safe (test : cell_check) entry := exists result, test entry = result.
Definition cell_select (test : cell_check) (yes no : cell_code) : cell_code :=
  fun entry => let '(accepted, checked) := test entry in
    (if accepted then yes else no) checked.

Lemma cell_select_exact test yes no entry observed :
  cell_runs (cell_select test yes no) entry observed <->
  exists accepted checked, cell_checks test entry accepted checked /\
    cell_runs (if accepted then yes else no) checked observed.
Proof.
  unfold cell_runs, cell_select, cell_checks.
  destruct (test entry) as [accepted checked]; cbn; split.
  - intro RUN; exists accepted, checked; auto.
  - intros [answer [after [[ANSWER AFTER] RUN]]]; subst answer after; exact RUN.
Qed.

Definition cell_host : guard_host cell_state :=
  {| code := cell_code; check := cell_check; observation := cell_state;
     runs := cell_runs; checks := cell_checks; check_safe := cell_check_safe;
     select := cell_select; select_exact := cell_select_exact |}.

(** Finite premise syntax is reused from the existing formula library. These
    two atoms have language-specific meanings and read-only implementations. *)
Inductive cell_atom := DifferentCells | NoWrapIncrement8.
Definition cell_atom_meaning atom entry : bool :=
  match atom with
  | DifferentCells => negb (Bool.eqb (left_key entry) (right_key entry))
  | NoWrapIncrement8 => (0 <=? zero_cell entry) && (zero_cell entry <? 255)
  end.
Definition cell_atom_evaluate atom entry := Some (cell_atom_meaning atom entry).
Definition cell_formula_check (premise : formula cell_atom) : cell_check :=
  fun entry => (formula_accepts cell_atom_evaluate premise entry, entry).

Definition cell_formula_certificate premise : readonly_condition cell_host (fun _ => True)
  (fun entry => formula_meaning cell_atom_meaning premise entry = true)
  (cell_formula_check premise).
Proof.
  constructor.
  - intros entry _; exists (cell_formula_check premise entry); reflexivity.
  - intros entry _; exists (formula_accepts cell_atom_evaluate premise entry), entry; split; reflexivity.
  - intros entry accepted checked _ [ANSWER AFTER].
    cbn in ANSWER, AFTER; subst accepted checked; split; [reflexivity|].
    intro ACCEPT; eapply formula_accepts_sound with
      (I := fun _ => True) (evaluate := cell_atom_evaluate).
    + intros atom state value _ RESULT; unfold cell_atom_evaluate in RESULT.
      inversion RESULT; reflexivity.
    + exact I.
    + exact ACCEPT.
Defined.

Definition cells_separate entry := left_key entry <> right_key entry.
Lemma different_cells_encoding entry :
  formula_meaning cell_atom_meaning (Fact DifferentCells) entry = true -> cells_separate entry.
Proof.
  destruct entry as [p q z o frame]; destruct p, q; cbn;
    unfold cells_separate; cbn; congruence.
Qed.
Definition cell_alias_certificate : readonly_condition cell_host (fun _ => True)
  cells_separate (cell_formula_check (Fact DifferentCells)) :=
  @readonly_condition_entails cell_state cell_host _ _ cells_separate _
    (cell_formula_certificate (Fact DifferentCells))
    (fun entry _ => different_cells_encoding entry).

(** The source interleaves two writes per iteration; the candidate groups all
    right writes before all left writes. Within each group order is preserved.
    The theorem works for every finite list, including empty and duplicate
    iteration values. This mathematical loop model is not Clight codegen. *)
Definition left_jobs entry values := map (fun v => WriteCell (left_key entry) v) values.
Definition right_jobs entry values := map (fun v => WriteCell (right_key entry) (10 * v)) values.
Definition source_jobs entry values :=
  flat_map (fun v => [WriteCell (left_key entry) v; WriteCell (right_key entry) (10 * v)]) values.
Definition candidate_jobs entry values := right_jobs entry values ++ left_jobs entry values.
Definition loop_source values : cell_code := fun entry => cell_execute (source_jobs entry values) entry.
Definition loop_candidate values : cell_code := fun entry => cell_execute (candidate_jobs entry values) entry.

Lemma separated_loop_certificate entry values : cells_separate entry ->
  schedule_certificate cell_schedule_model (source_jobs entry values) (candidate_jobs entry values).
Proof.
  intro SEPARATE.
  assert (INTERLEAVE : schedule_certificate cell_schedule_model
    (left_jobs entry values ++ right_jobs entry values) (source_jobs entry values)).
  { unfold left_jobs, right_jobs, source_jobs.
    replace (map (fun v => WriteCell (right_key entry) (10 * v)) values)
      with (flat_map (fun v => [WriteCell (right_key entry) (10 * v)]) values).
    - apply interleave_certificate.
      intros x y item _ _ MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|IMPOSSIBLE];
        [subst item|contradiction]; exact SEPARATE.
    - clear SEPARATE; induction values; cbn [flat_map map app];
        [reflexivity|rewrite IHvalues; reflexivity]. }
  eapply certificate_trans.
  - apply (schedule_certificate_reverse cell_independence_symmetric INTERLEAVE).
  - unfold candidate_jobs.
    replace (left_jobs entry values ++ right_jobs entry values)
      with (left_jobs entry values ++ right_jobs entry values ++ []) by now rewrite app_nil_r.
    replace (right_jobs entry values ++ left_jobs entry values)
      with (right_jobs entry values ++ left_jobs entry values ++ []) by now rewrite app_nil_r.
    apply swap_blocks; intros first second FIRST SECOND.
    apply in_map_iff in FIRST as [x [FIRST _]]; apply in_map_iff in SECOND as [y [SECOND _]].
    subst first second; exact SEPARATE.
Qed.

Lemma cell_schedule_observation_transport first second :
  state_equivalent cell_schedule_model first second -> forall observed : cell_state,
  observed = first <-> observed = second.
Proof. cbn; intros SAME; subst second; reflexivity. Qed.

Lemma cell_schedule_observes instructions entry observed :
  schedule_observes cell_schedule_model (fun final seen => seen = final) instructions entry observed <->
  observed = cell_execute instructions entry.
Proof.
  split.
  - intros [final [RUN SAME]]; rewrite SAME; apply cell_run_result; exact RUN.
  - intro SAME; exists (cell_execute instructions entry); split;
      [apply cell_execute_runs|exact SAME].
Qed.

Theorem loop_conditional_equivalent values : conditional_equivalence cell_host
  (fun _ => True) cells_separate (loop_source values) (loop_candidate values).
Proof.
  intros entry observed [_ SEPARATE].
  change (observed = cell_execute (candidate_jobs entry values) entry <->
    observed = cell_execute (source_jobs entry values) entry).
  rewrite <- !cell_schedule_observes.
  eapply certified_schedule_equivalent.
  - exact cell_independence_symmetric.
  - exact cell_schedule_observation_transport.
  - apply separated_loop_certificate; exact SEPARATE.
  - exact I.
Qed.

Theorem loop_guarded_equivalent values : local_equivalence cell_host (fun _ => True)
  (guarded_rewrite cell_host (loop_source values) (loop_candidate values)
    (cell_formula_check (Fact DifferentCells))) (loop_source values).
Proof. eapply guarded_rewrite_equivalent; [exact cell_alias_certificate|apply loop_conditional_equivalent]. Qed.

Definition increment_nowrap entry := 0 <= zero_cell entry < 255.
Lemma increment_nowrap_encoding entry :
  formula_meaning cell_atom_meaning (Fact NoWrapIncrement8) entry = true -> increment_nowrap entry.
Proof.
  cbn; intro CHECK; apply andb_true_iff in CHECK as [LOW HIGH].
  unfold increment_nowrap; apply Z.leb_le in LOW; apply Z.ltb_lt in HIGH; lia.
Qed.
Definition increment_condition : readonly_condition cell_host (fun _ => True)
  increment_nowrap (cell_formula_check (Fact NoWrapIncrement8)) :=
  @readonly_condition_entails cell_state cell_host _ _ increment_nowrap _
    (cell_formula_certificate (Fact NoWrapIncrement8))
    (fun entry _ => increment_nowrap_encoding entry).

Definition overflow_branch_source : cell_code := fun entry =>
  cell_step (WriteCell true
    (if ((zero_cell entry + 1) mod 256 <? zero_cell entry) then 1 else 0)) entry.
Definition overflow_branch_candidate : cell_code := fun entry => cell_step (WriteCell true 0) entry.

Theorem overflow_branch_conditional_equivalent : conditional_equivalence cell_host
  (fun _ => True) increment_nowrap overflow_branch_source overflow_branch_candidate.
Proof.
  intros entry observed [_ RANGE]; unfold increment_nowrap in RANGE.
  unfold runs, cell_host, cell_runs, overflow_branch_source, overflow_branch_candidate; cbn.
  rewrite Z.mod_small by lia.
  assert (FALSE : (zero_cell entry + 1 <? zero_cell entry) = false) by (apply Z.ltb_ge; lia).
  rewrite FALSE; reflexivity.
Qed.

Theorem overflow_branch_guarded_equivalent : local_equivalence cell_host (fun _ => True)
  (guarded_rewrite cell_host overflow_branch_source overflow_branch_candidate
    (cell_formula_check (Fact NoWrapIncrement8))) overflow_branch_source.
Proof.
  eapply guarded_rewrite_equivalent;
    [exact increment_condition|exact overflow_branch_conditional_equivalent].
Qed.

(** The surrounding program consumes the entire final state. Its continuation
    may read either cell, either input identifier, or the unrelated value. *)
Definition cell_context := (cell_state * (cell_state -> Z))%type.
Definition cell_program := (cell_state * (cell_code * (cell_state -> Z)))%type.
Definition cell_plug (surrounding : cell_context) (body : cell_code) : cell_program :=
  (fst surrounding, (body, snd surrounding)).
Definition cell_program_runs (p : cell_program) observed :=
  observed = (snd (snd p)) ((fst (snd p)) (fst p)).

Definition cell_rewrite_context : rewrite_context cell_host.
Proof.
  refine (@RewriteContext cell_state cell_host cell_context cell_program Z
    cell_plug cell_program_runs
    (fun surrounding _ domain => domain (fst surrounding))
    (fun _ _ _ _ => True) _).
  intros surrounding source target domain DOMAIN _ LOCAL observed.
  pose proof (proj1 (LOCAL (fst surrounding) (target (fst surrounding)) DOMAIN) eq_refl) as SAME.
  change (target (fst surrounding) = source (fst surrounding)) in SAME.
  unfold cell_program_runs, cell_plug; cbn; rewrite SAME; reflexivity.
Defined.

Theorem loop_program_equivalent values surrounding observed :
  cell_program_runs (cell_plug surrounding
    (guarded_rewrite cell_host (loop_source values) (loop_candidate values)
      (cell_formula_check (Fact DifferentCells)))) observed <->
  cell_program_runs (cell_plug surrounding (loop_source values)) observed.
Proof.
  eapply (guarded_rewrite_program_equivalent cell_alias_certificate
    (loop_conditional_equivalent values) cell_rewrite_context). all: exact I.
Qed.

Theorem overflow_branch_program_equivalent surrounding observed :
  cell_program_runs (cell_plug surrounding
    (guarded_rewrite cell_host overflow_branch_source overflow_branch_candidate
      (cell_formula_check (Fact NoWrapIncrement8)))) observed <->
  cell_program_runs (cell_plug surrounding overflow_branch_source) observed.
Proof.
  eapply (guarded_rewrite_program_equivalent increment_condition
    overflow_branch_conditional_equivalent cell_rewrite_context). all: exact I.
Qed.

Definition separate_entry := CellState false true 0 0 77.
Definition aliased_entry := CellState false false 0 0 77.
Definition guarded_loop := guarded_rewrite cell_host (loop_source [1; 2]) (loop_candidate [1; 2])
  (cell_formula_check (Fact DifferentCells)).

Example loop_accepts_and_preserves_frame :
  fst (cell_formula_check (Fact DifferentCells) separate_entry) = true /\
  guarded_loop separate_entry = CellState false true 2 20 77.
Proof. split; reflexivity. Qed.
Example alias_requires_fallback :
  loop_candidate [1; 2] aliased_entry = CellState false false 2 0 77 /\
  loop_source [1; 2] aliased_entry = CellState false false 20 0 77 /\
  fst (cell_formula_check (Fact DifferentCells) aliased_entry) = false /\
  guarded_loop aliased_entry = CellState false false 20 0 77.
Proof. repeat split; reflexivity. Qed.
Example overflow_requires_fallback :
  fst (cell_formula_check (Fact NoWrapIncrement8) (CellState false true 254 9 77)) = true /\
  guarded_rewrite cell_host overflow_branch_source overflow_branch_candidate
    (cell_formula_check (Fact NoWrapIncrement8)) (CellState false true 255 9 77) =
    CellState false true 255 1 77.
Proof. split; reflexivity. Qed.
Example mixed_condition :
  fst (cell_formula_check (Conjunction (Fact DifferentCells) (Fact NoWrapIncrement8))
    (CellState false true 254 9 77)) = true.
Proof. reflexivity. Qed.

Print Assumptions cell_formula_certificate.
Print Assumptions cell_execute_frame.
Print Assumptions loop_conditional_equivalent.
Print Assumptions loop_guarded_equivalent.
Print Assumptions loop_program_equivalent.
Print Assumptions overflow_branch_guarded_equivalent.
Print Assumptions overflow_branch_program_equivalent.
