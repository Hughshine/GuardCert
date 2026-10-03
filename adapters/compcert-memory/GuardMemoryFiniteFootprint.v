From Stdlib Require Import List Bool ZArith Lia.
From compcert.common Require Import AST Memory.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import ImpureAlarmConfig Linalg.
From Vpl Require Import Impure.
From Guard Require Import CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryLoopTrace
  GuardMemoryExtractorProgress GuardMemoryFootprintRestriction.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition memory_cell_identity_dec : forall first second : MemCell, {first=second}+{first<>second}.
Proof. decide equality; [apply (@List.list_eq_dec Z Z.eq_dec)|apply Pos.eq_dec]. Defined.
Definition memory_footprint_allowed (cells : list MemCell) cell :=
  existsb (fun other => if memory_cell_identity_dec cell other then true else false) cells.
Lemma memory_footprint_allowed_exact cells cell : memory_footprint_allowed cells cell = true <-> In cell cells.
Proof.
  unfold memory_footprint_allowed; rewrite existsb_exists; split.
  - intros [other [MEMBER SAME]]; destruct memory_cell_identity_dec; [subst; exact MEMBER|discriminate].
  - intro MEMBER; exists cell; split; [exact MEMBER|destruct memory_cell_identity_dec; congruence].
Qed.
Definition memory_cell_pair_separation_check locations first second :=
  if memory_cell_identity_dec first second then true else
  match locations first,locations second with
  | Some first_location,Some second_location => location_disjointb first_location second_location
  | _,_ => false end.
Definition memory_finite_separation_check (locations : cell_locations) cells :=
  forallb (fun first => forallb (memory_cell_pair_separation_check locations first) cells) cells.
Theorem memory_finite_separation_check_sound locations cells :
  memory_finite_separation_check locations cells = true ->
  memory_locations_separated_on (memory_footprint_allowed cells) locations.
Proof.
  intros CHECK first second left right FIRST_ALLOWED SECOND_ALLOWED FIRST SECOND DIFFERENT.
  apply memory_footprint_allowed_exact in FIRST_ALLOWED,SECOND_ALLOWED.
  unfold memory_finite_separation_check in CHECK.
  apply forallb_forall with (x := first) in CHECK; [|exact FIRST_ALLOWED].
  apply forallb_forall with (x := second) in CHECK; [|exact SECOND_ALLOWED].
  unfold memory_cell_pair_separation_check in CHECK.
  destruct (memory_cell_identity_dec first second) as [SAME|DISTINCT].
  - subst second; unfold cell_neq in DIFFERENT; destruct DIFFERENT as [BAD|BAD];
      [congruence|exfalso; apply BAD; apply veq_refl].
  - rewrite FIRST,SECOND in CHECK; apply location_disjointb_correct; exact CHECK.
Qed.
Definition memory_events_footprint events := flat_map (fun event =>
  exact_cell (instruction_write (event_instruction event)) (event_arguments event) ::
  map (fun access => exact_cell access (event_arguments event))
    (instruction_reads (event_instruction event))) events.
Theorem memory_loop_own_footprint_covered source parameters :
  memory_loop_cells_covered (memory_footprint_allowed
    (memory_events_footprint (memory_loop_trace source parameters))) source parameters.
Proof.
  unfold memory_loop_cells_covered; apply Forall_forall; intros event MEMBER.
  unfold memory_instruction_cells_covered; split.
  - apply memory_footprint_allowed_exact; unfold memory_events_footprint; apply in_flat_map.
    exists event; split; [exact MEMBER|cbn; auto].
  - apply Forall_forall; intros cell ACCESS; apply memory_footprint_allowed_exact.
    unfold memory_events_footprint; apply in_flat_map; exists event; split; [exact MEMBER|cbn; auto].
Qed.
Lemma memory_loop_footprint_members_covered cells loop parameters :
  (forall cell, In cell (memory_events_footprint (memory_loop_trace loop parameters)) -> In cell cells) ->
  memory_loop_cells_covered (memory_footprint_allowed cells) loop parameters.
Proof.
  intro SUBSET; unfold memory_loop_cells_covered; apply Forall_forall; intros event EVENT.
  unfold memory_instruction_cells_covered; split.
  - apply memory_footprint_allowed_exact,SUBSET; unfold memory_events_footprint; apply in_flat_map.
    exists event; split; [exact EVENT|cbn; auto].
  - apply Forall_forall; intros cell ACCESS; apply memory_footprint_allowed_exact,SUBSET.
    unfold memory_events_footprint; apply in_flat_map; exists event; split; [exact EVENT|cbn; auto].
Qed.
(** This wrapper instantiates the existing polyhedral validator with a finite
    physical view. It does not assume a globally disjoint pointer allocation. *)
Theorem memory_finite_footprint_separated_candidate source candidate context vars parameters locations before after :
  length parameters = length context ->
  mayReturn (checked_memory_loop_equivalence (source,context,vars) (candidate,context,vars)) true ->
  memory_locations_separated_on (memory_footprint_allowed
    (memory_events_footprint (memory_loop_trace source parameters))) locations ->
  L.loop_semantics source parameters (RuntimeState locations before) (RuntimeState locations after) ->
  L.loop_semantics candidate parameters (RuntimeState locations before) (RuntimeState locations after).
Proof.
  intros LENGTH CHECK SEPARATION SOURCE.
  set (allowed := memory_footprint_allowed (memory_events_footprint (memory_loop_trace source parameters))).
  assert (NONALIAS : GuardMemoryInstr.NonAlias (RuntimeState (memory_restrict_locations allowed locations) before)).
  { apply memory_restricted_locations_nonalias; exact SEPARATION. }
  assert (RESTRICTED : L.loop_semantics source parameters
    (RuntimeState (memory_restrict_locations allowed locations) before)
    (RuntimeState (memory_restrict_locations allowed locations) after)).
  { change (L.loop_semantics source parameters
      (memory_restrict_state allowed (RuntimeState locations before))
      (memory_restrict_state allowed (RuntimeState locations after))).
    eapply memory_restrict_loop_execution; [apply memory_loop_own_footprint_covered|exact SOURCE]. }
  apply memory_unrestrict_loop_execution with (allowed := allowed).
  pose proof (@validated_memory_affine_loops_at source candidate context vars (rev parameters)
    (RuntimeState (memory_restrict_locations allowed locations) before)
    (RuntimeState (memory_restrict_locations allowed locations) after)
    ltac:(rewrite rev_length; exact LENGTH) NONALIAS CHECK) as VALIDATED.
  rewrite rev_involutive in VALIDATED; apply (proj1 VALIDATED); exact RESTRICTED.
Qed.
Theorem memory_finite_footprint_validated_candidate source candidate context vars parameters locations before after :
  length parameters = length context ->
  mayReturn (checked_memory_loop_equivalence (source,context,vars) (candidate,context,vars)) true ->
  memory_finite_separation_check locations
    (memory_events_footprint (memory_loop_trace source parameters)) = true ->
  L.loop_semantics source parameters (RuntimeState locations before) (RuntimeState locations after) ->
  L.loop_semantics candidate parameters (RuntimeState locations before) (RuntimeState locations after).
Proof.
  intros LENGTH CHECK SEPARATION SOURCE; eapply memory_finite_footprint_separated_candidate;
    [exact LENGTH|exact CHECK|eapply memory_finite_separation_check_sound; exact SEPARATION|exact SOURCE].
Qed.
Print Assumptions memory_finite_footprint_separated_candidate.
Print Assumptions memory_finite_separation_check_sound.
Print Assumptions memory_loop_own_footprint_covered.
Print Assumptions memory_finite_footprint_validated_candidate.
