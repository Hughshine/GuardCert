From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness PolyBase.
From polcert.polygen Require Import Result.
From Vpl Require Import Impure.
From Guard Require Import PolCertTilingProgress.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleCandidateProgress.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Module DoubleTiling := PolCertTilingProgressFor DoubleAssignmentIRs.
Module T := DoubleTiling.T.
Module PL := DoubleAssignmentIRs.PolyLang.

Lemma double_tiling_state_eq_exact first second : DoubleAssignmentIRs.State.eq first second -> first = second.
Proof. unfold DoubleAssignmentIRs.State.eq,DoubleAssignmentInstr.State.eq; auto. Qed.
Lemma double_tiling_extractor_execution_at source context vars instructions parameters before after :
  DoubleAssignmentExtractor.extractor (source,context,vars)=Okk (instructions,context,vars) ->
  length parameters=length context ->
  (DoubleAssignmentIRs.Loop.loop_semantics source (rev parameters) before after <->
   PL.poly_instance_list_semantics parameters (instructions,context,vars) before after).
Proof.
  intros EXTRACT LENGTH.
  pose proof (@double_extractor_execution_at source context vars instructions (rev parameters) before after
    EXTRACT ltac:(rewrite length_rev; symmetry; exact LENGTH)) as RUN.
  rewrite rev_involutive in RUN; exact RUN.
Qed.

Definition double_tiling_pinstr_eqb (first second : PL.PolyInstr) :=
  Nat.eqb (PL.pi_depth first) (PL.pi_depth second) &&
  DoubleAssignmentInstr.eqb (PL.pi_instr first) (PL.pi_instr second) &&
  (if @List.list_eq_dec (list Z * Z)%type DoubleCandidate.representation_affine_term_eq_dec (PL.pi_poly first) (PL.pi_poly second) then true else false) &&
  (if @List.list_eq_dec (list Z * Z)%type DoubleCandidate.representation_affine_term_eq_dec (PL.pi_schedule first) (PL.pi_schedule second) then true else false) &&
  point_space_witness_eqb (PL.pi_point_witness first) (PL.pi_point_witness second) &&
  (if @List.list_eq_dec (list Z * Z)%type DoubleCandidate.representation_affine_term_eq_dec (PL.pi_transformation first) (PL.pi_transformation second) then true else false) &&
  (if @List.list_eq_dec (list Z * Z)%type DoubleCandidate.representation_affine_term_eq_dec (PL.pi_access_transformation first) (PL.pi_access_transformation second) then true else false) &&
  (if @List.list_eq_dec AccessFunction affine_access_eq_dec (PL.pi_waccess first) (PL.pi_waccess second) then true else false) &&
  (if @List.list_eq_dec AccessFunction affine_access_eq_dec (PL.pi_raccess first) (PL.pi_raccess second) then true else false).
Lemma double_tiling_pinstr_eqb_sound first second : double_tiling_pinstr_eqb first second = true -> first = second.
Proof.
  unfold double_tiling_pinstr_eqb; repeat rewrite andb_true_iff.
  repeat match goal with |- context[if ?dec then _ else _] => destruct dec; [|intuition discriminate] end.
  intros [[[[[[[[DEPTH INSTR] DOMAIN] SCHEDULE] WITNESS] TRANSFORM] ACCESS] WRITES] READS].
  apply Nat.eqb_eq in DEPTH; apply DoubleAssignmentInstr.eqb_eq in INSTR;
    apply point_space_witness_eqb_eq in WITNESS.
  destruct first,second; cbn in *; subst; reflexivity.
Qed.
Fixpoint double_tiling_pinstr_list_eqb first second := match first,second with
  | [],[] => true
  | a::rest,b::tail => double_tiling_pinstr_eqb a b && double_tiling_pinstr_list_eqb rest tail
  | _,_ => false end.
Lemma double_tiling_pinstr_list_eqb_sound first second : double_tiling_pinstr_list_eqb first second = true -> first = second.
Proof.
  revert second; induction first; destruct second; cbn; try discriminate; [reflexivity|].
  rewrite andb_true_iff; intros [HEAD TAIL]; f_equal;
    [apply double_tiling_pinstr_eqb_sound|apply IHfirst]; assumption.
Qed.
Definition double_tiling_current_shape instructions :=
  forallb (fun pi => Nat.eqb (witness_current_point_dim (PL.pi_point_witness pi)) (PL.pi_depth pi)) instructions.
Lemma double_tiling_current_shape_sound instructions : double_tiling_current_shape instructions = true ->
  Forall (fun pi => witness_current_point_dim (PL.pi_point_witness pi) = PL.pi_depth pi) instructions.
Proof.
  unfold double_tiling_current_shape; rewrite forallb_forall; intro ALL; apply Forall_forall.
  intros; apply Nat.eqb_eq,ALL; assumption.
Qed.
Definition double_attach_tiling_instruction dimension (before candidate : PL.PolyInstr) witness : PL.PolyInstr :=
  let compiled := T.compiled_pinstr_tiling_witness witness in
  {| PL.pi_depth := PL.pi_depth candidate; PL.pi_instr := PL.pi_instr candidate;
     PL.pi_poly := T.ptw_link_domain compiled ++ T.lifted_base_domain_after_env dimension compiled (PL.pi_poly before);
     PL.pi_schedule := PL.pi_schedule candidate;
     PL.pi_point_witness := PSWTiling (T.ptw_statement_witness compiled);
     PL.pi_transformation := PL.pi_transformation before;
     PL.pi_access_transformation := PL.pi_access_transformation before;
     PL.pi_waccess := PL.pi_waccess candidate; PL.pi_raccess := PL.pi_raccess candidate |}.
Fixpoint double_attach_tiling_instructions dimension before candidate witnesses :=
  match before,candidate,witnesses with
  | [],[],[] => Some []
  | old::olds,next::nexts,witness::rest =>
      match double_attach_tiling_instructions dimension olds nexts rest with
      | Some tail => Some (double_attach_tiling_instruction dimension old next witness::tail)
      | None => None end
  | _,_,_ => None end.

Lemma double_tiling_current_view_execution parameters instructions context vars before after :
  length parameters = length context ->
  Forall (fun pi => witness_current_point_dim (PL.pi_point_witness pi) = PL.pi_depth pi) instructions ->
  (PL.poly_instance_list_semantics parameters
    (map (PL.current_view_pi (length context)) instructions,context,vars) before after <->
   PL.poly_instance_list_semantics parameters (instructions,context,vars) before after).
Proof.
  intros LENGTH SHAPE; split; intro RUN;
    inversion RUN as [env program pis ctxt variables first final points ordered PROGRAM FLAT PERM SORTED EXEC];
    injection PROGRAM as PIS CONTEXT VARS; subst pis ctxt variables;
    eapply PL.PolyPointListSema with (ipl := points) (sorted_ipl := ordered);
    try reflexivity; try exact PERM; try exact SORTED; try exact EXEC.
  - rewrite <- LENGTH in FLAT; apply (proj1 (@PL.flatten_instrs_current_view_iff parameters (length parameters)
      instructions points eq_refl SHAPE)); exact FLAT.
  - rewrite <- LENGTH; apply (proj2 (@PL.flatten_instrs_current_view_iff parameters (length parameters)
      instructions points eq_refl SHAPE)); exact FLAT.
Qed.

Definition checked_double_extracted_tiling_loops source candidate witnesses :=
  match DoubleAssignmentExtractor.extractor source,DoubleAssignmentExtractor.extractor candidate with
  | Okk (before,context,vars),Okk (after,_,_) =>
    let normalized_before := DoubleCandidate.memory_normalized_instructions before in
    let normalized_after := DoubleCandidate.memory_normalized_instructions after in
    match double_attach_tiling_instructions (length context) normalized_before normalized_after witnesses with
    | Some tiled =>
      if double_tiling_current_shape tiled then
        BIND aligned <- DoubleCandidate.memory_align_domains (map (PL.current_view_pi (length context)) tiled) normalized_after -;
        match aligned with
        | Some aligned => if double_tiling_pinstr_list_eqb (map (PL.current_view_pi (length context)) tiled) aligned
          then DoubleTiling.validate_memory_tiling_equivalence (normalized_before,context,vars) (tiled,context,vars) witnesses
          else pure false
        | None => pure false end
      else pure false
    | None => pure false end
  | _,_ => pure false end.
Theorem validated_double_extracted_tiling_loops_at source candidate context vars witnesses parameters before after :
  length parameters = length context -> DoubleAssignmentInstr.NonAlias before ->
  mayReturn (checked_double_extracted_tiling_loops (source,context,vars) (candidate,context,vars) witnesses) true ->
  DoubleAssignmentIRs.Loop.loop_semantics source (rev parameters) before after ->
  DoubleAssignmentIRs.Loop.loop_semantics candidate (rev parameters) before after.
Proof.
  intros LENGTH NONALIAS CHECK SOURCE_RUN; unfold checked_double_extracted_tiling_loops in CHECK.
  destruct (DoubleAssignmentExtractor.extractor (source,context,vars)) as [source_program|error] eqn:SOURCE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (DoubleAssignmentExtractor.extractor (candidate,context,vars)) as [candidate_program|error] eqn:CANDIDATE;
    [|destruct source_program as [[pis ctxt] variables]; apply mayReturn_pure in CHECK; discriminate].
  destruct (@DoubleAssignmentExtractor.extractor_success_inv source context vars _ SOURCE) as [source_instructions [_ [_ SOURCE_PROGRAM]]].
  destruct (@DoubleAssignmentExtractor.extractor_success_inv candidate context vars _ CANDIDATE) as [candidate_instructions [_ [_ CANDIDATE_PROGRAM]]].
  subst source_program candidate_program; cbn -[double_attach_tiling_instructions DoubleCandidate.memory_normalized_instructions double_tiling_pinstr_list_eqb double_tiling_current_shape] in CHECK.
  change (@length PL.ident context) with (@length DoubleAssignmentIRs.Loop.ident context) in CHECK.
  destruct (double_attach_tiling_instructions (length context) (DoubleCandidate.memory_normalized_instructions source_instructions)
    (DoubleCandidate.memory_normalized_instructions candidate_instructions) witnesses) as [tiled|] eqn:ATTACH;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (double_tiling_current_shape tiled) eqn:SHAPE; [|apply mayReturn_pure in CHECK; discriminate].
  apply double_tiling_current_shape_sound in SHAPE.
  bind_imp_destruct CHECK aligned_result ALIGN.
  destruct aligned_result as [aligned|]; [|apply mayReturn_pure in CHECK; discriminate].
  destruct (double_tiling_pinstr_list_eqb (map (PL.current_view_pi (length context)) tiled) aligned) eqn:SAME;
    [|apply mayReturn_pure in CHECK; discriminate].
  apply double_tiling_pinstr_list_eqb_sound in SAME; subst aligned.
  rewrite (@double_tiling_extractor_execution_at candidate context vars candidate_instructions parameters before after CANDIDATE LENGTH).
  rewrite (@DoubleCandidate.memory_domain_normalization_execution parameters candidate_instructions context vars before after).
  rewrite (@DoubleCandidate.memory_aligned_domains_execution parameters (map (PL.current_view_pi (length context)) tiled)
    (DoubleCandidate.memory_normalized_instructions candidate_instructions) (map (PL.current_view_pi (length context)) tiled)
    context vars before after ltac:(symmetry; exact LENGTH) ALIGN).
  apply (proj2 (@double_tiling_current_view_execution parameters tiled context vars before after LENGTH SHAPE)).
  eapply (DoubleTiling.validated_memory_multiple_tiling_progress_at double_tiling_state_eq_exact); [exact LENGTH|exact NONALIAS|exact CHECK|].
  apply (proj1 (@DoubleCandidate.memory_domain_normalization_execution parameters source_instructions context vars before after)).
  apply (proj1 (@double_tiling_extractor_execution_at source context vars source_instructions parameters before after SOURCE LENGTH)).
  exact SOURCE_RUN.
Qed.
Print Assumptions validated_double_extracted_tiling_loops_at.
