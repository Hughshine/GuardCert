From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.src Require Import PointWitness TilingWitness.
From polcert.polygen Require Import Result.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryPolyhedral GuardMemoryLoops
  GuardMemoryExtractorTrace GuardMemoryExtractorProgress GuardMemoryDomainNormalization GuardMemoryDomainAlignment GuardMemoryTilingProgress GuardMemoryTilingMultipleProgress.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Module PL := GuardMemoryIRs.PolyLang.

Definition memory_pinstr_eqb (first second : PL.PolyInstr) :=
  Nat.eqb (PL.pi_depth first) (PL.pi_depth second) &&
  GuardMemoryInstr.eqb (PL.pi_instr first) (PL.pi_instr second) &&
  (if list_eq_dec affine_term_eq_dec (PL.pi_poly first) (PL.pi_poly second) then true else false) &&
  (if list_eq_dec affine_term_eq_dec (PL.pi_schedule first) (PL.pi_schedule second) then true else false) &&
  point_space_witness_eqb (PL.pi_point_witness first) (PL.pi_point_witness second) &&
  (if list_eq_dec affine_term_eq_dec (PL.pi_transformation first) (PL.pi_transformation second) then true else false) &&
  (if list_eq_dec affine_term_eq_dec (PL.pi_access_transformation first) (PL.pi_access_transformation second) then true else false) &&
  (if list_eq_dec affine_access_eq_dec (PL.pi_waccess first) (PL.pi_waccess second) then true else false) &&
  (if list_eq_dec affine_access_eq_dec (PL.pi_raccess first) (PL.pi_raccess second) then true else false).
Lemma memory_pinstr_eqb_sound first second : memory_pinstr_eqb first second = true -> first = second.
Proof.
  unfold memory_pinstr_eqb; repeat rewrite andb_true_iff.
  repeat match goal with |- context[if ?dec then _ else _] => destruct dec; [|intuition discriminate] end.
  intros [[[[[[[[DEPTH INSTR] DOMAIN] SCHEDULE] WITNESS] TRANSFORM] ACCESS] WRITES] READS].
  apply Nat.eqb_eq in DEPTH; apply GuardMemoryInstr.eqb_eq in INSTR;
    apply point_space_witness_eqb_eq in WITNESS.
  destruct first,second; cbn in *; subst; reflexivity.
Qed.
Fixpoint memory_pinstr_list_eqb first second := match first,second with
  | [],[] => true
  | a::rest,b::tail => memory_pinstr_eqb a b && memory_pinstr_list_eqb rest tail
  | _,_ => false end.
Lemma memory_pinstr_list_eqb_sound first second : memory_pinstr_list_eqb first second = true -> first = second.
Proof.
  revert second; induction first; destruct second; cbn; try discriminate; [reflexivity|].
  rewrite andb_true_iff; intros [HEAD TAIL]; f_equal;
    [apply memory_pinstr_eqb_sound|apply IHfirst]; assumption.
Qed.
Definition memory_tiling_current_shape instructions :=
  forallb (fun pi => Nat.eqb (witness_current_point_dim (PL.pi_point_witness pi)) (PL.pi_depth pi)) instructions.
Lemma memory_tiling_current_shape_sound instructions : memory_tiling_current_shape instructions = true ->
  Forall (fun pi => witness_current_point_dim (PL.pi_point_witness pi) = PL.pi_depth pi) instructions.
Proof.
  unfold memory_tiling_current_shape; rewrite forallb_forall; intro ALL; apply Forall_forall.
  intros; apply Nat.eqb_eq,ALL; assumption.
Qed.
Definition memory_attach_tiling_instruction dimension (before candidate : PL.PolyInstr) witness : PL.PolyInstr :=
  let compiled := T.compiled_pinstr_tiling_witness witness in
  {| PL.pi_depth := PL.pi_depth candidate; PL.pi_instr := PL.pi_instr candidate;
     PL.pi_poly := T.ptw_link_domain compiled ++ T.lifted_base_domain_after_env dimension compiled (PL.pi_poly before);
     PL.pi_schedule := PL.pi_schedule candidate;
     PL.pi_point_witness := PSWTiling (T.ptw_statement_witness compiled);
     PL.pi_transformation := PL.pi_transformation before;
     PL.pi_access_transformation := PL.pi_access_transformation before;
     PL.pi_waccess := PL.pi_waccess candidate; PL.pi_raccess := PL.pi_raccess candidate |}.
Fixpoint memory_attach_tiling_instructions dimension before candidate witnesses :=
  match before,candidate,witnesses with
  | [],[],[] => Some []
  | old::olds,next::nexts,witness::rest =>
      match memory_attach_tiling_instructions dimension olds nexts rest with
      | Some tail => Some (memory_attach_tiling_instruction dimension old next witness::tail)
      | None => None end
  | _,_,_ => None end.

Lemma memory_tiling_current_view_execution parameters instructions context vars before after :
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

Definition checked_memory_extracted_tiling_loops source candidate witnesses :=
  match MemoryExtractor.extractor source,MemoryExtractor.extractor candidate with
  | Okk (before,context,vars),Okk (after,_,_) =>
    let normalized_before := memory_normalized_instructions before in
    let normalized_after := memory_normalized_instructions after in
    match memory_attach_tiling_instructions (length context) normalized_before normalized_after witnesses with
    | Some tiled =>
      if memory_tiling_current_shape tiled then
        BIND aligned <- memory_align_domains (map (PL.current_view_pi (length context)) tiled) normalized_after -;
        match aligned with
        | Some aligned => if memory_pinstr_list_eqb (map (PL.current_view_pi (length context)) tiled) aligned
          then validate_memory_tiling_equivalence (normalized_before,context,vars) (tiled,context,vars) witnesses
          else pure false
        | None => pure false end
      else pure false
    | None => pure false end
  | _,_ => pure false end.
Theorem validated_memory_extracted_tiling_loops_at source candidate context vars witnesses parameters before after :
  length parameters = length context -> GuardMemoryInstr.NonAlias before ->
  mayReturn (checked_memory_extracted_tiling_loops (source,context,vars) (candidate,context,vars) witnesses) true ->
  L.loop_semantics source (rev parameters) before after ->
  L.loop_semantics candidate (rev parameters) before after.
Proof.
  intros LENGTH NONALIAS CHECK SOURCE_RUN; unfold checked_memory_extracted_tiling_loops in CHECK.
  destruct (MemoryExtractor.extractor (source,context,vars)) as [source_program|error] eqn:SOURCE;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (MemoryExtractor.extractor (candidate,context,vars)) as [candidate_program|error] eqn:CANDIDATE;
    [|destruct source_program as [[pis ctxt] variables]; apply mayReturn_pure in CHECK; discriminate].
  destruct (@MemoryExtractor.extractor_success_inv source context vars _ SOURCE) as [source_instructions [_ [_ SOURCE_PROGRAM]]].
  destruct (@MemoryExtractor.extractor_success_inv candidate context vars _ CANDIDATE) as [candidate_instructions [_ [_ CANDIDATE_PROGRAM]]].
  subst source_program candidate_program; cbn -[memory_attach_tiling_instructions memory_normalized_instructions memory_pinstr_list_eqb memory_tiling_current_shape] in CHECK.
  change (@length PL.ident context) with (@length L.ident context) in CHECK.
  destruct (memory_attach_tiling_instructions (length context) (memory_normalized_instructions source_instructions)
    (memory_normalized_instructions candidate_instructions) witnesses) as [tiled|] eqn:ATTACH;
    [|apply mayReturn_pure in CHECK; discriminate].
  destruct (memory_tiling_current_shape tiled) eqn:SHAPE; [|apply mayReturn_pure in CHECK; discriminate].
  apply memory_tiling_current_shape_sound in SHAPE.
  bind_imp_destruct CHECK aligned_result ALIGN.
  destruct aligned_result as [aligned|]; [|apply mayReturn_pure in CHECK; discriminate].
  destruct (memory_pinstr_list_eqb (map (PL.current_view_pi (length context)) tiled) aligned) eqn:SAME;
    [|apply mayReturn_pure in CHECK; discriminate].
  apply memory_pinstr_list_eqb_sound in SAME; subst aligned.
  rewrite (@memory_extractor_execution_at candidate context vars candidate_instructions parameters before after CANDIDATE LENGTH).
  rewrite (@memory_domain_normalization_execution parameters candidate_instructions context vars before after).
  rewrite (@memory_aligned_domains_execution parameters (map (PL.current_view_pi (length context)) tiled)
    (memory_normalized_instructions candidate_instructions) (map (PL.current_view_pi (length context)) tiled)
    context vars before after ALIGN).
  apply (proj2 (@memory_tiling_current_view_execution parameters tiled context vars before after LENGTH SHAPE)).
  eapply validated_memory_multiple_tiling_progress_at; [exact LENGTH|exact NONALIAS|exact CHECK|].
  apply (proj1 (@memory_domain_normalization_execution parameters source_instructions context vars before after)).
  apply (proj1 (@memory_extractor_execution_at source context vars source_instructions parameters before after SOURCE LENGTH)).
  exact SOURCE_RUN.
Qed.
Print Assumptions validated_memory_extracted_tiling_loops_at.
