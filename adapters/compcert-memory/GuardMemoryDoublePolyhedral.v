From Stdlib Require Import List Bool String.
From polcert.src Require Import PolyLang OpenScop AffineValidator TilingValidator ISSWitness TilingWitness
  PrepareCodegen ExtractorCorrect.
From polcert.polygen Require Import PolIRs Loop PolyLoop Result.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryDoubleAssignment.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** This is the typed model/checker/codegen instance. External phase producers
    return data to the functions below; there is no scheduler installed here. *)
Module DoubleAssignmentIRs <: POLIRS.
Module Instr := DoubleAssignmentInstr.
Module State := Instr.State.
Module Ty := Instr.Ty.
Module PolyLang := PolyLang Instr.
Module PolyLoop := PolyLoop Instr.
Module Loop := Loop Instr.
Definition scheduler (_ : PolyLang.t) : result PolyLang.t := Err "supply a checked double model candidate"%string.
Definition affine_scheduler := scheduler.
Definition export_for_phase_scheduler (_ : PolyLang.t) : option OpenScop := None.
Definition export_for_pluto_phase_pipeline := export_for_phase_scheduler.
Definition to_phase_openscop := export_for_phase_scheduler.
Definition phase_scop_scheduler (_ : OpenScop) : result (OpenScop*OpenScop) := Err "double phase producer not installed"%string.
Definition run_pluto_phase_pipeline := phase_scop_scheduler.
Definition identity_tiling_phase_scop_scheduler := phase_scop_scheduler.
Definition run_pluto_identity_tiling_pipeline := identity_tiling_phase_scop_scheduler.
Definition phase_scop_scheduler_with_iss := phase_scop_scheduler.
Definition run_pluto_phase_pipeline_with_iss := phase_scop_scheduler_with_iss.
Definition post_tiling_affine_phase_scop_scheduler (_ : OpenScop) : result (OpenScop*(OpenScop*OpenScop)) :=
  Err "double phase producer not installed"%string.
Definition run_pluto_post_tiling_affine_phase_pipeline := post_tiling_affine_phase_scop_scheduler.
Definition post_tiling_affine_phase_scop_scheduler_with_iss := post_tiling_affine_phase_scop_scheduler.
Definition run_pluto_post_tiling_affine_phase_pipeline_with_iss := post_tiling_affine_phase_scop_scheduler_with_iss.
Definition infer_iss_from_source_scop (_ : PolyLang.t) (_ : OpenScop) : result (option (PolyLang.t*iss_witness)) :=
  Err "double ISS producer not installed"%string.
Definition infer_tiling_witness_scops (_ _ : OpenScop) : result (list statement_tiling_witness) :=
  Err "supply checked tiling witness data"%string.
End DoubleAssignmentIRs.
Module DoubleAssignmentValidator := AffineValidator DoubleAssignmentIRs.
Module DoubleAssignmentTilingValidator := TilingValidator DoubleAssignmentIRs.
Module DoubleAssignmentPrepare := PrepareCodegen DoubleAssignmentIRs.
Module DoubleAssignmentExtractor := ExtractorCorrect DoubleAssignmentIRs.

Definition validate_double_equivalence source candidate :=
  BIND backward <- DoubleAssignmentValidator.validate source candidate -;
  BIND forward <- DoubleAssignmentValidator.validate candidate source -;
  pure (backward && forward).
Lemma validate_double_equivalence_results source candidate :
  mayReturn (validate_double_equivalence source candidate) true ->
  mayReturn (DoubleAssignmentValidator.validate source candidate) true /\
  mayReturn (DoubleAssignmentValidator.validate candidate source) true.
Proof.
  intro VALID; unfold validate_double_equivalence in VALID.
  bind_imp_destruct VALID backward BACKWARD; bind_imp_destruct VALID forward FORWARD.
  apply mayReturn_pure in VALID; apply andb_true_iff in VALID as [BACK FOR]; subst backward forward; auto.
Qed.

Theorem validated_double_equivalence_at source candidate parameters initial final :
  List.length (snd (fst source)) = List.length parameters -> List.length (snd (fst candidate)) = List.length parameters ->
  DoubleAssignmentInstr.NonAlias initial -> mayReturn (validate_double_equivalence source candidate) true ->
  (DoubleAssignmentIRs.PolyLang.poly_instance_list_semantics parameters source initial final <->
   DoubleAssignmentIRs.PolyLang.poly_instance_list_semantics parameters candidate initial final).
Proof.
  destruct source as [[source_pis source_context] source_vars].
  destruct candidate as [[candidate_pis candidate_context] candidate_vars].
  intros SOURCE_LENGTH CANDIDATE_LENGTH NONALIAS VALID.
  destruct (validate_double_equivalence_results VALID) as [BACKWARD FORWARD]; split; intro EXEC.
  - destruct (@DoubleAssignmentValidator.validate_correct'
      (candidate_pis,candidate_context,candidate_vars) (source_pis,source_context,source_vars)
      candidate_context source_context candidate_pis source_pis candidate_vars source_vars
      parameters initial final true FORWARD eq_refl eq_refl eq_refl CANDIDATE_LENGTH NONALIAS EXEC)
      as [result [RUN SAME]].
    unfold DoubleAssignmentIRs.State.eq,DoubleAssignmentInstr.State.eq in SAME; subst result; exact RUN.
  - destruct (@DoubleAssignmentValidator.validate_correct'
      (source_pis,source_context,source_vars) (candidate_pis,candidate_context,candidate_vars)
      source_context candidate_context source_pis candidate_pis source_vars candidate_vars
      parameters initial final true BACKWARD eq_refl eq_refl eq_refl SOURCE_LENGTH NONALIAS EXEC)
      as [result [RUN SAME]].
    unfold DoubleAssignmentIRs.State.eq,DoubleAssignmentInstr.State.eq in SAME; subst result; exact RUN.
Qed.

(** Pipeline checks have a backward direction. Generated-loop progress and
    target lowering still need the candidate/site bridge used at installation. *)
Definition checked_double_schedule_codegen source candidate :=
  BIND valid <- DoubleAssignmentValidator.validate source candidate -;
  if valid then BIND generated <- DoubleAssignmentPrepare.prepared_codegen candidate -;
    pure (Some generated)
  else pure None.
Theorem checked_double_schedule_codegen_correct source candidate generated initial final :
  mayReturn (checked_double_schedule_codegen source candidate) (Some generated) ->
  DoubleAssignmentIRs.Loop.semantics generated initial final ->
  DoubleAssignmentIRs.PolyLang.instance_list_semantics source initial final.
Proof.
  intros CHECK EXEC; unfold checked_double_schedule_codegen in CHECK.
  bind_imp_destruct CHECK valid VALID; destruct valid; [|apply mayReturn_pure in CHECK; discriminate].
  bind_imp_destruct CHECK actual GENERATED; apply mayReturn_pure in CHECK; inversion CHECK; subst actual.
  destruct (DoubleAssignmentValidator.validate_preserve_wf_pprog _ _ _ VALID eq_refl) as [_ WF].
  pose proof (DoubleAssignmentPrepare.prepared_codegen_correct candidate initial final generated GENERATED WF EXEC) as MODEL.
  destruct (DoubleAssignmentValidator.validate_correct source candidate initial final true VALID eq_refl MODEL)
    as [source_final [SOURCE SAME]].
  unfold DoubleAssignmentIRs.State.eq,DoubleAssignmentInstr.State.eq in SAME; subst source_final; exact SOURCE.
Qed.

Print Assumptions DoubleAssignmentValidator.validate_correct.
Print Assumptions DoubleAssignmentTilingValidator.checked_tiling_validate_poly_correct.
Print Assumptions DoubleAssignmentPrepare.prepared_codegen_correct.
Print Assumptions DoubleAssignmentExtractor.extractor_correct.
Print Assumptions validated_double_equivalence_at.
Print Assumptions checked_double_schedule_codegen_correct.
