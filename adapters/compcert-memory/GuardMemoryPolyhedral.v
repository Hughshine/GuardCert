From Stdlib Require Import List Bool String.
From polcert.src Require Import PolyLang OpenScop AffineValidator ISSWitness TilingWitness.
From polcert.polygen Require Import PolIRs Loop PolyLoop Result.
From Vpl Require Import Impure.
From polcert.lib Require Import ImpureAlarmConfig.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr.
Import ListNotations.
Set Implicit Arguments.

(** External scheduling is deliberately outside this adapter. A caller gives
    the source and proposed PolyLang program directly to the actual validator. *)
Module GuardMemoryIRs <: POLIRS.
Module Instr := GuardMemoryInstr.
Module State := Instr.State.
Module Ty := Instr.Ty.
Module PolyLang := PolyLang Instr.
Module PolyLoop := PolyLoop Instr.
Module Loop := Loop Instr.
Definition scheduler (_ : PolyLang.t) : result PolyLang.t := Err "supply a candidate to validate"%string.
Definition affine_scheduler := scheduler.
Definition export_for_phase_scheduler (_ : PolyLang.t) : option OpenScop := None.
Definition export_for_pluto_phase_pipeline := export_for_phase_scheduler.
Definition to_phase_openscop := export_for_phase_scheduler.
Definition phase_scop_scheduler (_ : OpenScop) : result (OpenScop * OpenScop) := Err "no external scheduler connected"%string.
Definition run_pluto_phase_pipeline := phase_scop_scheduler.
Definition identity_tiling_phase_scop_scheduler := phase_scop_scheduler.
Definition run_pluto_identity_tiling_pipeline := identity_tiling_phase_scop_scheduler.
Definition phase_scop_scheduler_with_iss := phase_scop_scheduler.
Definition run_pluto_phase_pipeline_with_iss := phase_scop_scheduler_with_iss.
Definition post_tiling_affine_phase_scop_scheduler (_ : OpenScop) : result (OpenScop * (OpenScop * OpenScop)) :=
  Err "no external scheduler connected"%string.
Definition run_pluto_post_tiling_affine_phase_pipeline := post_tiling_affine_phase_scop_scheduler.
Definition post_tiling_affine_phase_scop_scheduler_with_iss := post_tiling_affine_phase_scop_scheduler.
Definition run_pluto_post_tiling_affine_phase_pipeline_with_iss := post_tiling_affine_phase_scop_scheduler_with_iss.
Definition infer_iss_from_source_scop (_ : PolyLang.t) (_ : OpenScop) : result (option (PolyLang.t * iss_witness)) :=
  Err "no ISS producer connected"%string.
Definition infer_tiling_witness_scops (_ _ : OpenScop) : result (list statement_tiling_witness) :=
  Err "supply a tiling witness explicitly"%string.
End GuardMemoryIRs.
Module GuardMemoryValidator := AffineValidator GuardMemoryIRs.

Theorem guarded_memory_validate_refines source candidate initial final :
  mayReturn (GuardMemoryValidator.validate source candidate) true ->
  GuardMemoryIRs.PolyLang.instance_list_semantics candidate initial final ->
  GuardMemoryIRs.PolyLang.instance_list_semantics source initial final.
Proof.
  intros VALIDATED EXEC.
  destruct (GuardMemoryValidator.validate_correct source candidate initial final true VALIDATED eq_refl EXEC)
    as [source_final [SOURCE SAME]].
  unfold GuardMemoryIRs.State.eq, GuardMemoryInstr.State.eq in SAME; subst source_final; exact SOURCE.
Qed.
Theorem guarded_memory_validate_tiling_refines source candidate initial final :
  mayReturn (GuardMemoryValidator.validate_tiling source candidate) true ->
  GuardMemoryIRs.PolyLang.instance_list_semantics candidate initial final ->
  GuardMemoryIRs.PolyLang.instance_list_semantics source initial final.
Proof.
  intros VALIDATED EXEC.
  destruct (GuardMemoryValidator.validate_tiling_correct source candidate initial final true VALIDATED eq_refl EXEC)
    as [source_final [SOURCE SAME]].
  unfold GuardMemoryIRs.State.eq, GuardMemoryInstr.State.eq in SAME; subst source_final; exact SOURCE.
Qed.
Print Assumptions GuardMemoryInstr.bc_condition_implie_permutbility.
Print Assumptions GuardMemoryValidator.validate_correct.
Print Assumptions guarded_memory_validate_refines.
Print Assumptions guarded_memory_validate_tiling_refines.

(** Affine schedules can be checked in both directions to obtain progress as
    well as endpoint refinement. This is a concrete validator construction,
    rather than a candidate-progress certificate left to a caller. *)
Definition validate_memory_equivalence source candidate :=
  BIND backward <- GuardMemoryValidator.validate source candidate -;
  BIND forward <- GuardMemoryValidator.validate candidate source -;
  pure (backward && forward).
Lemma validate_memory_equivalence_results source candidate :
  mayReturn (validate_memory_equivalence source candidate) true ->
  mayReturn (GuardMemoryValidator.validate source candidate) true /\
  mayReturn (GuardMemoryValidator.validate candidate source) true.
Proof.
  intro VALID; unfold validate_memory_equivalence in VALID.
  bind_imp_destruct VALID backward BACKWARD.
  bind_imp_destruct VALID forward FORWARD.
  apply mayReturn_pure in VALID; apply andb_true_iff in VALID as [BACK FOR]; subst backward forward; auto.
Qed.
Theorem validated_memory_equivalence source candidate initial final :
  mayReturn (validate_memory_equivalence source candidate) true ->
  (GuardMemoryIRs.PolyLang.instance_list_semantics source initial final <->
   GuardMemoryIRs.PolyLang.instance_list_semantics candidate initial final).
Proof.
  intro VALID; destruct (validate_memory_equivalence_results VALID) as [BACKWARD FORWARD].
  split; [apply guarded_memory_validate_refines; exact FORWARD|apply guarded_memory_validate_refines; exact BACKWARD].
Qed.
Print Assumptions validated_memory_equivalence.
