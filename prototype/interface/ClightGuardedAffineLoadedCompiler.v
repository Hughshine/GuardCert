From Stdlib Require Import List.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Clight Csyntax Csem Cstrategy
  SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion ClightPrivatePool ClightTempFootprint GuardCompiler.
From GuardMemory Require Import GuardMemoryNamedCompiler GuardMemoryTiledCompiler GuardMemoryCompiler.
From GuardInterface Require Import ClightAffineInnerPointerCandidates ClightAffineLoadedCandidates ClightLoadedRegionHost.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Fixpoint checked_affine_loaded_regions live pool profile propose sources :
  CoreAlarmed.Base.imp (list (Clight.statement * Clight.statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND candidate <- check_affine_loaded_source live pool profile propose source -;
    BIND table <- checked_affine_loaded_regions live pool profile propose rest -;
    pure (match candidate with Some target => (source,target)::table | None => table end)
  end.
Theorem checked_affine_loaded_regions_sound live pool profile propose sources table :
  mayReturn (checked_affine_loaded_regions live pool profile propose sources) table ->
  Forall (fun pair => PrivateRegion.projected_region_contract live (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources as [|source rest IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst table; constructor.
  - bind_imp_destruct RUN candidate CANDIDATE; bind_imp_destruct RUN rest_table TAIL.
    apply mayReturn_pure in RUN; destruct candidate as [target|]; subst table;
      [constructor; [eapply check_affine_loaded_source_sound; exact CANDIDATE|]|];
      apply IH; exact TAIL.
Qed.

(** A metadata and candidate proposer supplies this user pass. Both are
    untrusted; checked actual source descriptions, source-supported condition
    evidence and candidate certificates precede language installation. *)
Definition compile_guarded_affine_loaded (profile : affine_inner_pointer_profiler)
  (propose : affine_inner_pointer_proposer) private_count (program : Csyntax.program) :
  CoreAlarmed.Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      let live := program_temps normalized in
      let pool := propose_private_names live private_count in
      BIND table <- checked_affine_loaded_regions live pool profile propose
        (memory_program_candidates normalized) -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight
        (apply_loaded_region_table pool table normalized)))
    end
  end.

Theorem guarded_affine_loaded_cstrategy_forward profile propose private_count program target :
  mayReturn (compile_guarded_affine_loaded profile propose private_count program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_guarded_affine_loaded.
  destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1.
  2: intro RUN; apply mayReturn_pure in RUN; discriminate.
  destruct (SimplLocals.transf_program clight) as [normalized|errors] eqn:P2.
  2: intro RUN; apply mayReturn_pure in RUN; discriminate.
  intro RUN; bind_imp_destruct RUN table TABLE.
  apply mayReturn_pure in RUN; rewrite Compiler.print_identity in RUN.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply apply_loaded_region_table_correct;
      eapply checked_affine_loaded_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact RUN.
Qed.

Theorem compile_guarded_affine_loaded_correct profile propose private_count program target :
  mayReturn (compile_guarded_affine_loaded profile propose private_count program) (OK target) ->
  backward_simulation (Csem.semantics program) (Asm.semantics target).
Proof.
  intro RUN; apply compose_backward_simulation with (atomic (Cstrategy.semantics program)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * eapply guarded_affine_loaded_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.

Print Assumptions checked_affine_loaded_regions_sound.
Print Assumptions guarded_affine_loaded_cstrategy_forward.
Print Assumptions compile_guarded_affine_loaded_correct.
