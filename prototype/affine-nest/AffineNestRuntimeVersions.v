From Stdlib Require Import List.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Clight Ctypes Csyntax Csem Cstrategy SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivatePool ClightTempFootprint GuardCompiler.
From GuardMemory Require Import GuardMemoryCompiler GuardMemoryTiledCompiler.
From GuardAffineNest Require Import AffineNestCheckedCompiler AffineNestUnifiedCompiler AffineNestConditionedCompiler.
Import CoreAlarmed ListNotations.
Set Implicit Arguments.

(** Each pass checks the current program and allocates a fresh private pool.
    Later passes can install another version in an earlier source fallback. *)
Fixpoint affine_version_stages (describes:list affine_source_proposer)
  propose private_count (program:Clight.program) := match describes with
  | []=>pure program
  | describe::rest=>
    let live:=program_temps program in let pool:=propose_private_names live private_count in
    BIND table <- checked_conditioned_regions live pool [describe] propose (fun _=>None)
      (memory_program_candidates program) -;
    affine_version_stages rest propose private_count (apply_memory_tiled_table pool table program)
  end.

Lemma affine_version_stages_correct describes propose private_count program target :
  mayReturn(affine_version_stages describes propose private_count program) target ->
  forward_simulation(Clight.semantics2 program)(Clight.semantics2 target).
Proof.
  revert program target; induction describes as [|describe rest IH]; intros program target RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst target.
    apply forward_simulation_step with(match_states:=@eq Clight.state).
    + reflexivity.
    + intros source INIT; exists source; auto.
    + intros; subst; assumption.
    + intros source events next STEP selected SAME; subst selected; exists next; auto.
  - bind_imp_destruct RUN table TABLE; eapply compose_forward_simulations.
    + apply apply_memory_tiled_table_correct; eapply checked_conditioned_regions_sound; exact TABLE.
    + apply IH; exact RUN.
Qed.

Definition compile_guardcert_versions describes propose propose_memory private_count(program:Csyntax.program) :
  CoreAlarmed.Base.imp(res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors=>pure(Error errors)
  | OK clight=>match SimplLocals.transf_program clight with
    | Error errors=>pure(Error errors)
    | OK normalized=>
      BIND versioned <- affine_version_stages describes propose private_count normalized -;
      let live:=program_temps versioned in let pool:=propose_private_names live private_count in
      BIND table <- checked_guardcert_regions live pool (fun _ _ _=>None) (fun _=>None) propose_memory
        (memory_program_candidates versioned) -;
      pure(compile_clight_tail(Compiler.print Compiler.print_Clight
        (guardcert_scalar_rewrites(apply_memory_tiled_table pool table versioned))))
    end end.

Theorem versions_cstrategy_forward describes propose propose_memory private_count program target :
  mayReturn(compile_guardcert_versions describes propose propose_memory private_count program)(OK target) ->
  forward_simulation(Cstrategy.semantics program)(Asm.semantics target).
Proof.
  unfold compile_guardcert_versions; destruct(SimplExpr.transl_program program) as [clight|errors] eqn:P1.
  2:intro RUN; apply mayReturn_pure in RUN; discriminate.
  destruct(SimplLocals.transf_program clight) as [normalized|errors] eqn:P2.
  2:intro RUN; apply mayReturn_pure in RUN; discriminate.
  intro RUN; bind_imp_destruct RUN versioned VERSIONS.
  bind_imp_destruct RUN table TABLE.
  apply mayReturn_pure in RUN; rewrite Compiler.print_identity in RUN.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { eapply affine_version_stages_correct; exact VERSIONS. }
  eapply compose_forward_simulations.
  { apply apply_memory_tiled_table_correct; eapply checked_guardcert_regions_sound; exact TABLE. }
  eapply compose_forward_simulations.
  { apply guardcert_scalar_rewrites_correct. }
  eapply clight_tail_correct; exact RUN.
Qed.

Theorem compile_guardcert_versions_correct describes propose propose_memory private_count program target :
  mayReturn(compile_guardcert_versions describes propose propose_memory private_count program)(OK target) ->
  backward_simulation(Csem.semantics program)(Asm.semantics target).
Proof.
  intro RUN.
  apply compose_backward_simulation with(atomic(Cstrategy.semantics program)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * apply versions_cstrategy_forward with(describes:=describes)(propose:=propose)(propose_memory:=propose_memory)
          (private_count:=private_count); exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions compile_guardcert_versions_correct.
