From Stdlib Require Import List Bool.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion ClightPrivatePool ClightTempFootprint GuardCompiler.
From GuardMemory Require Import GuardMemoryCompiler GuardMemoryTiledCompiler.
From GuardAffineNest Require Import AffineNestCheckedCompiler.
From GuardInterface Require Import ClightNestedStabilityFactory ClightExpressionRegionHost.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.

Fixpoint checked_ncs_stability_regions live pool describe propose sources := match sources with
  | []=>pure []
  | source::rest=>
    BIND candidate <- check_ncs_stability_frontend_region live pool describe propose source -;
    BIND table <- checked_ncs_stability_regions live pool describe propose rest -;
    pure(match candidate with Some target=>(source,target)::table|None=>table end) end.
Lemma checked_ncs_stability_regions_sound live pool describe propose sources table :
  mayReturn(checked_ncs_stability_regions live pool describe propose sources) table ->
  Forall(fun pair=>projected_region_contract live(fst pair)(snd pair)) table.
Proof.
  revert table; induction sources; intros table CHECK; cbn in CHECK.
  - apply mayReturn_pure in CHECK; subst; constructor.
  - bind_imp_destruct CHECK candidate CANDIDATE; bind_imp_destruct CHECK rest REST.
    apply mayReturn_pure in CHECK; destruct candidate as [target|]; subst; [constructor|];
      eauto using check_ncs_stability_frontend_region_sound.
Qed.

Definition compile_ncs_stability_regions describe propose private_count(program:Csyntax.program) : CoreAlarmed.Base.imp(res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors=>pure(Error errors)
  | OK clight=>match SimplLocals.transf_program clight with
    | Error errors=>pure(Error errors)
    | OK normalized=>
      let live:=program_temps normalized in
      let pool:=propose_private_names live private_count in
      BIND table <- checked_ncs_stability_regions live pool describe propose(memory_program_candidates normalized) -;
      pure(compile_clight_tail(Compiler.print Compiler.print_Clight(apply_expression_region_table pool table normalized))) end end.

Theorem ncs_stability_cstrategy_forward describe propose private_count program target :
  mayReturn(compile_ncs_stability_regions describe propose private_count program)(OK target) ->
  forward_simulation(Cstrategy.semantics program)(Asm.semantics target).
Proof.
  unfold compile_ncs_stability_regions; destruct(SimplExpr.transl_program program) as [clight|errors] eqn:P1.
  2:intro RUN; apply mayReturn_pure in RUN; discriminate.
  destruct(SimplLocals.transf_program clight) as [normalized|errors] eqn:P2.
  2:intro RUN; apply mayReturn_pure in RUN; discriminate.
  intro RUN; bind_imp_destruct RUN table TABLE.
  apply mayReturn_pure in RUN; rewrite Compiler.print_identity in RUN.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply apply_expression_region_table_correct; eapply checked_ncs_stability_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact RUN.
Qed.

Theorem compile_ncs_stability_regions_correct describe propose private_count program target :
  mayReturn(compile_ncs_stability_regions describe propose private_count program)(OK target) ->
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
      * apply ncs_stability_cstrategy_forward with(describe:=describe)(propose:=propose)(private_count:=private_count); exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions ncs_stability_cstrategy_forward.
Print Assumptions checked_ncs_stability_regions_sound.
Print Assumptions compile_ncs_stability_regions_correct.
