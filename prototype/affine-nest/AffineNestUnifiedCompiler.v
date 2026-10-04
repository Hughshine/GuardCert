From Stdlib Require Import List Bool.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion ClightPrivatePool ClightTempFootprint GuardCompiler
  ClightGuard ClightGuardProof ClightNoWrap ClightTreeRewrite ClightTreeRewriteProof ClightSameAddress ClightSignedCancel.
From GuardMemory Require Import GuardMemoryCompiler GuardMemoryTiledCompiler GuardMemoryUnifiedCompiler.
From GuardAffineNest Require Import AffineNestCheckedCompiler AffineNestMultiCheckedCompiler ClightVariableCancel.
Import CoreAlarmed ListNotations PrivateRegion.
Set Implicit Arguments.

(** One whole-program pipeline consumes deep affine and existing rectangular
    memory services, then applies the existing conditional scalar rewrites. *)
Definition check_guardcert_region live pool describe propose_affine propose_memory source :=
  BIND candidate <- check_affine_region live pool describe propose_affine source -;
  match candidate with
  | Some target=>pure(Some target)
  | None=>BIND multiple <- check_affine_multi_region live pool describe propose_affine source -;
    match multiple with
    | Some target=>pure(Some target)
    | None=>check_memory_unified_region live pool propose_memory source end end.
Theorem check_guardcert_region_sound live pool describe propose_affine propose_memory source target :
  mayReturn(check_guardcert_region live pool describe propose_affine propose_memory source)(Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_guardcert_region; intro RUN; bind_imp_destruct RUN candidate CHECK.
  destruct candidate as [candidate|].
  - apply mayReturn_pure in RUN; inversion RUN; subst; eapply check_affine_region_sound; exact CHECK.
  - bind_imp_destruct RUN multiple MULTIPLE; destruct multiple as [multiple|].
    + apply mayReturn_pure in RUN; inversion RUN; subst; eapply check_affine_multi_region_sound; exact MULTIPLE.
    + eapply check_memory_unified_region_sound; exact RUN.
Qed.
Fixpoint checked_guardcert_regions live pool describe propose_affine propose_memory sources := match sources with
  | []=>pure []
  | source::rest=>
    BIND candidate <- check_guardcert_region live pool describe propose_affine propose_memory source -;
    BIND table <- checked_guardcert_regions live pool describe propose_affine propose_memory rest -;
    pure(match candidate with Some target=>(source,target)::table|None=>table end) end.
Lemma checked_guardcert_regions_sound live pool describe propose_affine propose_memory sources table :
  mayReturn(checked_guardcert_regions live pool describe propose_affine propose_memory sources) table ->
  Forall(fun pair=>projected_region_contract live(fst pair)(snd pair)) table.
Proof.
  revert table; induction sources; intros table CHECK; cbn in CHECK.
  - apply mayReturn_pure in CHECK; subst; constructor.
  - bind_imp_destruct CHECK candidate CANDIDATE; bind_imp_destruct CHECK rest REST.
    apply mayReturn_pure in CHECK; destruct candidate as [target|]; subst; [constructor|];
      eauto using check_guardcert_region_sound.
Qed.

Definition guardcert_scalar_rewrites program :=
  ClightTreeRewrite.transform_program select_all_guardcert_rewrites
    (ClightGuard.transform_program select_no_wrap program).
Lemma guardcert_scalar_rewrites_correct program :
  forward_simulation(Clight.semantics2 program)(Clight.semantics2(guardcert_scalar_rewrites program)).
Proof.
  unfold guardcert_scalar_rewrites; eapply compose_forward_simulations.
  - apply ClightGuardProof.transform_program_correct2; exact select_no_wrap_sound.
  - apply ClightTreeRewriteProof.transform_program_correct2; exact select_all_guardcert_rewrites_sound.
Qed.

Definition compile_guardcert describe propose_affine propose_memory private_count(program:Csyntax.program) : CoreAlarmed.Base.imp(res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors=>pure(Error errors)
  | OK clight=>match SimplLocals.transf_program clight with
    | Error errors=>pure(Error errors)
    | OK normalized=>let live:=program_temps normalized in let pool:=propose_private_names live private_count in
      BIND table <- checked_guardcert_regions live pool describe propose_affine propose_memory(memory_program_candidates normalized) -;
      pure(compile_clight_tail(Compiler.print Compiler.print_Clight
        (guardcert_scalar_rewrites(apply_memory_tiled_table pool table normalized)))) end end.

Theorem guardcert_cstrategy_forward describe propose_affine propose_memory private_count program target :
  mayReturn(compile_guardcert describe propose_affine propose_memory private_count program)(OK target) ->
  forward_simulation(Cstrategy.semantics program)(Asm.semantics target).
Proof.
  unfold compile_guardcert; destruct(SimplExpr.transl_program program) as [clight|errors] eqn:P1.
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
  { apply apply_memory_tiled_table_correct; eapply checked_guardcert_regions_sound; exact TABLE. }
  eapply compose_forward_simulations.
  { apply guardcert_scalar_rewrites_correct. }
  eapply clight_tail_correct; exact RUN.
Qed.

Theorem compile_guardcert_correct describe propose_affine propose_memory private_count program target :
  mayReturn(compile_guardcert describe propose_affine propose_memory private_count program)(OK target) ->
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
      * apply guardcert_cstrategy_forward with(describe:=describe)(propose_affine:=propose_affine)
          (propose_memory:=propose_memory)(private_count:=private_count); exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
Print Assumptions check_guardcert_region_sound.
Print Assumptions compile_guardcert_correct.
