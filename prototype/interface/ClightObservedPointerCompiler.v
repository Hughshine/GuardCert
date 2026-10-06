From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy
  SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightPrivateRegion ClightPrivatePool ClightTempFootprint
  ClightStructuredProgress ClightStraightLine ClightRectangularSelector ClightRegionProgress GuardCompiler.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryNamedOperations
  GuardMemoryNamedCandidate GuardMemoryNamedCompiler GuardMemoryTiledCompiler GuardMemoryCompiler.
From Guard Require Import ClightPrivateRegionProof ClightTempScope.
From GuardInterface Require Import ClightParamPointerCandidates ClightParamPointerCompiler ClightObservedPointerCandidates
  ClightSequenceProgressSelector.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint checked_realized_observed_pointer_regions shared live pool propose sources :
  CoreAlarmed.Base.imp (list (Clight.statement * Clight.statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND candidate <- check_realized_observed_or_scanned_pointer_source shared live pool propose source -;
    BIND table <- checked_realized_observed_pointer_regions shared live pool propose rest -;
    pure (match candidate with Some target => (source,target)::table | None => table end)
  end.
Theorem checked_realized_observed_pointer_regions_sound shared live pool propose sources table :
  mayReturn (checked_realized_observed_pointer_regions shared live pool propose sources) table ->
  Forall (fun pair => PrivateRegion.projected_region_contract live (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources as [|source rest IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst table; constructor.
  - bind_imp_destruct RUN candidate CANDIDATE; bind_imp_destruct RUN rest_table TAIL.
    apply mayReturn_pure in RUN; destruct candidate as [target|]; subst table;
      [constructor; [eapply check_realized_observed_or_scanned_pointer_source_sound; exact CANDIDATE|]|];
      apply IH; exact TAIL.
Qed.

Definition apply_preserving_observed_pointer_table pool table (p : Clight.program) :=
  transform_private_program sequence_progress_supported
    (fun _ _ => select_memory_tiled_table table) pool p.
Theorem apply_preserving_observed_pointer_table_correct pool table p :
  Forall (fun pair => PrivateRegion.projected_region_contract (program_temps p) (fst pair) (snd pair)) table ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (apply_preserving_observed_pointer_table pool table p)).
Proof.
  intro TABLE; unfold apply_preserving_observed_pointer_table,transform_private_program.
  destruct (private_pool_check (program_temps p) pool) eqn:FRESH.
  - eapply PrivateRegionProof.transform_program_correct2 with (live:=program_temps p).
    + exact sequence_progress_supported_sound.
    + apply select_memory_tiled_table_sound; exact TABLE.
    + apply program_scope_computed.
    + eapply private_pool_check_sound; exact FRESH.
  - apply forward_simulation_step with (match_states:=@eq Clight.state).
    + reflexivity.
    + intros source INIT; exists source; auto.
    + intros; subst; assumption.
    + intros source events next STEP target SAME; subst target; exists next; auto.
Qed.

Definition compile_realized_observed_pointer (shared : bool) (propose : pointer_preserving_proposer) private_count (program : Csyntax.program) :
  CoreAlarmed.Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with
  | Error errors => pure (Error errors)
  | OK clight => match SimplLocals.transf_program clight with
    | Error errors => pure (Error errors)
    | OK normalized =>
      let live := program_temps normalized in
      let pool := propose_private_names live private_count in
      BIND table <- checked_realized_observed_pointer_regions shared live pool propose
        (memory_program_candidates normalized) -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight
        (apply_preserving_observed_pointer_table pool table normalized)))
    end
  end.

Theorem realized_observed_pointer_cstrategy_forward shared propose private_count program target :
  mayReturn (compile_realized_observed_pointer shared propose private_count program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_realized_observed_pointer.
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
  { apply apply_preserving_observed_pointer_table_correct;
      eapply checked_realized_observed_pointer_regions_sound; exact TABLE. }
  eapply clight_tail_correct; exact RUN.
Qed.

Theorem compile_realized_observed_pointer_correct shared propose private_count program target :
  mayReturn (compile_realized_observed_pointer shared propose private_count program) (OK target) ->
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
      * eapply realized_observed_pointer_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.


Print Assumptions checked_realized_observed_pointer_regions_sound.
Print Assumptions apply_preserving_observed_pointer_table_correct.
Print Assumptions compile_realized_observed_pointer_correct.

(** The historical entry retains direct lowering. The realized entry
    quantifies over both concrete language implementations. *)
Definition checked_preserving_observed_pointer_regions live pool propose sources :=
  checked_realized_observed_pointer_regions false live pool propose sources.

Definition compile_preserving_observed_pointer (propose : pointer_preserving_proposer) private_count (program : Csyntax.program) :=
  compile_realized_observed_pointer false propose private_count program.

Theorem checked_preserving_observed_pointer_regions_sound live pool propose sources table :
  mayReturn (checked_preserving_observed_pointer_regions live pool propose sources) table ->
  Forall (fun pair => PrivateRegion.projected_region_contract live (fst pair) (snd pair)) table.
Proof. unfold checked_preserving_observed_pointer_regions; apply checked_realized_observed_pointer_regions_sound. Qed.

Print Assumptions checked_preserving_observed_pointer_regions_sound.

Theorem preserving_observed_pointer_cstrategy_forward propose private_count program target :
  mayReturn (compile_preserving_observed_pointer propose private_count program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof. unfold compile_preserving_observed_pointer; apply realized_observed_pointer_cstrategy_forward. Qed.

Theorem compile_preserving_observed_pointer_correct propose private_count program target :
  mayReturn (compile_preserving_observed_pointer propose private_count program) (OK target) ->
  backward_simulation (Csem.semantics program) (Asm.semantics target).
Proof. unfold compile_preserving_observed_pointer; apply compile_realized_observed_pointer_correct. Qed.

Print Assumptions compile_preserving_observed_pointer_correct.
