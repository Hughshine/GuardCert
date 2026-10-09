From Stdlib Require Import List Bool.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Clight Csyntax Csem Cstrategy
  SimplExpr SimplExprproof SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import GuardCompiler ClightRegionProgress ClightGlobalScope ClightPrivatePool
  ClightTempFootprint ClightTempScope ClightScopedPrivateRegion ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryDoubleCandidateProgress GuardMemoryTiledCompiler.
From GuardInterface Require Import ClightSelectedRegion ClightScopedSelectedRegion ClightScopedSelectedRegionProof
  InitializedDoubleRegionFactory InitializedDoubleBoundedTiledRegionFactory InitializedDoubleSelectedCompiler
  DoubleBoundedTiledChoicesCompiler OriginalMatmulProgramCompiler OriginalMatmulActualProgramCompiler.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Fixpoint checked_initialized_bounded_tiled_regions p live pool phase adapt choices sources : Base.imp (list (Clight.statement*Clight.statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND target <- check_initialized_double_bounded_tiled_region p live pool phase adapt choices source -;
    BIND table <- checked_initialized_bounded_tiled_regions p live pool phase adapt choices rest -;
    pure (match target with Some target => (source,target)::table | None => table end)
  end.
Lemma checked_initialized_bounded_tiled_regions_individual p live pool phase adapt choices sources table :
  mayReturn (checked_initialized_bounded_tiled_regions p live pool phase adapt choices sources) table ->
  Forall (fun pair => In (fst pair) sources /\
    ScopedPrivateRegion.projected_region_contract live (Clight.globalenv p)
      (initialized_double_source_globals p (fst pair)) (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst table; constructor.
  - bind_imp_destruct RUN target TARGET; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    pose proof (IH rest REST) as TAIL.
    assert (EXTEND : Forall (fun pair => In (fst pair) (source::sources) /\
      ScopedPrivateRegion.projected_region_contract live (Clight.globalenv p)
        (initialized_double_source_globals p (fst pair)) (fst pair) (snd pair)) rest).
    { eapply Forall_impl; [|exact TAIL]; intros pair [MEMBER CONTRACT]; split; [right; exact MEMBER|exact CONTRACT]. }
    destruct target as [target|]; subst table; [constructor; [|exact EXTEND]|exact EXTEND].
    split; [left; reflexivity|eapply check_initialized_double_bounded_tiled_region_sound; exact TARGET].
Qed.
Theorem checked_initialized_bounded_tiled_regions_sound p live pool phase adapt choices sources table :
  mayReturn (checked_initialized_bounded_tiled_regions p live pool phase adapt choices sources) table ->
  Forall (fun pair => ScopedPrivateRegion.projected_region_contract live (Clight.globalenv p)
    (initialized_double_sources_globals p sources) (fst pair) (snd pair)) table.
Proof.
  intro RUN; eapply Forall_impl; [|eapply checked_initialized_bounded_tiled_regions_individual; exact RUN].
  intros [source target] [MEMBER CONTRACT]; cbn in MEMBER,CONTRACT |- *.
  eapply scoped_initialized_contract_weaken; [|exact CONTRACT].
  intros identifier GLOBAL; unfold initialized_double_sources_globals; apply in_flat_map.
  exists source; split; assumption.
Qed.
Definition checked_selected_initialized_bounded_tiled_program chosen private_count phase adapt choices p :=
  let live := program_temps p in
  let pool := propose_private_names live private_count in
  BIND table <- checked_initialized_bounded_tiled_regions p live pool phase adapt choices (selected_program_candidates chosen p) -;
  pure (apply_selected_initialized_double_table chosen pool table p).
Theorem checked_selected_initialized_bounded_tiled_program_correct chosen private_count phase adapt choices p target :
  mayReturn (checked_selected_initialized_bounded_tiled_program chosen private_count phase adapt choices p) target ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 target).
Proof.
  unfold checked_selected_initialized_bounded_tiled_program; intro RUN; bind_imp_destruct RUN table TABLE.
  apply mayReturn_pure in RUN; subst target; apply apply_selected_initialized_double_table_correct.
  eapply checked_initialized_bounded_tiled_regions_sound; exact TABLE.
Qed.

(** Recompute all site evidence on each intermediate program. *)
Definition checked_selected_initialized_bounded_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices p :=
  BIND initialized <- checked_selected_initialized_bounded_tiled_program chosen private_count phase adapt choices p -;
  DoubleBoundedTiledChoicesCompiler.checked_selected_bounded_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices initialized.
Theorem checked_selected_initialized_bounded_tiled_choices_program_correct chosen private_count phase adapt schedule inherited_swaps choices p target :
  mayReturn (checked_selected_initialized_bounded_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices p) target ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 target).
Proof.
  unfold checked_selected_initialized_bounded_tiled_choices_program; intro RUN; bind_imp_destruct RUN initialized INITIALIZED.
  eapply compose_forward_simulations.
  - eapply checked_selected_initialized_bounded_tiled_program_correct; exact INITIALIZED.
  - eapply DoubleBoundedTiledChoicesCompiler.checked_selected_bounded_tiled_choices_program_correct; exact RUN.
Qed.
Definition compile_selected_initialized_bounded_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices (program : Csyntax.program) : Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with Error errors => pure (Error errors) | OK clight =>
    match SimplLocals.transf_program clight with Error errors => pure (Error errors) | OK normalized =>
      BIND target <- checked_selected_initialized_bounded_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices normalized -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight target)) end end.
Theorem selected_initialized_bounded_tiled_choices_program_cstrategy_forward chosen private_count phase adapt schedule inherited_swaps choices program target :
  mayReturn (compile_selected_initialized_bounded_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_selected_initialized_bounded_tiled_choices_program; destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  destruct (SimplLocals.transf_program clight) as [normalized|errors] eqn:P2;
    [|intro RUN; apply mayReturn_pure in RUN; discriminate].
  intro RUN; bind_imp_destruct RUN installed INSTALL; apply mayReturn_pure in RUN.
  rewrite Compiler.print_identity in RUN.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { eapply checked_selected_initialized_bounded_tiled_choices_program_correct; exact INSTALL. }
  eapply clight_tail_correct; exact RUN.
Qed.
Theorem compile_selected_initialized_bounded_tiled_choices_program_correct chosen private_count phase adapt schedule inherited_swaps choices program target :
  mayReturn (compile_selected_initialized_bounded_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices program) (OK target) ->
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
      * eapply selected_initialized_bounded_tiled_choices_program_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.


Print Assumptions checked_selected_initialized_bounded_tiled_program_correct.
Print Assumptions checked_selected_initialized_bounded_tiled_choices_program_correct.
Print Assumptions compile_selected_initialized_bounded_tiled_choices_program_correct.
