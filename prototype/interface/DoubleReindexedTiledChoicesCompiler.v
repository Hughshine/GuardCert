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
  ReductionDoubleRegionFactory ReductionDoubleReindexedTiledFactory ReductionDoubleSelectedCompiler
  ReductionDoubleChoicesCompiler OriginalMatmulProgramCompiler.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition tiled_double_sources_globals p sources :=
  flat_map (reduction_double_source_globals p) sources.
Fixpoint checked_tiled_double_regions p live pool phase adapt choices sources : Base.imp (list (Clight.statement*Clight.statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND target <- check_reindexed_tiled_reduction_double_region p live pool phase adapt choices source -;
    BIND table <- checked_tiled_double_regions p live pool phase adapt choices rest -;
    pure (match target with Some target => (source,target)::table | None => table end)
  end.
Lemma checked_tiled_double_regions_individual p live pool phase adapt choices sources table :
  mayReturn (checked_tiled_double_regions p live pool phase adapt choices sources) table ->
  Forall (fun pair => In (fst pair) sources /\
    ScopedPrivateRegion.projected_region_contract live (Clight.globalenv p)
      (reduction_double_source_globals p (fst pair)) (fst pair) (snd pair)) table.
Proof.
  revert table; induction sources as [|source sources IH]; intros table RUN; cbn in RUN.
  - apply mayReturn_pure in RUN; subst table; constructor.
  - bind_imp_destruct RUN target TARGET; bind_imp_destruct RUN rest REST; apply mayReturn_pure in RUN.
    pose proof (IH rest REST) as TAIL.
    assert (EXTEND : Forall (fun pair => In (fst pair) (source::sources) /\
      ScopedPrivateRegion.projected_region_contract live (Clight.globalenv p)
        (reduction_double_source_globals p (fst pair)) (fst pair) (snd pair)) rest).
    { eapply Forall_impl; [|exact TAIL]; intros pair [MEMBER CONTRACT]; split; [right; exact MEMBER|exact CONTRACT]. }
    destruct target as [target|]; subst table; [constructor; [|exact EXTEND]|exact EXTEND].
    split; [left; reflexivity|eapply check_reindexed_tiled_reduction_double_region_sound; exact TARGET].
Qed.
Theorem checked_tiled_double_regions_sound p live pool phase adapt choices sources table :
  mayReturn (checked_tiled_double_regions p live pool phase adapt choices sources) table ->
  Forall (fun pair => ScopedPrivateRegion.projected_region_contract live (Clight.globalenv p)
    (tiled_double_sources_globals p sources) (fst pair) (snd pair)) table.
Proof.
  intro RUN; eapply Forall_impl; [|eapply checked_tiled_double_regions_individual; exact RUN].
  intros [source target] [MEMBER CONTRACT]; cbn in MEMBER,CONTRACT |- *.
  eapply scoped_reduction_contract_weaken; [|exact CONTRACT].
  intros identifier GLOBAL; unfold tiled_double_sources_globals; apply in_flat_map.
  exists source; split; assumption.
Qed.
Lemma select_tiled_double_table_sound live reference globals table :
  Forall (fun pair => ScopedPrivateRegion.projected_region_contract live reference globals (fst pair) (snd pair)) table ->
  forall source target, select_memory_tiled_table table source=Some target ->
    ScopedPrivateRegion.projected_region_contract live reference globals source target.
Proof.
  intro TABLE; induction TABLE as [|[original candidate] rest HEAD TAIL IH]; intros source target; cbn.
  - discriminate.
  - destruct (statement_eq source original) as [SAME|DIFFERENT]; [subst original|apply IH].
    intro SELECT; inversion SELECT; subst target; exact HEAD.
Qed.
Definition apply_selected_tiled_double_table chosen pool table p :=
  let globals := tiled_double_sources_globals p (selected_program_candidates chosen p) in
  if program_avoids_check globals p && private_pool_check (program_temps p) pool then
    ScopedSelectedRegion.transform_program chosen pool (reduction_double_progress_supported p)
      (select_memory_tiled_table table) p else p.
Theorem apply_selected_tiled_double_table_correct chosen pool table p :
  Forall (fun pair => ScopedPrivateRegion.projected_region_contract (program_temps p) (Clight.globalenv p)
    (tiled_double_sources_globals p (selected_program_candidates chosen p)) (fst pair) (snd pair)) table ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (apply_selected_tiled_double_table chosen pool table p)).
Proof.
  intro TABLE; unfold apply_selected_tiled_double_table.
  destruct (program_avoids_check _ p && private_pool_check (program_temps p) pool) eqn:PROFILE.
  - apply andb_true_iff in PROFILE as [GLOBAL PRIVATE].
    eapply ScopedSelectedRegionProof.transform_program_correct2 with (live:=program_temps p).
    + apply reduction_double_progress_supported_sound.
    + apply program_avoids_check_sound; exact GLOBAL.
    + apply select_tiled_double_table_sound; exact TABLE.
    + apply program_scope_computed.
    + apply private_pool_check_sound; exact PRIVATE.
  - apply unchanged_clight_simulation.
Qed.
Definition checked_selected_tiled_double_program chosen private_count phase adapt choices p :=
  let live := program_temps p in
  let pool := propose_private_names live private_count in
  BIND table <- checked_tiled_double_regions p live pool phase adapt choices (selected_program_candidates chosen p) -;
  pure (apply_selected_tiled_double_table chosen pool table p).
Theorem checked_selected_tiled_double_program_correct chosen private_count phase adapt choices p target :
  mayReturn (checked_selected_tiled_double_program chosen private_count phase adapt choices p) target ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 target).
Proof.
  unfold checked_selected_tiled_double_program; intro RUN; bind_imp_destruct RUN table TABLE.
  apply mayReturn_pure in RUN; subst target; apply apply_selected_tiled_double_table_correct.
  eapply checked_tiled_double_regions_sound; exact TABLE.
Qed.


(** Compose tiling and the existing affine/source routes on the current program.
    Every stage recomputes actual scope and private resources. *)
Definition checked_selected_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices p :=
  BIND tiled <- checked_selected_tiled_double_program chosen private_count phase adapt choices p -;
  ReductionDoubleChoicesCompiler.checked_selected_reduction_choices_program chosen private_count schedule inherited_swaps choices tiled.
Theorem checked_selected_tiled_choices_program_correct chosen private_count phase adapt schedule inherited_swaps choices p target :
  mayReturn (checked_selected_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices p) target ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 target).
Proof.
  unfold checked_selected_tiled_choices_program; intro RUN; bind_imp_destruct RUN tiled TILED.
  eapply compose_forward_simulations.
  - eapply checked_selected_tiled_double_program_correct; exact TILED.
  - eapply ReductionDoubleChoicesCompiler.checked_selected_reduction_choices_program_correct; exact RUN.
Qed.
Definition compile_selected_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices (program : Csyntax.program) : Base.imp (res Asm.program) :=
  match SimplExpr.transl_program program with Error errors => pure (Error errors) | OK clight =>
    match SimplLocals.transf_program clight with Error errors => pure (Error errors) | OK normalized =>
      BIND target <- checked_selected_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices normalized -;
      pure (compile_clight_tail (Compiler.print Compiler.print_Clight target)) end end.
Theorem selected_tiled_choices_program_cstrategy_forward chosen private_count phase adapt schedule inherited_swaps choices program target :
  mayReturn (compile_selected_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices program) (OK target) ->
  forward_simulation (Cstrategy.semantics program) (Asm.semantics target).
Proof.
  unfold compile_selected_tiled_choices_program; destruct (SimplExpr.transl_program program) as [clight|errors] eqn:P1;
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
  { eapply checked_selected_tiled_choices_program_correct; exact INSTALL. }
  eapply clight_tail_correct; exact RUN.
Qed.
Theorem compile_selected_tiled_choices_program_correct chosen private_count phase adapt schedule inherited_swaps choices program target :
  mayReturn (compile_selected_tiled_choices_program chosen private_count phase adapt schedule inherited_swaps choices program) (OK target) ->
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
      * eapply selected_tiled_choices_program_cstrategy_forward; exact RUN.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.


Print Assumptions checked_selected_tiled_double_program_correct.
Print Assumptions checked_selected_tiled_choices_program_correct.
Print Assumptions compile_selected_tiled_choices_program_correct.
