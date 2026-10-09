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
  ReductionDoubleRegionFactory ReductionDoubleQuotientFactory ReductionDoubleSelectedCompiler
  ReductionDoubleChoicesCompiler OriginalMatmulProgramCompiler.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

Definition quotient_tiled_double_sources_globals p sources :=
  flat_map (reduction_double_source_globals p) sources.
Fixpoint checked_quotient_tiled_double_regions p live pool phase adapt choices divisor sources : Base.imp (list (Clight.statement*Clight.statement)) :=
  match sources with
  | [] => pure []
  | source::rest =>
    BIND target <- check_quotient_reduction_double_region p live pool phase adapt choices divisor source -;
    BIND table <- checked_quotient_tiled_double_regions p live pool phase adapt choices divisor rest -;
    pure (match target with Some target => (source,target)::table | None => table end)
  end.
Lemma checked_quotient_tiled_double_regions_individual p live pool phase adapt choices divisor sources table :
  mayReturn (checked_quotient_tiled_double_regions p live pool phase adapt choices divisor sources) table ->
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
    split; [left; reflexivity|eapply check_quotient_reduction_double_region_sound; exact TARGET].
Qed.
Theorem checked_quotient_tiled_double_regions_sound p live pool phase adapt choices divisor sources table :
  mayReturn (checked_quotient_tiled_double_regions p live pool phase adapt choices divisor sources) table ->
  Forall (fun pair => ScopedPrivateRegion.projected_region_contract live (Clight.globalenv p)
    (quotient_tiled_double_sources_globals p sources) (fst pair) (snd pair)) table.
Proof.
  intro RUN; eapply Forall_impl; [|eapply checked_quotient_tiled_double_regions_individual; exact RUN].
  intros [source target] [MEMBER CONTRACT]; cbn in MEMBER,CONTRACT |- *.
  eapply scoped_reduction_contract_weaken; [|exact CONTRACT].
  intros identifier GLOBAL; unfold quotient_tiled_double_sources_globals; apply in_flat_map.
  exists source; split; assumption.
Qed.
Lemma select_quotient_tiled_double_table_sound live reference globals table :
  Forall (fun pair => ScopedPrivateRegion.projected_region_contract live reference globals (fst pair) (snd pair)) table ->
  forall source target, select_memory_tiled_table table source=Some target ->
    ScopedPrivateRegion.projected_region_contract live reference globals source target.
Proof.
  intro TABLE; induction TABLE as [|[original candidate] rest HEAD TAIL IH]; intros source target; cbn.
  - discriminate.
  - destruct (statement_eq source original) as [SAME|DIFFERENT]; [subst original|apply IH].
    intro SELECT; inversion SELECT; subst target; exact HEAD.
Qed.
Definition apply_selected_quotient_tiled_double_table chosen pool table p :=
  let globals := quotient_tiled_double_sources_globals p (selected_program_candidates chosen p) in
  if program_avoids_check globals p && private_pool_check (program_temps p) pool then
    ScopedSelectedRegion.transform_program chosen pool (reduction_double_progress_supported p)
      (select_memory_tiled_table table) p else p.
Theorem apply_selected_quotient_tiled_double_table_correct chosen pool table p :
  Forall (fun pair => ScopedPrivateRegion.projected_region_contract (program_temps p) (Clight.globalenv p)
    (quotient_tiled_double_sources_globals p (selected_program_candidates chosen p)) (fst pair) (snd pair)) table ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (apply_selected_quotient_tiled_double_table chosen pool table p)).
Proof.
  intro TABLE; unfold apply_selected_quotient_tiled_double_table.
  destruct (program_avoids_check _ p && private_pool_check (program_temps p) pool) eqn:PROFILE.
  - apply andb_true_iff in PROFILE as [GLOBAL PRIVATE].
    eapply ScopedSelectedRegionProof.transform_program_correct2 with (live:=program_temps p).
    + apply reduction_double_progress_supported_sound.
    + apply program_avoids_check_sound; exact GLOBAL.
    + apply select_quotient_tiled_double_table_sound; exact TABLE.
    + apply program_scope_computed.
    + apply private_pool_check_sound; exact PRIVATE.
  - apply unchanged_clight_simulation.
Qed.
Definition checked_selected_quotient_tiled_double_program chosen private_count phase adapt choices divisor p :=
  let live := program_temps p in
  let pool := propose_private_names live private_count in
  BIND table <- checked_quotient_tiled_double_regions p live pool phase adapt choices divisor (selected_program_candidates chosen p) -;
  pure (match table with [] => p | _ => apply_selected_quotient_tiled_double_table chosen pool table p end).
Theorem checked_selected_quotient_tiled_double_program_correct chosen private_count phase adapt choices divisor p target :
  mayReturn (checked_selected_quotient_tiled_double_program chosen private_count phase adapt choices divisor p) target ->
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 target).
Proof.
  unfold checked_selected_quotient_tiled_double_program; intro RUN; bind_imp_destruct RUN table TABLE.
  apply mayReturn_pure in RUN; subst target; destruct table as [|pair rest].
  - apply unchanged_clight_simulation.
  - apply apply_selected_quotient_tiled_double_table_correct.
    eapply checked_quotient_tiled_double_regions_sound; exact TABLE.
Qed.



Print Assumptions checked_selected_quotient_tiled_double_program_correct.
