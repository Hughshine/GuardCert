From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightStraightLine ClightTempFrame ClightTempFootprint
  ClightPrivateRegion ClightProjectedExecution ClightMemorySteps CompCertMemoryEquivalence ClightRegionProgress.
From GuardInterface Require Import ClightDualLoadedUnitSyntax ClightReadonlyRuleEmbedding.
Import ListNotations.
Set Implicit Arguments.

(** Sequence association and empty statements are frontend representation
    choices. Transport the actual source execution and its public scope. *)
Lemma flatten_region_temps source :
  flat_map statement_temps (flatten_region source) = statement_temps source.
Proof.
  induction source; cbn [flatten_region statement_temps flat_map]; try rewrite app_nil_r; try reflexivity.
  rewrite flat_map_app, IHsource1, IHsource2; reflexivity.
Qed.

Theorem flattened_projected_region_contract live actual canonical target :
  flatten_region actual = flatten_region canonical ->
  PrivateRegion.projected_region_contract live canonical target ->
  PrivateRegion.projected_region_contract live actual target.
Proof.
  intros FLAT CONTRACT temps p locals entry current memory after final SCOPE AGREE RUN fn continuation.
  apply CONTRACT with (le:=entry) (le':=after) (m':=final).
  - unfold statement_scope in *; rewrite <- (flatten_region_temps canonical), <- FLAT,
      flatten_region_temps; exact SCOPE.
  - exact AGREE.
  - apply flatten_region_encode; rewrite <- FLAT; apply flatten_region_execution; exact RUN.
Qed.

(** Retain a quiet source suffix, including its real memory writes. Public
    temporary agreement and memory equivalence transport its execution after
    a checked replacement; neither exact scratch values nor memory equality
    are required. Calls, returns and labels remain outside this finite host. *)
Theorem projected_region_quiet_suffix live source target suffix :
  quiet_statement suffix = true ->
  PrivateRegion.projected_region_contract live source target ->
  PrivateRegion.projected_region_contract live (Ssequence source suffix) (Ssequence target suffix).
Proof.
  intros QUIET CONTRACT temps p locals entry current memory after final SCOPE AGREE RUN fn continuation.
  inversion RUN; subst; [|contradiction].
  match goal with EMPTY : _ ** _ = E0 |- _ =>
    apply Eapp_E0_inv in EMPTY as [LEFT RIGHT]; subst end.
  assert (SOURCE_SCOPE : statement_scope live source).
  { unfold statement_scope in *; eapply scope_append_left; exact SCOPE. }
  assert (SUFFIX_SCOPE : statement_scope live suffix).
  { unfold statement_scope in *; eapply scope_append_right; exact SCOPE. }
  match goal with BODY : exec_stmt _ _ _ _ _ source _ _ _ _ |- _ =>
    destruct (CONTRACT _ _ _ _ _ _ _ _ SOURCE_SCOPE AGREE BODY fn (Kseq suffix continuation))
      as [middle [mem [BODY_STEPS [PUBLIC MEMORY]]]] end.
  match goal with TAIL : exec_stmt _ _ _ _ _ suffix _ _ _ _ |- _ =>
    destruct (@structured_execution_temp_transport (adapter_entry temps) (globalenv p) locals _ _
      suffix E0 after final Out_normal TAIL live middle (statement_temps suffix)
      (@quiet_source_write_bound suffix QUIET) SUFFIX_SCOPE PUBLIC) as [exit [SUFFIX EXIT]] end.
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ SUFFIX fn continuation)
    as [finish [SUFFIX_STEPS FINISH]]; inversion FINISH; subst finish.
  destruct (@star_memory_transport temps (globalenv p) _ E0 _ SUFFIX_STEPS
    (State fn suffix continuation locals middle mem) (memory_state _ _ _ _ _ _ _ MEMORY))
    as [finish [TRANSPORTED RESULT]]; inversion RESULT; subst finish.
  eexists; eexists; split; [|split; eassumption].
  eapply star_left with (t1:=E0) (t2:=E0).
  - unfold adapter_step; apply step_seq.
  - eapply star_trans with (t1:=E0) (t2:=E0); [exact BODY_STEPS| |reflexivity].
    eapply star_left with (t1:=E0) (t2:=E0).
    + unfold adapter_step; apply step_skip_seq.
    + exact TRANSPORTED.
    + reflexivity.
  - reflexivity.
Qed.

Print Assumptions flattened_projected_region_contract.
Print Assumptions projected_region_quiet_suffix.
