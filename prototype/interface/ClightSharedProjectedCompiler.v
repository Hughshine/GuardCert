From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Csyntax Csem Cstrategy SimplExpr SimplExprproof SimplLocals
  SimplLocalsproof Clight ClightBigstep.
From compcert.driver Require Import Compiler Complements.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightGuard ClightCondition ClightRegionProgress ClightRegionRewrite ClightTempFrame
  ClightTempFootprint ClightProjectedExecution ClightPrivateRegion ClightPrivatePool CompCertMemoryEquivalence GuardCompiler.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite ClightRegionBoundary
  ClightReadonlyProjectedCompiler ClightReadonlyRuleEmbedding ClightSharedGuard ClightGuardRealization.
Import ListNotations.
Set Implicit Arguments.

Lemma shared_projected_selected live source (rule : readonly_projected_clight_rule live source)
  temps p locals target memory source_exit final :
  exec_stmt (adapter_entry temps) (Clight.globalenv p) locals target memory source E0 source_exit final Out_normal ->
  exists accepted target_exit target_memory,
    decision_run (Entry (Clight.globalenv p) locals target memory) (projected_guard rule) accepted /\
    exec_stmt (adapter_entry temps) (Clight.globalenv p) locals target memory
      (if accepted then projected_candidate rule else source) E0 target_exit target_memory Out_normal /\
    temp_agree live source_exit target_exit /\ memory_equivalent final target_memory.
Proof. apply projected_rule_selected. Qed.

Definition shared_projected_replacement live source (rule : readonly_projected_clight_rule live source) result :=
  shared_guard_statement (projected_guard rule) result (projected_candidate rule) source.

Theorem shared_projected_region_contract live source (rule : readonly_projected_clight_rule live source) result :
  quiet_statement (projected_candidate rule) = true ->
  ~ In result (statement_temps source ++ statement_temps (projected_candidate rule) ++ live) ->
  PrivateRegion.projected_region_contract live source (shared_projected_replacement rule result).
Proof.
  intros QUIET FRESH.
  assert (PRIVATE : ~ In result (statement_temps (projected_candidate rule) ++ statement_temps source ++ live)).
  { repeat rewrite in_app_iff in *; tauto. }
  exact (@projected_realized_rule_region_contract live source rule
    (@shared_normal_realization live (projected_guard rule) (projected_candidate rule) source result
      (statement_temps (projected_candidate rule)) (projected_source_writes rule)
      (quiet_source_write_bound _ QUIET) (projected_source_write_bound rule) PRIVATE)).
Qed.

Section USER_PASS.
Variable choose : forall (live : list ident) (pool : list (ident * type)) source,
  option (readonly_projected_clight_rule live source).
Variable supported : statement -> bool.
Hypothesis SUPPORTED : forall source, supported source = true -> exists MODEL : region_progress source, True.
Variable private_count : nat.

(** One slot belongs to the lowering; the remaining slots are supplied to
    the original user selector. The abstract condition certificate is reused. *)
Definition shared_projected_selection (live : list ident) (pool : list (ident * type)) (source : statement) : option statement.
Proof.
  destruct pool as [|[result ty] rest]; [exact None|].
  destruct (choose live rest source) as [rule|]; [|exact None].
  destruct (Bool.bool_dec (quiet_statement (projected_candidate rule)) true) as [QUIET|]; [|exact None].
  destruct (in_dec peq result (statement_temps source ++ statement_temps (projected_candidate rule) ++ live))
    as [|FRESH]; [exact None|].
  exact (Some (shared_projected_replacement rule result)).
Defined.

Theorem shared_projected_selection_sound live pool source target :
  shared_projected_selection live pool source = Some target -> PrivateRegion.projected_region_contract live source target.
Proof.
  unfold shared_projected_selection; destruct pool as [|[result ty] rest]; try discriminate.
  destruct (choose live rest source) as [rule|]; try discriminate.
  destruct (Bool.bool_dec (quiet_statement (projected_candidate rule)) true) as [QUIET|]; try discriminate.
  destruct (in_dec peq result (statement_temps source ++ statement_temps (projected_candidate rule) ++ live))
    as [|FRESH]; try discriminate.
  intro SAME; injection SAME as SAME; subst target; apply shared_projected_region_contract; assumption.
Qed.

Definition transform_shared_projected (p : Clight.program) :=
  transform_private_program supported shared_projected_selection (propose_private_names (program_temps p) private_count) p.
Theorem transform_shared_projected_correct p :
  forward_simulation (Clight.semantics2 p) (Clight.semantics2 (transform_shared_projected p)).
Proof. apply transform_private_program_correct; [exact SUPPORTED|apply shared_projected_selection_sound]. Qed.

Definition compile_shared_projected (p : Csyntax.program) : res Asm.program :=
  match SimplExpr.transl_program p with
  | Error err => Error err
  | OK p1 => match SimplLocals.transf_program p1 with
    | Error err => Error err
    | OK p2 => compile_clight_tail (Compiler.print Compiler.print_Clight (transform_shared_projected p2)) end end.

Theorem shared_projected_cstrategy_forward p target : compile_shared_projected p = OK target ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics target).
Proof.
  unfold compile_shared_projected; intro COMPILE.
  destruct (SimplExpr.transl_program p) as [p1|err] eqn:P1; try discriminate.
  destruct (SimplLocals.transf_program p1) as [p2|err] eqn:P2; try discriminate.
  rewrite Compiler.print_identity in COMPILE.
  eapply compose_forward_simulations.
  { eapply SimplExprproof.transl_program_correct; eauto using SimplExprproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply SimplLocalsproof.transf_program_correct; eauto using SimplLocalsproof.match_transf_program. }
  eapply compose_forward_simulations.
  { apply transform_shared_projected_correct. }
  eapply clight_tail_correct; exact COMPILE.
Qed.

Theorem compile_shared_projected_correct p target : compile_shared_projected p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  intro COMPILE; apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  - eapply sd_traces; eapply Asm.semantics_determinate.
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * eapply shared_projected_cstrategy_forward; exact COMPILE.
      * eapply sd_traces; eapply Asm.semantics_determinate.
    + apply atomic_receptive; apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
Qed.
End USER_PASS.

Print Assumptions shared_projected_selected.
Print Assumptions shared_projected_region_contract.
Print Assumptions shared_projected_selection_sound.
Print Assumptions transform_shared_projected_correct.
Print Assumptions compile_shared_projected_correct.
