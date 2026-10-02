From Stdlib Require Import List.
From compcert.lib Require Import Maps.
From compcert.common Require Import Values Memory Events Errors Smallstep.
From compcert.cfrontend Require Import Csem Clight ClightBigstep.
From polcert.src Require Import CState CInstr.
From Guard Require Import AbstractGuard SemanticFacts AbstractSchedule
  ClightGuard ClightCondition ClightPureExpr ClightDecisionRule
  ClightRegionRewrite ClightRegionRewriteProof ClightRegionRule
  ClightNoWrap ClightSignedCancel RegionCompiler CompCertMemoryEquivalence PolCertMemoryModel.
From GuardPolCert Require Import PolCertSchedule.
Set Implicit Arguments.

(** A language adapter separates decoding, conditional scheduling, and
    encoding. Its certificates refer to actual CInstr execution. The model
    environment may project the variables accessed by this fragment; this
    does not change the Clight environment or hide memory effects. *)
Module PolCertScheduleRegion (Names : C_INSTR_NAMES).
Module I := CInstr Names.
Module S := PolCertSchedule I.

Record schedule_bridge (source candidate : statement) := ScheduleBridge {
  bridge_domain : clight_entry -> Prop;
  bridge_assumption : clight_entry -> Prop;
  bridge_globalenv : Csem.genv;
  bridge_locals : clight_entry -> Csem.env;
  bridge_source : clight_entry -> list S.invocation;
  bridge_candidate : clight_entry -> list S.invocation;
  bridge_entry_domain : forall temps p e le m le' m',
    exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
    bridge_domain (Entry (globalenv p) e le m);
  bridge_decode : forall temps p e le m le' m',
    exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
    bridge_assumption (Entry (globalenv p) e le m) ->
    le' = le /\
    exists post,
      schedule_run S.model (bridge_source (Entry (globalenv p) e le m))
        (bridge_globalenv, bridge_locals (Entry (globalenv p) e le m), m) post /\
      concrete_memory_view bridge_globalenv (bridge_locals (Entry (globalenv p) e le m)) post m';
  bridge_encode : forall temps p e le m post,
    bridge_domain (Entry (globalenv p) e le m) ->
    bridge_assumption (Entry (globalenv p) e le m) ->
    schedule_run S.model (bridge_candidate (Entry (globalenv p) e le m))
      (bridge_globalenv, bridge_locals (Entry (globalenv p) e le m), m) post ->
    exists target_memory,
      exec_stmt (adapter_entry temps) (globalenv p) e le m candidate E0 le target_memory Out_normal /\
      concrete_memory_view bridge_globalenv (bridge_locals (Entry (globalenv p) e le m)) post target_memory
}.

Definition bridge_presumption {source candidate} (b : schedule_bridge source candidate) s :=
  bridge_assumption b s /\
  I.NonAlias (bridge_globalenv b, bridge_locals b s, entry_memory s) /\
  schedule_certificate S.model (bridge_source b s) (bridge_candidate b s).

Lemma memory_views_related ge locals first second first_memory second_memory :
  CState.eq first second -> concrete_memory_view ge locals first first_memory ->
  concrete_memory_view ge locals second second_memory ->
  memory_equivalent first_memory second_memory.
Proof.
  intros EQ FIRST SECOND.
  assert (REL : CState.eq (ge, locals, first_memory) (ge, locals, second_memory)).
  { eapply CState.eq_trans; [apply CState.eq_sym; exact FIRST |].
    eapply CState.eq_trans; [exact EQ | exact SECOND]. }
  exact (proj2 (proj2 REL)).
Qed.

Record schedule_region_package (source : statement) := ScheduleRegionPackage {
  package_candidate : statement;
  package_bridge : schedule_bridge source package_candidate;
  package_atoms : Type;
  package_dimension : property_dimension clight_entry package_atoms (bridge_domain package_bridge);
  package_primitives : check_primitives decision_test_language (bridge_domain package_bridge)
    (decide_atom package_dimension);
  package_formula : formula package_atoms;
  package_presumption : forall s, bridge_domain package_bridge s ->
    formula_property (atom_property package_dimension) package_formula s ->
    bridge_presumption package_bridge s
}.

Definition package_rule source (pkg : schedule_region_package source) :
  encoded_region_rule source (package_candidate pkg).
Proof.
  refine {| region_rule_atoms := package_atoms pkg;
            region_rule_domain := bridge_domain (package_bridge pkg);
            region_rule_dimension := package_dimension pkg;
            region_rule_primitives := package_primitives pkg;
            region_rule_formula := package_formula pkg |}.
  - intros temps p e le m le' m' SOURCE.
    exact (bridge_entry_domain (package_bridge pkg) SOURCE).
  - intros temps p e le m le' m' SOURCE PROPERTY.
    pose proof (bridge_entry_domain (package_bridge pkg) SOURCE) as DOMAIN.
    destruct (package_presumption pkg _ DOMAIN PROPERTY) as [ADAPTER [NONALIAS CERT]].
    destruct (bridge_decode (package_bridge pkg) SOURCE ADAPTER)
      as [TEMPS [post [RUN VIEW]]]. subst le'.
    destruct (@S.schedule_correct _ _ CERT _ _ NONALIAS RUN) as [candidate_post [CANDIDATE EQ]].
    destruct (@bridge_encode _ _ (package_bridge pkg) temps p e le m candidate_post DOMAIN ADAPTER CANDIDATE)
      as [target_memory [EXEC VIEW']].
    exists target_memory; split; [exact EXEC | exact (@memory_views_related _ _ _ _ _ _ EQ VIEW VIEW')].
Defined.

Definition select_schedule_region
  (propose : forall source, option (schedule_region_package source)) source : option statement :=
  match propose source with
  | Some pkg => Some (generated_region (package_rule pkg))
  | None => None
  end.

Theorem select_schedule_region_sound propose source target :
  select_schedule_region propose source = Some target -> region_contract source target.
Proof.
  unfold select_schedule_region; destruct (propose source); try discriminate.
  intro SELECT; inversion SELECT; subst; apply encoded_region_rule_sound.
Qed.

Theorem schedule_program_correct propose p :
  forward_simulation (semantics2 p)
    (semantics2 (ClightRegionRewrite.transform_program (select_schedule_region propose) p)).
Proof. apply ClightRegionRewriteProof.transform_program_correct2, select_schedule_region_sound. Qed.

Definition compile_schedule_regions propose :=
  compile_with_regions select_no_wrap select_signed_memory_rewrites (select_schedule_region propose).

Theorem compile_schedule_regions_correct propose p target :
  compile_schedule_regions propose p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  unfold compile_schedule_regions; apply compile_with_regions_correct.
  - exact select_no_wrap_sound.
  - exact (select_schedule_region_sound propose).
  - exact select_signed_memory_rewrites_sound.
Qed.

Goal True. idtac "GUARDCERT_SCHEDULE_REGION_BASELINE_BEGIN". exact Logic.I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "GUARDCERT_SCHEDULE_REGION_ADAPTER_BEGIN". exact Logic.I. Qed.
Print Assumptions package_rule.
Print Assumptions schedule_program_correct.
Print Assumptions compile_schedule_regions_correct.
Goal True. idtac "GUARDCERT_SCHEDULE_REGION_ASSUMPTIONS_END". exact Logic.I. Qed.
End PolCertScheduleRegion.
