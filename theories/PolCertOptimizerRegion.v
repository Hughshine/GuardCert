From Stdlib Require Import Bool.
From compcert.common Require Import Values Memory Events Errors Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep Csem.
From compcert.driver Require Import Compiler.
From Guard Require Import AbstractGuard SemanticFacts EndpointBridge ClightGuard
  ClightCondition ClightPureExpr ClightDecisionRule ClightRegionRule ClightRegionRewrite ClightSyntaxEquality
  CompCertMemoryEquivalence ClightRegionProgress ClightAdaptiveRegion
  ClightFrontendRegion AdaptiveRegionCompiler ClightNoWrap ClightSignedCancel.
From polcert.polygen Require Import PolIRs.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.driver Require Import PolOptCorrect.
From Vpl Require Import Impure.
Import Clight.
Set Implicit Arguments.

(** An optimizer result alone gives a backward endpoint. This adapter records
    the language properties needed to convert it to a forward local rule.
    These are certificate fields, not new global axioms. No concrete loop
    decoder or native optimizer driver is asserted by this interface. *)
Module PolCertOptimizerRegion (P : POLIRS) (Core : POL_OPT_CORE P).
Module Endpoint := PolOptCorrect P Core.
Module L := P.Loop.
Module State := P.State.

Record optimizer_loop_bridge (source : statement) (original optimized : L.t) := OptimizerLoopBridge {
  optimizer_candidate : statement;
  optimizer_source_progress : region_progress source;
  optimizer_domain : clight_entry -> Prop;
  optimizer_premise : clight_entry -> Prop;
  optimizer_initial : clight_entry -> State.t;
  optimizer_view : clight_entry -> State.t -> mem -> Prop;
  optimizer_atoms : Type;
  optimizer_dimension : property_dimension clight_entry optimizer_atoms optimizer_domain;
  optimizer_checks : check_primitives decision_test_language optimizer_domain
    (decide_atom optimizer_dimension);
  optimizer_formula : formula optimizer_atoms;
  optimizer_formula_premise : forall s, optimizer_domain s ->
    formula_property (atom_property optimizer_dimension) optimizer_formula s -> optimizer_premise s;
  optimizer_entry_domain : forall temps p e le m le' m',
    exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
    optimizer_domain (Entry (globalenv p) e le m);
  optimizer_decode : forall temps p e le m le' m',
    exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
    optimizer_premise (Entry (globalenv p) e le m) ->
    exists result, L.semantics original (optimizer_initial (Entry (globalenv p) e le m)) result /\
      optimizer_view (Entry (globalenv p) e le m) result m';
  optimizer_source_unique : forall s first second,
    optimizer_domain s -> optimizer_premise s ->
    L.semantics original (optimizer_initial s) first ->
    L.semantics original (optimizer_initial s) second -> State.eq first second;
  optimizer_candidate_progress : forall s result,
    optimizer_domain s -> optimizer_premise s ->
    L.semantics original (optimizer_initial s) result ->
    exists target, L.semantics optimized (optimizer_initial s) target;
  optimizer_encode : forall temps p e le m le' m' result,
    exec_stmt (adapter_entry temps) (globalenv p) e le m source E0 le' m' Out_normal ->
    optimizer_domain (Entry (globalenv p) e le m) -> optimizer_premise (Entry (globalenv p) e le m) ->
    L.semantics optimized (optimizer_initial (Entry (globalenv p) e le m)) result ->
    exists target_memory,
      exec_stmt (adapter_entry temps) (globalenv p) e le m optimizer_candidate E0 le' target_memory Out_normal /\
      optimizer_view (Entry (globalenv p) e le m) result target_memory;
  optimizer_view_related : forall s first second first_memory second_memory,
    State.eq first second -> optimizer_view s first first_memory -> optimizer_view s second second_memory ->
    memory_equivalent first_memory second_memory
}.

Definition optimizer_loop_language source original optimized
  (b : optimizer_loop_bridge source original optimized) : language clight_entry.
Proof.
  refine {| command := L.t; test := bool; observation := State.t;
    command_run := fun c s result => L.semantics c (optimizer_initial b s) result;
    test_run := fun t _ flag => flag = t;
    conditional := fun t yes no => if t then yes else no |}.
  intros t yes no s result; split.
  - intro RUN; exists t; auto.
  - intros [flag [EQ RUN]]; subst flag; exact RUN.
Defined.

Theorem optimized_loop_preservation source original optimized
  (b : optimizer_loop_bridge source original optimized) :
  mayReturn (Core.Opt_prepared original) optimized ->
  conditional_preservation (optimizer_loop_language b)
    (optimizer_domain b) (optimizer_premise b) State.eq original optimized.
Proof.
  intro OPT; apply endpoint_refinement_to_preservation.
  - exact State.eq_sym.
  - exact State.eq_trans.
  - exact (optimizer_source_unique b).
  - exact (optimizer_candidate_progress b).
  - intros s result DOMAIN PREMISE RUN.
    exact (Endpoint.Opt_prepared_correct original (optimizer_initial b s) result optimized OPT RUN).
Qed.

Definition actual_optimizer_region_rule source original optimized
  (b : optimizer_loop_bridge source original optimized)
  (OPT : mayReturn (Core.Opt_prepared original) optimized) :
  encoded_region_rule source (optimizer_candidate b).
Proof.
  refine {| region_rule_atoms := optimizer_atoms b;
    region_rule_domain := optimizer_domain b;
    region_rule_dimension := optimizer_dimension b;
    region_rule_primitives := optimizer_checks b;
    region_rule_formula := optimizer_formula b |}.
  - exact (optimizer_entry_domain b).
  - intros temps p e le m le' m' SOURCE PROPERTY.
    pose proof (optimizer_entry_domain b SOURCE) as DOMAIN.
    pose proof (optimizer_formula_premise b _ DOMAIN PROPERTY) as PREMISE.
    destruct (optimizer_decode b SOURCE PREMISE) as [original_result [RUN VIEW]].
    destruct (@optimized_loop_preservation source original optimized b OPT
      (Entry (globalenv p) e le m) original_result DOMAIN PREMISE RUN)
      as [candidate_result [CANDIDATE EQ]].
    destruct (optimizer_encode b SOURCE DOMAIN PREMISE CANDIDATE)
      as [target_memory [EXEC VIEW']].
    exists target_memory; split; [exact EXEC |].
    exact (@optimizer_view_related source original optimized b (Entry (globalenv p) e le m)
      original_result candidate_result m' target_memory EQ VIEW VIEW').
Defined.

Theorem actual_optimizer_region_contract source original optimized
  (b : optimizer_loop_bridge source original optimized)
  (OPT : mayReturn (Core.Opt_prepared original) optimized) :
  region_contract source (generated_region (actual_optimizer_region_rule b OPT)).
Proof. apply encoded_region_rule_sound. Qed.

Definition optimizer_supported source original optimized
  (b : optimizer_loop_bridge source original optimized) code : bool :=
  if statement_eq code source then true else frontend_progress_supported code.

Lemma optimizer_supported_sound source original optimized
  (b : optimizer_loop_bridge source original optimized) code : optimizer_supported b code = true ->
  exists MODEL : region_progress code, True.
Proof.
  unfold optimizer_supported; destruct (statement_eq code source) as [EQ|NE].
  - intros _; subst code. exists (optimizer_source_progress b); exact I.
  - apply frontend_progress_supported_sound.
Qed.

Definition select_optimizer_region source original optimized
  (b : optimizer_loop_bridge source original optimized)
  (OPT : mayReturn (Core.Opt_prepared original) optimized) code : option statement :=
  if statement_eq code source
  then Some (generated_region (actual_optimizer_region_rule b OPT))
  else select_progress_regions code.

Lemma optimizer_source_is_selected source original optimized
  (b : optimizer_loop_bridge source original optimized)
  (OPT : mayReturn (Core.Opt_prepared original) optimized) :
  select_optimizer_region b OPT source = Some (generated_region (actual_optimizer_region_rule b OPT)).
Proof.
  unfold select_optimizer_region; destruct (statement_eq source source) as [EQ|NE];
    [reflexivity | contradiction].
Qed.

Lemma select_optimizer_region_sound source original optimized
  (b : optimizer_loop_bridge source original optimized)
  (OPT : mayReturn (Core.Opt_prepared original) optimized) code target :
  select_optimizer_region b OPT code = Some target -> region_contract code target.
Proof.
  unfold select_optimizer_region; destruct (statement_eq code source) as [EQ|NE].
  - intro TARGET; inversion TARGET; subst. apply actual_optimizer_region_contract.
  - apply select_progress_regions_sound.
Qed.

(** A proved construction consuming the actual optimizer's successful-result
    evidence. It does not run the impure optimizer in the native C driver. *)
Definition compile_optimizer_result source original optimized
  (b : optimizer_loop_bridge source original optimized)
  (OPT : mayReturn (Core.Opt_prepared original) optimized) :=
  compile_with_adaptive_regions (optimizer_supported b) select_no_wrap select_signed_memory_rewrites
    (select_optimizer_region b OPT).

Theorem compile_optimizer_result_correct source original optimized
  (b : optimizer_loop_bridge source original optimized)
  (OPT : mayReturn (Core.Opt_prepared original) optimized) p target :
  compile_optimizer_result b OPT p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  unfold compile_optimizer_result; apply compile_with_adaptive_regions_correct.
  - exact (optimizer_supported_sound b).
  - exact select_no_wrap_sound.
  - exact (select_optimizer_region_sound b OPT).
  - exact select_signed_memory_rewrites_sound.
Qed.

Goal True. idtac "GUARDCERT_OPT_REGION_OPTIMIZER_BASELINE_BEGIN". exact I. Qed.
Print Assumptions Endpoint.Opt_prepared_correct.
Goal True. idtac "GUARDCERT_OPT_REGION_COMPCERT_BASELINE_BEGIN". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "GUARDCERT_OPT_REGION_ADAPTER_BEGIN". exact I. Qed.
Print Assumptions compile_optimizer_result_correct.
Goal True. idtac "GUARDCERT_OPT_REGION_ASSUMPTIONS_END". exact I. Qed.
End PolCertOptimizerRegion.
