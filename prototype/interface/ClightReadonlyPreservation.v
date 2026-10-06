From Stdlib Require Import List.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition
  ClightPrivateRule ClightPrivateRegion ClightTempFrame ClightTempFootprint
  CompCertMemoryEquivalence.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyLoadedTreeSynthesis ClightRegionBoundary ClightGuardRealization
  ClightReadonlyProjectedCompiler.
Set Implicit Arguments.

(** A compiler may consume source-to-candidate preservation without requiring
    equivalence on arbitrary global environments. The language host determines
    the simulation direction; this interface does not rename it equivalence. *)
Record readonly_preserving_clight_rule (live : list ident) (source : statement) := {
  preserving_candidate : statement;
  preserving_guard : decision_tree;
  preserving_domain : clight_entry -> Prop;
  preserving_premise : clight_entry -> Prop;
  preserving_writes : list ident;
  preserving_source_writes : writes_only preserving_writes source;
  preserving_check : forall temps,
    readonly_condition (readonly_clight_host (adapter_entry temps) (boundary_observe (public_exit_ports live)))
      preserving_domain preserving_premise preserving_guard;
  preserving_local : forall temps (p : Clight.program) locals le memory after final,
    statement_scope live source ->
    exec_stmt (adapter_entry temps) (Clight.globalenv p) locals le memory source E0 after final Out_normal ->
    preserving_domain (Entry (Clight.globalenv p) locals le memory) ->
    preserving_premise (Entry (Clight.globalenv p) locals le memory) ->
    exists exit mem,
      exec_stmt (adapter_entry temps) (Clight.globalenv p) locals le memory
        preserving_candidate E0 exit mem Out_normal /\
      temp_agree live after exit /\ memory_equivalent final mem;
  preserving_entry : forall temps (p : Clight.program) locals le memory after final,
    exec_stmt (adapter_entry temps) (Clight.globalenv p) locals le memory source E0 after final Out_normal ->
    preserving_domain (Entry (Clight.globalenv p) locals le memory)
}.

Theorem preserving_rule_selected live source (rule : readonly_preserving_clight_rule live source)
  temps p locals le memory after final :
  statement_scope live source ->
  exec_stmt (adapter_entry temps) (Clight.globalenv p) locals le memory source E0 after final Out_normal ->
  projected_selected_execution live (preserving_guard rule) (preserving_candidate rule) source
    temps p locals le memory after final.
Proof.
  intros SCOPE SOURCE; pose proof (preserving_entry rule SOURCE) as DOMAIN.
  destruct (readonly_available (preserving_check rule temps) _ DOMAIN)
    as [accepted [checked [CHECK SAME]]]; subst checked.
  exists accepted; destruct accepted.
  - destruct (readonly_sound (preserving_check rule temps) _ _ _ DOMAIN (conj CHECK eq_refl)) as [_ PREMISE].
    destruct (preserving_local rule SCOPE SOURCE DOMAIN (PREMISE eq_refl))
      as [exit [mem [RUN [PUBLIC MEMORY]]]].
    exists exit, mem; split; [exact CHECK|split; [exact RUN|split; assumption]].
  - exists after, final; split; [exact CHECK|split; [exact SOURCE|split;
      [apply temp_agree_refl|apply memory_equivalent_refl]]].
Qed.

Theorem preserving_realized_region_contract live source (rule : readonly_preserving_clight_rule live source)
  (R : clight_normal_realization live (preserving_guard rule) (preserving_candidate rule) source) :
  PrivateRegion.projected_region_contract live source (realization_code (normal_realization R)).
Proof.
  eapply realized_projected_selection_contract; [exact (preserving_source_writes rule)|].
  intros; apply preserving_rule_selected; assumption.
Qed.

(** This bridge retains the legacy candidate/model certificate and generates
    the same logical tree, now with a readonly safety certificate. No candidate
    checker or alias/overflow theorem is bypassed by the conversion. *)
Definition encoded_private_as_preserving live source candidate
  (rule : encoded_private_rule live source candidate) : readonly_preserving_clight_rule live source.
Proof.
  refine {| preserving_candidate := candidate;
    preserving_guard := generated_private_tree rule;
    preserving_domain := private_rule_domain rule;
    preserving_premise := fun entry => formula_property (atom_property (private_rule_dimension rule))
      (private_rule_formula rule) entry;
    preserving_writes := private_rule_writes rule;
    preserving_source_writes := private_rule_source_writes rule |}.
  - intro temps; apply synthesized_loaded_tree_condition.
  - intros temps p locals le memory after final SCOPE SOURCE DOMAIN PREMISE.
    exact (private_rule_local rule SCOPE SOURCE PREMISE).
  - exact (private_rule_entry rule).
Defined.

Print Assumptions preserving_rule_selected.
Print Assumptions preserving_realized_region_contract.
Print Assumptions encoded_private_as_preserving.
