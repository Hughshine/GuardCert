From Stdlib Require Import Bool.
From compcert.common Require Import Errors Smallstep.
From compcert.cfrontend Require Import Clight Csyntax Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import AbstractGuard ClightGuard ClightCondition ClightSyntaxEquality
  ClightProgressClassifier.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightPreloadExample ClightPreloadSynthesis ClightReadonlyCompiler.
From GuardInterface Require Import ClightAdministrative.
Set Implicit Arguments.

Definition preload_branch_rule count pointer body :
  readonly_clight_rule (tree_statement (lazy_preload_tree count pointer) body Clight.Sskip).
Proof.
  refine {| readonly_candidate := body;
    readonly_guard := synthesize_tree (preload_primitives count pointer) (Fact tt);
    readonly_domain := preload_domain count pointer;
    readonly_premise := preload_premise count pointer |}.
  - intro temps; exact (synthesized_preload_condition (adapter_entry temps) (@eq fragment_observation)
      count pointer (Fact tt)).
  - intro temps; apply preload_branch_conditional_equivalence.
  - intros temps p e le m le' m' RUN.
    exact (@preload_domain_from_source_execution (adapter_entry temps) count pointer body
      (Entry (Clight.globalenv p) e le m)
      (FragmentObservation Events.E0 le' m' ClightBigstep.Out_normal) RUN).
Defined.

(** A minimal user pass: propose the two-test pattern, then check the entire
    actual syntax (including types). Only matched fragments obtain a rule.
    The generic compiler separately filters progress and target labels. *)
Definition choose_preload_normalized (source : Clight.statement) : option (readonly_clight_rule source).
Proof.
  refine (match source as s return option (readonly_clight_rule s) with
  | Clight.Sifthenelse (Clight.Etempvar count count_type)
      (Clight.Sifthenelse (Clight.Ederef (Clight.Etempvar pointer pointer_type) load_type) body no_inner) no => _
  | _ => None end).
  set (actual := Clight.Sifthenelse (Clight.Etempvar count count_type)
    (Clight.Sifthenelse (Clight.Ederef (Clight.Etempvar pointer pointer_type) load_type) body no_inner) no).
  change (option (readonly_clight_rule actual)).
  destruct (statement_eq actual (tree_statement (lazy_preload_tree count pointer) body Clight.Sskip))
    as [SAME|DIFFERENT]; [|exact None].
  rewrite SAME; exact (Some (preload_branch_rule count pointer body)).
Defined.

Definition trim_readonly_rule source (rule : readonly_clight_rule (trim_skips source)) :
  readonly_clight_rule source.
Proof.
  refine {| readonly_candidate := readonly_candidate rule; readonly_guard := readonly_guard rule;
    readonly_domain := readonly_domain rule; readonly_premise := readonly_premise rule;
    readonly_rule_check := readonly_rule_check rule |}.
  - intros temps entry observed PROPERTIES.
    exact (iff_trans (@readonly_rule_local (trim_skips source) rule temps entry observed PROPERTIES)
      (trim_skips_runs (adapter_entry temps) (@eq fragment_observation) source entry observed)).
  - intros temps p e le m le' m' RUN.
    eapply (@readonly_rule_entry (trim_skips source) rule temps p e le m le' m').
    apply (proj2 (trim_skips_equivalent (adapter_entry temps) source _ _ _ _ _ _ _ _)); exact RUN.
Defined.

Definition choose_preload_rewrite source : option (readonly_clight_rule source) :=
  match choose_preload_normalized (trim_skips source) with
  | Some rule => Some (trim_readonly_rule source rule)
  | None => None
  end.

Definition compile_preload_rewrites :=
  compile_readonly_rewrites choose_preload_rewrite progress_supported.

Theorem compile_preload_rewrites_correct p target :
  compile_preload_rewrites p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_readonly_rewrites_correct, progress_supported_sound. Qed.

Print Assumptions preload_branch_rule.
Print Assumptions choose_preload_rewrite.
Print Assumptions trim_readonly_rule.
Print Assumptions compile_preload_rewrites_correct.
