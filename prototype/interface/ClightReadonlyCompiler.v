From Stdlib Require Import Bool.
From compcert.common Require Import Errors Events Smallstep Behaviors.
From compcert.cfrontend Require Import Clight ClightBigstep Csyntax Csem.
From compcert.x86 Require Import Asm.
From Guard Require Import ClightGuard ClightCondition CompCertMemoryEquivalence
  ClightRegionRewrite ClightRegionProgress AdaptiveRegionCompiler.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite.
Set Implicit Arguments.

(** This first whole-program adapter uses exact raw exits. It does not yet
    support ignoring private temporaries through the live-out frame relation.
    The user still supplies selection and a source-progress classifier. *)
Record readonly_clight_rule (source : Clight.statement) := ReadonlyClightRule {
  readonly_candidate : Clight.statement;
  readonly_guard : decision_tree;
  readonly_domain : clight_entry -> Prop;
  readonly_premise : clight_entry -> Prop;
  readonly_rule_check : forall temps,
    readonly_condition (readonly_clight_host (adapter_entry temps) (@eq fragment_observation))
      readonly_domain readonly_premise readonly_guard;
  readonly_rule_local : forall temps,
    conditional_equivalence (readonly_clight_host (adapter_entry temps) (@eq fragment_observation))
      readonly_domain readonly_premise source readonly_candidate;
  readonly_rule_entry : forall temps (p : Clight.program) e le m le' m',
    exec_stmt (adapter_entry temps) (Clight.globalenv p) e le m source E0 le' m' Out_normal ->
    readonly_domain (Entry (Clight.globalenv p) e le m)
}.

Definition readonly_replacement {source} (rule : readonly_clight_rule source) :=
  tree_statement (readonly_guard rule) (readonly_candidate rule) source.

Theorem readonly_rule_fragment_contract source (rule : readonly_clight_rule source) :
  guarded_fragment_contract source (readonly_guard rule) (readonly_candidate rule).
Proof.
  intros temps p e le m le' m' SOURCE.
  pose proof (readonly_rule_entry rule SOURCE) as DOMAIN.
  destruct (readonly_available (readonly_rule_check rule temps) _ DOMAIN) as
    [accepted [checked [CHECK SAME]]]; subst checked.
  exists accepted; split; [exact CHECK|]; intro ACCEPT.
  pose proof (readonly_sound (readonly_rule_check rule temps) _ _ _ DOMAIN (conj CHECK eq_refl)) as [_ PREMISE].
  assert (SOURCE_RUN : runs (readonly_clight_host (adapter_entry temps) (@eq fragment_observation))
    source (Entry (Clight.globalenv p) e le m) (FragmentObservation E0 le' m' Out_normal)).
  { exists (FragmentObservation E0 le' m' Out_normal); split; [exact SOURCE|reflexivity]. }
  apply (proj2 (@readonly_rule_local source rule temps (Entry (Clight.globalenv p) e le m)
    (FragmentObservation E0 le' m' Out_normal) (conj DOMAIN (PREMISE ACCEPT)))) in SOURCE_RUN.
  destruct SOURCE_RUN as [raw [RUN EQUAL]]; subst raw.
  exists m'; split; [exact RUN|apply memory_equivalent_refl].
Qed.

Theorem readonly_rule_region_contract source (rule : readonly_clight_rule source) :
  region_contract source (readonly_replacement rule).
Proof. apply guarded_fragment_region_contract, readonly_rule_fragment_contract. Qed.

Section USER_PASS.
Variable choose : forall source, option (readonly_clight_rule source).
Variable supported : Clight.statement -> bool.
Hypothesis SUPPORTED : forall source, supported source = true -> exists MODEL : region_progress source, True.

Definition readonly_selection source : option Clight.statement :=
  match choose source with Some rule => Some (readonly_replacement rule) | None => None end.

Lemma readonly_selection_sound source target :
  readonly_selection source = Some target -> region_contract source target.
Proof.
  unfold readonly_selection; destruct (choose source) as [rule|]; [|discriminate].
  intro SAME; injection SAME as SAME; subst target; apply readonly_rule_region_contract.
Qed.

Definition compile_readonly_rewrites (p : Csyntax.program) : res Asm.program :=
  compile_with_adaptive_regions supported (fun _ => None) (fun _ => None) readonly_selection p.

Theorem compile_readonly_rewrites_correct p target :
  compile_readonly_rewrites p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  unfold compile_readonly_rewrites; intro COMPILE.
  eapply compile_with_adaptive_regions_correct; [exact SUPPORTED| | | |exact COMPILE].
  - intros; discriminate.
  - apply readonly_selection_sound.
  - intros; discriminate.
Qed.
End USER_PASS.

Print Assumptions readonly_rule_fragment_contract.
Print Assumptions readonly_rule_region_contract.
Print Assumptions readonly_selection_sound.
Print Assumptions compile_readonly_rewrites_correct.
