From Stdlib Require Import List ZArith.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint
  ClightPrivateRegion ClightStraightLine ClightCountedLoop ClightFrontendLoopProtocol ClightLoopSyntax ClightProjectedExecution CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryPointerSequence GuardMemoryParametricSourceClight GuardMemoryParametricWidth
  GuardMemoryAffineSourceExpressions GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightSourceObservation
  ClightAffinePointerGuard ClightAffineInnerPointerSourceGuard ClightAffineInnerPointerCandidateGuard ClightAffineInnerPointerCandidate.
Import ListNotations.
Set Implicit Arguments.

Definition affine_inner_pointer_package_candidate_guard source (package : memory_affine_inner_pointer_package source)
  live (candidate : affine_inner_pointer_candidate_package package live) width_tree alias_tree :=
  affine_inner_pointer_candidate_guard_tree package width_tree alias_tree
    (affine_inner_candidate_validator_bounds candidate) (affine_inner_candidate_encoder_bounds candidate).
Definition affine_inner_pointer_guarded_candidate source (package : memory_affine_inner_pointer_package source)
  live (candidate : affine_inner_pointer_candidate_package package live) width_tree alias_tree :=
  tree_statement (affine_inner_pointer_package_candidate_guard candidate width_tree alias_tree)
    (affine_inner_pointer_candidate_statement candidate) source.

Theorem affine_inner_pointer_source_writes source (package : memory_affine_inner_pointer_package source) :
  writes_only [affine_inner_pointer_row (affine_inner_pointer_shape package);
    affine_inner_pointer_inner_bound (affine_inner_pointer_shape package);
    affine_inner_pointer_column (affine_inner_pointer_shape package)] source.
Proof.
  rewrite (affine_inner_pointer_source_exact (affine_inner_pointer_syntax package)).
  assert (OUTER : writes_only [affine_inner_pointer_inner_bound (affine_inner_pointer_shape package);
    affine_inner_pointer_column (affine_inner_pointer_shape package)]
    (affine_inner_pointer_outer_body (affine_inner_pointer_shape package))).
  { eapply memory_parametric_outer_writes;
      [eapply memory_pointer_sequence_writes; exact (affine_inner_pointer_body_exact (affine_inner_pointer_syntax package))|
       exact (affine_inner_pointer_outer_exact (affine_inner_pointer_syntax package))]. }
  unfold memory_affine_inner_pointer_source,frontend_counted_loop,counter_increment.
  repeat constructor; try (cbn; auto).
  eapply writes_only_weaken; [|exact OUTER]; cbn; tauto.
Qed.

Section PRESERVATION.
Variable source : statement.
Variable package : memory_affine_inner_pointer_package source.
Variable live : list ident.
Variable candidate : affine_inner_pointer_candidate_package package live.
Variable width_tree alias_tree : decision_tree.
Hypothesis WIDTH : compile_memory_source_width (affine_inner_pointer_column_limit package)
  (affine_inner_pointer_row (affine_inner_pointer_shape package))
  (memory_affine_inner_pointer_header (affine_inner_pointer_shape package) (affine_inner_pointer_expression package))
  (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit package) (affine_inner_pointer_header_limits package))
  (affine_inner_pointer_expression package) = Some width_tree.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes package = Some alias_tree.

(** Finite local preservation consumes the independent candidate certificate.
    Refusal executes the original loop. The observed entry fact is supplied
    by placement, not inferred from the loop or the optimizer's presumption. *)
Theorem affine_inner_pointer_guarded_candidate_execution fe ge locals temps memory after final :
  observed_pointer_domain (affine_inner_pointer_pointers package) (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals temps memory (affine_inner_pointer_guarded_candidate candidate width_tree alias_tree)
    E0 target final Out_normal /\ temp_agree live after target.
Proof.
  intros OBSERVED SOURCE.
  assert (DOMAIN : affine_inner_pointer_observed_completed package fe (Entry ge locals temps memory)).
  { split; [exists after,final; rewrite <- (affine_inner_pointer_source_exact (affine_inner_pointer_syntax package)); exact SOURCE|exact OBSERVED]. }
  pose proof (@affine_inner_pointer_candidate_guard_condition source package fe fragment_observation (@eq fragment_observation)
    width_tree alias_tree (affine_inner_candidate_validator_bounds candidate) (affine_inner_candidate_encoder_bounds candidate)
    WIDTH ALIAS) as CHECK.
  destruct (readonly_available CHECK _ DOMAIN) as [accepted [checked [RUN SAME]]]; subst checked.
  unfold affine_inner_pointer_guarded_candidate,affine_inner_pointer_package_candidate_guard.
  destruct accepted.
  - destruct (readonly_sound CHECK _ _ _ DOMAIN (conj RUN eq_refl)) as [_ SOUND].
    destruct (SOUND eq_refl) as [[READY NONALIAS] RANGES].
    destruct (@affine_inner_pointer_candidate_execution source package live candidate fe ge locals temps memory after final
      READY NONALIAS RANGES SOURCE) as [target [CANDIDATE PUBLIC]].
    exists target; split; [|exact PUBLIC].
    eapply decision_fragment_run with (b:=true); [exact RUN|exact CANDIDATE].
  - exists after; split; [|apply temp_agree_refl].
    eapply decision_fragment_run with (b:=false); [exact RUN|exact SOURCE].
Qed.

Definition affine_inner_pointer_observed_candidate loads :=
  Ssequence (source_load_prefix loads) (affine_inner_pointer_guarded_candidate candidate width_tree alias_tree).

(** C_host finite fragment contract: the established prefix service handles
    source scope, incoming public temps, retained reads and full memory. This
    theorem still needs a source-progress/placement checker for program use. *)
Theorem affine_inner_pointer_observed_candidate_contract loads :
  source_observations_check (affine_inner_pointer_pointers package) loads = true ->
  PrivateRegion.projected_region_contract live (Ssequence (source_load_prefix loads) source)
    (affine_inner_pointer_observed_candidate loads).
Proof.
  intro CHECK; destruct (@source_observations_check_sound (affine_inner_pointer_pointers package) loads CHECK) as [COVER FRESH].
  unfold affine_inner_pointer_observed_candidate.
  apply source_prefix_region_contract with
    (writes:=source_load_targets loads++[affine_inner_pointer_row (affine_inner_pointer_shape package);
      affine_inner_pointer_inner_bound (affine_inner_pointer_shape package);affine_inner_pointer_column (affine_inner_pointer_shape package)])
    (domain:=observed_pointer_domain (affine_inner_pointer_pointers package)).
  - apply source_load_prefix_supported.
  - constructor.
    + eapply writes_only_weaken; [intros identifier MEMBER; apply in_or_app; left; exact MEMBER|apply source_load_prefix_writes].
    + eapply writes_only_weaken; [intros identifier MEMBER; apply in_or_app; right; exact MEMBER|apply affine_inner_pointer_source_writes].
  - intros temps p locals entry memory middle after final PREFIX BODY.
    destruct (@source_load_prefix_observations loads (adapter_entry temps) (globalenv p) locals entry memory E0 middle memory Out_normal
      FRESH PREFIX) as [_ [_ [_ OBSERVED]]].
    intros identifier MEMBER; apply OBSERVED,COVER; exact MEMBER.
  - intros temps p locals entry memory after final SCOPE OBSERVED SOURCE.
    destruct (@affine_inner_pointer_guarded_candidate_execution (adapter_entry temps) (globalenv p) locals entry memory after final
      OBSERVED SOURCE) as [target [EXECUTE PUBLIC]].
    exists target,final; split; [exact EXECUTE|split; [exact PUBLIC|apply memory_equivalent_refl]].
Qed.
End PRESERVATION.

Print Assumptions affine_inner_pointer_source_writes.
Print Assumptions affine_inner_pointer_guarded_candidate_execution.
Print Assumptions affine_inner_pointer_observed_candidate_contract.
