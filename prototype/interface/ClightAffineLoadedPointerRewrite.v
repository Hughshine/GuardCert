From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightGuard ClightNoWrap ClightTempFrame
  ClightRedundantSet ClightRectangularGuard ClightCountedLoop ClightFrontendLoopProtocol ClightStraightLine
  ClightPrivateRegion ClightProjectedExecution ClightTempFootprint ClightRegionProgress ClightLoopSyntax CompCertMemoryEquivalence.
From GuardMemory Require Import GuardMemoryParametricWidth GuardMemoryAffineInnerPointerSyntax
  GuardMemoryParametricSourceClight GuardMemoryPointerSequence GuardMemoryAffineInnerPointerSourceDomain.
From GuardInterface Require Import GuardedRewrite ClightAffineLoadedPointerExample ClightAffineLoadedBoundTransport
  ClightLoadedBoundSyntax ClightAffinePointerGuard ClightAffinePointerGuardExamples ClightSourceObservation ClightReadonlyRewrite
  ClightSourcePreloadObservation ClightStrictLoopProgress
  ReadonlyConditionComposition ClightConditionComposition ClightReadonlyCompletedCondition
  ClightReadonlyLoadedTreeSynthesis ClightAffineInnerPointerSourceGuard ClightAffineInnerPointerCandidateGuard
  ClightAffineInnerPointerCandidate ClightAffineInnerPointerPreservation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition alp_cached_package : memory_affine_inner_pointer_package ap_source.
Proof.
  destruct (ap_description ap_source 64 64 [] [] [ap_p;ap_q]) as [package|] eqn:DESCRIPTION.
  - exact package.
  - exfalso; pose proof affine_inner_pointer_triangle_source_selected as SELECTED.
    rewrite DESCRIPTION in SELECTED; discriminate.
Defined.
Lemma alp_cached_pointers : affine_inner_pointer_pointers alp_cached_package = [ap_p;ap_q].
Proof. vm_compute; reflexivity. Qed.

(** D contains observed values and source capabilities, but no write-stability
    or non-alias presumption. A retained source prefix produces it below. *)
Definition alp_entry_domain entry := register_domain ap_i entry /\
  (exists word block offset,
    (entry_temps entry) ! ap_n = Some (Vint word) /\
    (entry_temps entry) ! ap_p = Some (Vptr block offset) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) = Some (Vint word)) /\
  observed_pointer_domain [ap_p;ap_q] entry.
Definition alp_preliminary := decision_bind (register_tree ap_i Int.zero) (register_range_tree ap_n 64) (Decision false).
Definition alp_preliminary_flag entry := register_flag ap_i Int.zero entry && register_range_flag ap_n 64 entry.
Definition alp_prepared entry := (entry_temps entry) ! ap_i = Some (Vint Int.zero) /\
  exists N block offset, (entry_temps entry) ! ap_n = Some (Vint (Int.repr N)) /\
    (entry_temps entry) ! ap_p = Some (Vptr block offset) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) = Some (Vint (Int.repr N)) /\ 0 < N <= 64.
Lemma alp_preliminary_run entry : alp_entry_domain entry -> decision_run entry alp_preliminary (alp_preliminary_flag entry).
Proof.
  intros [ROW [[word [block [offset [CACHE _]]]] OBSERVED]].
  unfold alp_preliminary,alp_preliminary_flag; eapply decision_bind_run; [apply register_tree_run; exact ROW|].
  destruct (register_flag ap_i Int.zero entry); cbn; [apply register_range_tree_run; exists word; exact CACHE|constructor].
Qed.
Lemma alp_preliminary_sound entry : alp_entry_domain entry -> alp_preliminary_flag entry = true -> alp_prepared entry.
Proof.
  intros [[row ROW] [[word [block [offset [CACHE [POINTER READ]]]]] OBSERVED]] ACCEPT.
  unfold alp_preliminary_flag in ACCEPT; apply andb_true_iff in ACCEPT as [ZERO RANGE].
  unfold register_flag,temp_word in ZERO; rewrite ROW in ZERO; apply Int.same_if_eq in ZERO; subst row.
  pose proof (@register_range_sound ap_n 64 entry ltac:(change (-2147483648 <= 64 <= 2147483647); lia)
    ltac:(exists word; exact CACHE) RANGE) as [_ BOUND].
  unfold temp_word in BOUND; rewrite CACHE in BOUND.
  split; [exact ROW|exists (Int.signed word),block,offset; rewrite Int.repr_signed; auto].
Qed.

Definition alp_completed_domain fe entry := alp_entry_domain entry /\ exists after final,
  exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) alp_source E0 after final Out_normal.
Definition alp_preliminary_condition fe O (observe : fragment_observation -> O -> Prop) :
  readonly_condition (readonly_clight_host fe observe) (alp_completed_domain fe) alp_prepared alp_preliminary.
Proof.
  apply readonly_completed_tree_condition.
  - intros entry [DOMAIN SOURCE]; exists (alp_preliminary_flag entry); apply alp_preliminary_run; exact DOMAIN.
  - intros entry [DOMAIN SOURCE] RUN; apply alp_preliminary_sound; [exact DOMAIN|].
    eapply readonly_decision_determinate; [apply alp_preliminary_run; exact DOMAIN|exact RUN].
Defined.

Theorem alp_prepared_cached_domain fe entry : alp_completed_domain fe entry -> alp_prepared entry ->
  affine_inner_pointer_observed_completed alp_cached_package fe entry.
Proof.
  destruct entry as [ge locals temps memory]; intros [DOMAIN [after [final SOURCE]]]
    [ZERO [N [block [offset [CACHE [POINTER [READ RANGE]]]]]]].
  destruct (@alp_loaded_source_cached fe ge locals temps memory block offset N after final ZERO CACHE POINTER READ RANGE SOURCE)
    as [CACHED STABLE].
  split.
  - exists after,final; rewrite <- (affine_inner_pointer_source_exact (affine_inner_pointer_syntax alp_cached_package)); exact CACHED.
  - rewrite alp_cached_pointers; exact (proj2 (proj2 DOMAIN)).
Qed.

Section REWRITE.
Variable live : list ident.
Variable candidate : affine_inner_pointer_candidate_package alp_cached_package live.
Variables width alias : decision_tree.
Hypothesis WIDTH : compile_memory_source_width (affine_inner_pointer_column_limit alp_cached_package)
  (affine_inner_pointer_row (affine_inner_pointer_shape alp_cached_package))
  (memory_affine_inner_pointer_header (affine_inner_pointer_shape alp_cached_package) (affine_inner_pointer_expression alp_cached_package))
  (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit alp_cached_package) (affine_inner_pointer_header_limits alp_cached_package))
  (affine_inner_pointer_expression alp_cached_package) = Some width.
Hypothesis ALIAS : compile_affine_inner_pointer_package_envelopes alp_cached_package = Some alias.

Definition alp_guarded_candidate := tree_statement
  (decision_bind alp_preliminary (affine_inner_pointer_package_candidate_guard candidate width alias) (Decision false))
  (affine_inner_pointer_candidate_statement candidate) alp_source.

Definition alp_candidate_condition fe O (observe : fragment_observation -> O -> Prop) :
  readonly_condition (readonly_clight_host fe observe) (fun entry => alp_completed_domain fe entry /\ alp_prepared entry)
    (fun entry => (affine_inner_pointer_ready alp_cached_package entry /\ affine_inner_pointer_source_nonalias alp_cached_package entry) /\
      affine_inner_pointer_candidate_ranges alp_cached_package (affine_inner_candidate_validator_bounds candidate)
        (affine_inner_candidate_encoder_bounds candidate) entry)
    (affine_inner_pointer_package_candidate_guard candidate width alias).
Proof.
  eapply readonly_condition_restrict; [exact (@affine_inner_pointer_candidate_guard_condition ap_source alp_cached_package fe
    O observe width alias (affine_inner_candidate_validator_bounds candidate) (affine_inner_candidate_encoder_bounds candidate) WIDTH ALIAS)|].
  intros entry [DOMAIN PREPARED]; apply alp_prepared_cached_domain; assumption.
Defined.
Definition alp_complete_condition fe O (observe : fragment_observation -> O -> Prop) :=
  sequence_readonly_conditions (clight_readonly_check_algebra fe observe)
    (alp_preliminary_condition fe observe) (alp_candidate_condition fe observe).

(** One actual guarded rewrite: accepted preliminaries establish the loaded
    source's correspondence to the checked source model. The existing guard
    then licenses any independently certified mapped/tiling candidate. Both
    refusals execute the original source with its repeated memory loads. *)
Theorem alp_guarded_candidate_execution fe ge locals temps memory after final :
  alp_entry_domain (Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory alp_source E0 after final Out_normal ->
  exists target, exec_stmt fe ge locals temps memory alp_guarded_candidate E0 target final Out_normal /\
    temp_agree live after target.
Proof.
  intros DOMAIN SOURCE.
  assert (COMPLETED : alp_completed_domain fe (Entry ge locals temps memory))
    by (split; [exact DOMAIN|exists after,final; exact SOURCE]).
  pose proof (@alp_complete_condition fe fragment_observation (@eq fragment_observation)) as CHECK.
  destruct (readonly_available CHECK _ COMPLETED) as [accepted [checked [RUN SAME]]]; subst checked.
  unfold alp_guarded_candidate; destruct accepted.
  - destruct (readonly_sound CHECK _ _ _ COMPLETED (conj RUN eq_refl)) as [_ SOUND].
    destruct (SOUND eq_refl) as [PREPARED [[READY NONALIAS] RANGES]].
    destruct PREPARED as [ZERO [N [block [offset [CACHE [POINTER [READ RANGE]]]]]]].
    destruct (@alp_loaded_source_cached fe ge locals temps memory block offset N after final ZERO CACHE POINTER READ RANGE SOURCE)
      as [CACHED STABLE].
    destruct (@affine_inner_pointer_candidate_execution ap_source alp_cached_package live candidate fe ge locals temps memory
      after final READY NONALIAS RANGES CACHED) as [target [EXECUTE PUBLIC]].
    exists target; split; [|exact PUBLIC].
    eapply decision_fragment_run with (b:=true); [exact RUN|exact EXECUTE].
  - exists after; split; [|apply temp_agree_refl].
    eapply decision_fragment_run with (b:=false); [exact RUN|exact SOURCE].
Qed.
End REWRITE.

Definition alp_loads := [(ap_n,ap_p);(8%positive,ap_p);(9%positive,ap_q)].
Definition alp_observed_source := Ssequence (source_load_prefix alp_loads) alp_source.

Theorem alp_source_prefix_domain fe ge locals temps memory middle after final :
  exec_stmt fe ge locals temps memory (source_load_prefix alp_loads) E0 middle memory Out_normal ->
  exec_stmt fe ge locals middle memory alp_source E0 after final Out_normal ->
  alp_entry_domain (Entry ge locals middle memory).
Proof.
  intros PREFIX SOURCE.
  destruct (@source_preload_value ap_n ap_p [(8%positive,ap_p);(9%positive,ap_q)] fe ge locals temps memory E0 middle memory Out_normal
    ltac:(unfold ap_p,ap_n; congruence) ltac:(unfold ap_n; cbn; intuition congruence) ltac:(unfold ap_p; cbn; intuition congruence) PREFIX)
    as [block [offset [value [CACHE [POINTER READ]]]]].
  destruct (loaded_bound_completed_header SOURCE) as [flag TEST].
  destruct (loaded_bound_test_facts TEST) as [row [word [other [other_offset [ROW [OTHER [LOAD _]]]]]]].
  assert (SAME : Vptr other other_offset = Vptr block offset) by congruence.
  injection SAME as BLOCK OFFSET; subst other other_offset; assert (VALUE : value = Vint word) by congruence; subst value.
  split; [exists row; exact ROW|split; [exists word,block,offset; auto|]].
  destruct (@source_load_prefix_observations alp_loads fe ge locals temps memory E0 middle memory Out_normal
    ltac:(cbn; intros identifier [<-|[<-|[<-|[]]]]; unfold ap_n,ap_p,ap_q; cbn; intuition congruence) PREFIX) as [_ [_ [_ OBSERVED]]].
  intros identifier MEMBER; apply OBSERVED; cbn in *; tauto.
Qed.

Lemma alp_source_writes : writes_only [ap_i;ap_k;ap_j] alp_source.
Proof.
  assert (OUTER : writes_only [ap_k;ap_j] ap_outer).
  { eapply memory_parametric_outer_writes; [exact (@memory_pointer_sequence_writes alp_operations ap_body alp_body_exact)|
      exact alp_outer_exact]. }
  unfold alp_source,loaded_bound_loop,strict_frontend_loop,counter_increment.
  apply writes_loop.
  - apply writes_sequence; [apply writes_sequence; [apply writes_skip|apply writes_if; [apply writes_skip|apply writes_break]]|].
    eapply writes_only_weaken; [|exact OUTER]; cbn; tauto.
  - apply writes_sequence; [apply writes_skip|apply writes_set; cbn; auto].
Qed.

(** C_host finite contract for the actual retained source loads and the loaded
    loop. A program selector must additionally supply its source progress
    protocol; no new whole-program installation is claimed by this theorem. *)
Theorem alp_observed_candidate_contract live
  (candidate : affine_inner_pointer_candidate_package alp_cached_package live) width alias :
  compile_memory_source_width (affine_inner_pointer_column_limit alp_cached_package)
    (affine_inner_pointer_row (affine_inner_pointer_shape alp_cached_package))
    (memory_affine_inner_pointer_header (affine_inner_pointer_shape alp_cached_package) (affine_inner_pointer_expression alp_cached_package))
    (affine_inner_pointer_header_bounds (affine_inner_pointer_row_limit alp_cached_package) (affine_inner_pointer_header_limits alp_cached_package))
    (affine_inner_pointer_expression alp_cached_package) = Some width ->
  compile_affine_inner_pointer_package_envelopes alp_cached_package = Some alias ->
  PrivateRegion.projected_region_contract live alp_observed_source
    (Ssequence (source_load_prefix alp_loads) (alp_guarded_candidate candidate width alias)).
Proof.
  intros WIDTH ALIAS; unfold alp_observed_source.
  apply source_prefix_region_contract with (writes:=source_load_targets alp_loads++[ap_i;ap_k;ap_j]) (domain:=alp_entry_domain).
  - apply source_load_prefix_supported.
  - apply writes_sequence.
    + eapply writes_only_weaken; [intros identifier MEMBER; apply in_or_app; left; exact MEMBER|apply source_load_prefix_writes].
    + eapply writes_only_weaken; [intros identifier MEMBER; apply in_or_app; right; exact MEMBER|exact alp_source_writes].
  - intros; eapply alp_source_prefix_domain; eassumption.
  - intros temps p locals entry memory after final SCOPE DOMAIN SOURCE.
    destruct (@alp_guarded_candidate_execution live candidate width alias WIDTH ALIAS (adapter_entry temps)
      (globalenv p) locals entry memory after final DOMAIN SOURCE) as [target [EXECUTE PUBLIC]].
    exists target,final; split; [exact EXECUTE|split; [exact PUBLIC|apply memory_equivalent_refl]].
Qed.

Print Assumptions alp_cached_pointers.
Print Assumptions alp_preliminary_run.
Print Assumptions alp_preliminary_sound.
Print Assumptions alp_preliminary_condition.
Print Assumptions alp_prepared_cached_domain.
Print Assumptions alp_candidate_condition.
Print Assumptions alp_complete_condition.
Print Assumptions alp_guarded_candidate_execution.
Print Assumptions alp_source_prefix_domain.
Print Assumptions alp_source_writes.
Print Assumptions alp_observed_candidate_contract.
