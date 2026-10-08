From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightGuard ClightPureExpr ClightNoWrap ClightRedundantSet ClightCountedLoop.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryArrayBackend GuardMemoryNaryRanges
  GuardMemoryParameterRanges GuardMemoryParametricGuard GuardMemoryParametricSourceDomain GuardMemoryParametricSourceClight
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource GuardMemoryZeroWidthPointerSource.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ReadonlyConditionComposition ClightConditionComposition ClightAffineInnerPointerSourceGuard
  ClightAffineDomainFacts ClightAffinePreparedState ClightAffineSnapshotSyntax ClightFirstReachedWidth
  ClightAffineSnapshotReachedCondition ClightAffineSnapshotZeroWidthView.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section READY.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Let row:=affine_inner_pointer_row shape.
Let expression:=affine_inner_pointer_expression package.
Let cap:=affine_inner_pointer_column_limit package.
Let geometry:=affine_inner_pointer_geometry package.
Let caps:=affine_inner_pointer_geometry_caps package.
Let context:=memory_affine_inner_pointer_region_context package.
Let CERT:=affine_inner_pointer_syntax package.
Variable skip : nat.
Variable bounds : list MemoryNested.A.interval.
Variable tree : decision_tree.
Hypothesis COMPILE : compile_first_reached_width 0 cap skip row
  (memory_affine_inner_pointer_header shape expression) bounds expression=Some tree.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable O : Type.
Variable observe : fragment_observation -> O -> Prop.
Let H:=readonly_clight_host fe observe.
Let D:=snapshot_first_reached_domain site bounds fe.
Let facts:=snapshot_first_reached_facts site 0 cap skip.
Let range_fact entry:=memory_nary_ranges caps(memory_source_parameter_values geometry entry).
Definition affine_zero_geometry_tree:=memory_parameter_ranges_tree caps geometry(Decision true).

Lemma affine_zero_geometry_limits : Forall(fun value=>0<value /\ signed_range value)caps.
Proof.
  unfold caps,affine_inner_pointer_geometry_caps; constructor.
  - split; [|exact(affine_inner_pointer_bound_limit CERT)].
    pose proof(affine_inner_pointer_control_limits CERT)as CAPS; inversion CAPS; subst; lia.
  - exact(affine_inner_pointer_parameter_limits CERT).
Qed.

Lemma affine_zero_facts_context_view entry : D entry -> facts entry ->
  MemoryNested.A.typed_view context(memory_source_parameter_values context entry)(entry_temps entry).
Proof.
  intros DOMAIN [_ WORDS].
  pose proof(@snapshot_first_reached_header_view original site bounds fe entry DOMAIN)as HEADER.
  apply memory_source_parameter_view; intros identifier MEMBER.
  unfold context,memory_affine_inner_pointer_region_context,memory_affine_inner_pointer_parameters in MEMBER.
  rewrite <-app_assoc in MEMBER; apply in_app_or in MEMBER as [HEAD|BODY].
  - eapply memory_source_typed_word; [exact HEADER|exact HEAD].
  - apply WORDS; exact BODY.
Qed.

Lemma affine_zero_geometry_exact entry : D entry -> facts entry -> forall flag,
  decision_run entry affine_zero_geometry_tree flag <->
    flag=memory_parameter_ranges_accept caps geometry entry.
Proof.
  intros DOMAIN FACTS flag.
  rewrite <-(andb_true_r(memory_parameter_ranges_accept caps geometry entry)).
  apply memory_parameter_ranges_exact.
  - apply Forall_forall; intros identifier MEMBER.
    eapply memory_source_typed_word; [exact(affine_zero_facts_context_view DOMAIN FACTS)|].
    unfold context,memory_affine_inner_pointer_region_context; apply in_or_app; left; exact MEMBER.
  - intros _ answer; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst answer; constructor].
Qed.

(** Ordered dependency: body/address parameter reads occur only after the
    first-reached certificate produces their word typing from original source. *)
Definition affine_zero_geometry_condition :
  readonly_condition H(fun entry=>D entry /\ facts entry)range_fact affine_zero_geometry_tree.
Proof.
  apply readonly_completed_tree_condition.
  - intros entry[DOMAIN FACTS]; eexists; apply(proj2(affine_zero_geometry_exact DOMAIN FACTS _)); reflexivity.
  - intros entry[DOMAIN FACTS]RUN.
    apply memory_parameter_ranges_sound; [exact affine_zero_geometry_limits|].
    symmetry; apply(proj1(affine_zero_geometry_exact DOMAIN FACTS true)); exact RUN.
Defined.

Lemma affine_zero_ready_from_facts entry : D entry -> facts entry -> range_fact entry ->
  affine_domain_ready package entry.
Proof.
  intros DOMAIN FACTS RANGE; constructor.
  - exact(proj1(proj2 DOMAIN)).
  - destruct FACTS as [WIDTH WORDS].
    unfold first_reached_width_fact in WIDTH; destruct WIDTH as [REACHED[ALL REST]].
    unfold memory_affine_inner_pointer_zero_width_property; intros i I.
    rewrite memory_affine_inner_pointer_word_math; apply ALL; rewrite memory_source_word_temp in I; exact I.
  - exact RANGE.
  - exact(affine_zero_facts_context_view DOMAIN FACTS).
Qed.

Definition affine_zero_preparation_tree:=decision_bind tree affine_zero_geometry_tree(Decision false).
Definition affine_zero_preparation_condition :
  readonly_condition H D(affine_domain_ready package)affine_zero_preparation_tree.
Proof.
  eapply readonly_condition_entails.
  - apply(@sequence_readonly_conditions clight_entry H(clight_readonly_check_algebra fe observe)
      D facts range_fact tree affine_zero_geometry_tree).
    + exact(@snapshot_first_reached_condition original site 0 cap skip bounds tree COMPILE
        ltac:(change Int.min_signed with(-2147483648); lia)
        ltac:(pose proof affine_zero_geometry_limits as CAPS;
          pose proof(affine_inner_pointer_control_limits CERT)as CTRL;
          rewrite Forall_forall in CTRL; exact(proj2(proj2(CTRL cap ltac:(unfold cap; cbn; auto)))))
        fe O observe).
    + exact affine_zero_geometry_condition.
  - intros entry DOMAIN[FACTS RANGE]; apply affine_zero_ready_from_facts; assumption.
Defined.
End READY.

Print Assumptions affine_zero_geometry_limits.
Print Assumptions affine_zero_facts_context_view.
Print Assumptions affine_zero_geometry_exact.
Print Assumptions affine_zero_geometry_condition.
Print Assumptions affine_zero_ready_from_facts.
Print Assumptions affine_zero_preparation_condition.
