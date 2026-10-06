From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightTempFrame
  ClightTempFootprint ClightRedundantSet ClightRegionProgress ClightLoopSyntax ClightFrontendLoopProtocol ClightCountedLoop.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceShape
  AffineNestFirstDomain AffineNestFirstLeaf AffineNestLeafModel AffineNestGuardPackage
  AffineNestNamespace AffineNestPackageGuard AffineNestProbe AffineNestProbeStage AffineNestDomainGuard
  AffineNestGuardParameterCheck AffineNestAcceptedDomain AffineNestMathDomain.
From GuardInterface Require Import GuardInterface ClightStrictLoopProgress ClightLoadedBoundSyntax
  ClightAffineFirstBodyReceipt ClightLoadedAffineFirstPath ClightMaterializedCheck
  ClightMaterializedCertificate ClightAffineNestMaterialized ClightPrivateScanHost ClightPrivateScanPreservation ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.

(** Reuse the checked package without a completion premise for its cached
    root. The receipt supplies only reached headers and the first real body. *)
Theorem affine_receipted_package_guard_execution source parameters live proposal
  (package : affine_guard_package source parameters live proposal) fe ge locals temps memory :
  affine_first_body_receipt (affine_proposed_iterator proposal) (affine_proposed_bound proposal)
    (affine_proposed_body proposal) fe (Entry ge locals temps memory) ->
  exists after,
    exec_stmt fe ge locals temps memory (affine_package_guard_code package) E0 after memory Out_normal /\
    temp_agree (affine_single_materialized_ports parameters proposal live) temps after /\
    after!(affine_proposed_result proposal)=Some(Vint(if affine_package_guard_flag parameters proposal
      (Entry ge locals temps memory) then Int.one else Int.zero)) /\
    (affine_package_guard_flag parameters proposal (Entry ge locals temps memory)=true ->
     affine_math_domain (affine_proposed_leaf_bounds proposal) (affine_proposal_layout proposal parameters)
       (affine_proposal_nest proposal) (affine_word_valuation temps)
       (affine_word_valuation temps (affine_proposed_iterator proposal))).
Proof.
  intro RECEIPT; pose proof (affine_package_nest package) as NEST.
  pose proof (described_affine_shapes (affine_package_description package)) as SHAPES; rewrite NEST in SHAPES.
  pose proof (@affine_nest_fresh_controls _ (described_affine_fresh (affine_package_description package))) as FRESH;
    rewrite NEST in FRESH.
  pose proof (described_affine_dependencies (affine_package_description package)) as DEPENDENCIES;
    rewrite NEST in DEPENDENCIES.
  pose proof (affine_package_namespace package) as NAMES.
  pose proof (@affine_first_body_header_domain (affine_proposed_iterator proposal) (affine_proposed_bound proposal)
    (MemorySourceTemp (affine_proposed_bound proposal)) (affine_proposed_body proposal) (affine_proposed_child proposal)
    fe ge locals temps memory SHAPES FRESH (affine_leaf_normal (affine_package_leaf package))
    (affine_leaf_quiet (affine_package_leaf package)) (affine_leaf_writes (affine_package_leaf package)) RECEIPT) as DOMAIN.
  assert (PARAMETERS : affine_first_path_flag (affine_proposal_nest proposal) temps=true ->
    Forall (fun identifier => register_domain identifier (Entry ge locals temps memory)) parameters).
  { intro ACTIVE; eapply affine_first_body_parameter_domains;
      [exact SHAPES|exact FRESH|exact (affine_leaf_normal (affine_package_leaf package))|
       exact (affine_leaf_quiet (affine_package_leaf package))|exact (affine_leaf_writes (affine_package_leaf package))|
       exact RECEIPT|exact (affine_package_leaf package)|exact (affine_package_used package)|].
    exact (proj1 (@affine_first_path_flag_exact (affine_proposal_nest proposal) temps) ACTIVE). }
  destruct (@affine_domain_guard_execution (affine_proposed_iterator proposal) (affine_proposed_bound proposal)
    (MemorySourceTemp (affine_proposed_bound proposal)) (affine_proposed_body proposal) (affine_proposed_child proposal)
    (affine_proposed_parameter_ranges proposal) parameters (affine_proposed_floor proposal) (affine_proposed_cap proposal)
    live (affine_probe_registry (affine_proposal_nest proposal) parameters) (affine_proposal_rename proposal)
    (affine_proposed_result proposal) fe ge locals temps memory DEPENDENCIES
    (@affine_probe_registry_coverage _ _) (affine_names_injective NAMES) (affine_names_root_distinct NAMES)
    (affine_names_result_private NAMES) (affine_names_controls_private NAMES) (affine_names_parameters NAMES)
    DOMAIN PARAMETERS) as [after [RUN [FRAME RESULT]]].
  exists after; split; [exact RUN|split; [exact FRAME|split; [exact RESULT|]]].
  intro ACCEPT; eapply (@affine_domain_guard_accepted (affine_proposed_iterator proposal) (affine_proposed_bound proposal)
    (MemorySourceTemp (affine_proposed_bound proposal)) (affine_proposed_body proposal) (affine_proposed_child proposal)
    (affine_proposed_parameter_ranges proposal) parameters (affine_proposed_floor proposal) (affine_proposed_cap proposal)
    (affine_proposed_remaining proposal) (affine_proposed_leaf_bounds proposal) (affine_proposal_layout proposal parameters)
    (Entry ge locals temps memory));
    [exact (affine_package_profile package)|exact (affine_package_parameter_intervals package)|exact FRESH| |exact ACCEPT].
  intros identifier MEMBER; exact (proj2 (@check_affine_guard_parameters_sound _ _ _ _ _
    (affine_package_used package) identifier MEMBER)).
Qed.

Definition affine_loaded_numeric_source pointer proposal :=
  loaded_bound_loop (affine_proposed_iterator proposal) pointer (affine_proposed_body proposal).
Definition affine_loaded_numeric_snapshot pointer proposal entry :=
  exists block offset upper,
    (entry_temps entry)!pointer=Some(Vptr block offset) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr block offset)=Some(Vint upper) /\
    (entry_temps entry)!(affine_proposed_bound proposal)=Some(Vint upper).
Definition affine_loaded_numeric_domain pointer proposal entry :=
  materialized_source_completion (affine_loaded_numeric_source pointer proposal) entry /\
  affine_loaded_numeric_snapshot pointer proposal entry.
Definition affine_loaded_numeric_premise parameters proposal entry :=
  affine_package_guard_flag parameters proposal entry=true /\
  affine_math_domain (affine_proposed_leaf_bounds proposal) (affine_proposal_layout proposal parameters)
    (affine_proposal_nest proposal) (affine_word_valuation (entry_temps entry))
    (affine_word_valuation (entry_temps entry) (affine_proposed_iterator proposal)).

Lemma affine_loaded_numeric_body_properties source parameters live proposal
  (package : affine_guard_package source parameters live proposal) :
  normal_statement (affine_proposed_body proposal)=true /\
  quiet_statement (affine_proposed_body proposal)=true.
Proof.
  pose proof (affine_package_nest package) as NEST.
  pose proof (described_affine_shapes (affine_package_description package)) as SHAPES; rewrite NEST in SHAPES.
  split.
  - eapply affine_nest_body_normal; [exact SHAPES|exact (affine_leaf_normal (affine_package_leaf package))|
      exact (affine_leaf_quiet (affine_package_leaf package))].
  - pose proof (affine_materialized_source_quiet package) as QUIET.
    pose proof (described_affine_source (affine_package_description package)) as EXACT;
      rewrite NEST in EXACT; rewrite EXACT in QUIET.
    cbn [affine_nest_source affine_proposal_nest frontend_counted_loop quiet_statement counter_increment] in QUIET;
      repeat rewrite andb_true_iff in QUIET; tauto.
Qed.

Lemma affine_loaded_numeric_source_quiet source parameters live proposal pointer
  (package : affine_guard_package source parameters live proposal) :
  quiet_statement (affine_loaded_numeric_source pointer proposal)=true.
Proof.
  destruct (affine_loaded_numeric_body_properties package) as [_ QUIET].
  cbn [affine_loaded_numeric_source loaded_bound_loop strict_frontend_loop quiet_statement counter_increment];
    rewrite QUIET; reflexivity.
Qed.

(** The snapshot in D is a value read at this entry. It contains no future
    stability or non-alias premise; source execution supplies the first body. *)
Definition affine_loaded_numeric_certificate source parameters live proposal pointer
  (package : affine_guard_package source parameters live proposal) test
  (BODY : materialized_body test=affine_package_guard_code package)
  (COND : materialized_condition test=Etempvar (affine_proposed_result proposal) type_int32s) temps :
  guard_certificate (materialized_host (adapter_entry temps) (scan_public_observe live))
    (affine_loaded_numeric_domain pointer proposal) (affine_loaded_numeric_premise parameters proposal)
    (private_scan_entry_frame (affine_single_materialized_ports parameters proposal live))
    (private_scan_entry_frame (affine_single_materialized_ports parameters proposal live)) test.
Proof.
  apply materialized_execution_certificate; intros [ge locals le memory] [COMPLETED [block [offset [upper [POINTER [READ CACHE]]]]]].
  destruct (@materialized_source_receipt (adapter_entry temps) _ _
    (affine_loaded_numeric_source_quiet pointer package) COMPLETED) as [after [final SOURCE]].
  destruct (affine_loaded_numeric_body_properties package) as [NORMAL QUIET].
  pose proof (@loaded_affine_first_body_receipt (adapter_entry temps) ge locals le memory
    (affine_proposed_iterator proposal) pointer (affine_proposed_bound proposal) (affine_proposed_body proposal)
    after final block offset upper NORMAL QUIET POINTER READ CACHE SOURCE) as RECEIPT.
  destruct (@affine_receipted_package_guard_execution source parameters live proposal package (adapter_entry temps)
    ge locals le memory RECEIPT) as [checked [RUN [FRAME [RESULT MATH]]]].
  exists (affine_package_guard_flag parameters proposal (Entry ge locals le memory)),checked.
  rewrite BODY,COND; cbn [entry_ge entry_env entry_temps entry_memory].
  split; [exact RUN|split; [apply affine_probe_result_test; exact RESULT|split; [exact FRAME|]]].
  intro ACCEPT; split; [exact ACCEPT|apply MATH; exact ACCEPT].
Defined.

(** An actual private capture produces D from the original source. No caller
    needs to assert that the cached source can complete. The returned source
    execution retains every original loaded header. *)
Theorem affine_loaded_numeric_capture_domain source parameters live proposal pointer
  (package : affine_guard_package source parameters live proposal) public fe ge locals le memory after final :
  check_plan_frameable (affine_loaded_numeric_source pointer proposal)=true ->
  ~In (affine_proposed_bound proposal) (statement_temps (affine_loaded_numeric_source pointer proposal)++public) ->
  exec_stmt fe ge locals le memory (affine_loaded_numeric_source pointer proposal) E0 after final Out_normal ->
  exists upper prepared_after,
    exec_stmt fe ge locals le memory (Sset (affine_proposed_bound proposal) (signed_load pointer))
      E0 (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory Out_normal /\
    exec_stmt fe ge locals (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory
      (affine_loaded_numeric_source pointer proposal) E0 prepared_after final Out_normal /\
    temp_agree (statement_temps (affine_loaded_numeric_source pointer proposal)++public) after prepared_after /\
    affine_loaded_numeric_domain pointer proposal
      (Entry ge locals (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory).
Proof.
  intros FRAMEABLE PRIVATE SOURCE; destruct (affine_loaded_numeric_body_properties package) as [NORMAL QUIET].
  destruct (@loaded_affine_capture_receipt fe ge locals le memory (affine_proposed_iterator proposal) pointer
    (affine_proposed_body proposal) (affine_proposed_bound proposal) public after final NORMAL QUIET FRAMEABLE PRIVATE SOURCE)
    as [upper [prepared_after [CAPTURE [PREPARED [PUBLIC RECEIPT]]]]].
  exists upper,prepared_after; split; [exact CAPTURE|split; [exact PREPARED|split; [exact PUBLIC|split]]].
  - exists fe,prepared_after,final; exact PREPARED.
  - inversion CAPTURE; subst.
    match goal with SAME : PTree.set ?key ?value ?before = PTree.set ?key (Vint upper) ?before |- _ =>
      pose proof (f_equal (fun mapping => mapping!key) SAME) as VALUE;
      rewrite !PTree.gss in VALUE; injection VALUE as VALUE; subst value end.
    match goal with EVAL : eval_expr _ _ _ _ (signed_load pointer) _ |- _ =>
      destruct (signed_load_inv EVAL) as [block [offset [POINTER READ]]] end.
    exists block,offset,upper; cbn [entry_temps entry_memory]; split; [|split; [exact READ|apply PTree.gss]].
    rewrite PTree.gso; [exact POINTER|].
    intro SAME; apply PRIVATE,in_or_app; left; rewrite SAME; apply loaded_bound_pointer_in_scope.
Qed.

Print Assumptions affine_receipted_package_guard_execution.
Print Assumptions affine_loaded_numeric_body_properties.
Print Assumptions affine_loaded_numeric_source_quiet.
Print Assumptions affine_loaded_numeric_certificate.
Print Assumptions affine_loaded_numeric_capture_domain.
