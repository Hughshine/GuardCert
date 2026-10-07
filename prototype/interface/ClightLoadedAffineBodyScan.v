From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells GuardMemoryBooleanScan
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestMathDomain
  AffineNestGuardPackage AffineNestGuardParameterCheck AffineNestSourceDecode AffineNestScanModel AffineNestScanSyntax
  AffineNestScanNamespace AffineNestScanExecution.
From GuardInterface Require Import ClightLoadedBodyPrefix ClightLoadedAffineBodyPrefix ClightLoadedAffineBodyDomain
  ClightAffineObservationLeaf ClightLoadedAffineWriteTest.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_loaded_body_scan_statement proposal pointer controls flag :=
  affine_scan_statement (affine_proposed_child proposal) controls(affine_scan_values(affine_proposal_nest proposal) controls)
    (Econst_int Int.zero type_int32s)
    (affine_observation_leaf pointer(affine_scan_values(affine_proposal_nest proposal) controls) flag(affine_proposed_operations proposal)).
Definition affine_loaded_child_scan_live proposal (controls : ident -> ident) live :=
  controls(affine_proposed_iterator proposal)::controls(affine_proposed_bound proposal)::live.

Lemma affine_loaded_ready_child_math parameters proposal entry i :
  affine_loaded_body_ready parameters proposal entry ->
  0<=i<Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps entry)) ->
  affine_math_domain(affine_proposed_leaf_bounds proposal)(affine_proposal_layout proposal parameters)
    (affine_proposed_child proposal)
    (memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i) 0.
Proof.
  intros [[CHECK DOMAIN] [ROW WORDS]] RANGE.
  assert(ZERO:affine_word_valuation(entry_temps entry)(affine_proposed_iterator proposal)=0)
    by(unfold affine_word_valuation,temp_word; rewrite ROW; reflexivity).
  cbn [affine_math_domain affine_proposal_nest memory_source_affine_math] in DOMAIN; rewrite ZERO in DOMAIN.
  apply (proj2(proj2 DOMAIN)); exact RANGE.
Qed.

Theorem affine_loaded_body_scan_execution source parameters public proposal pointer
  (package : affine_guard_package source parameters public proposal) controls flag live
  (names : affine_scan_namespace(affine_proposal_nest proposal) parameters live controls flag)
  fe entry i code checked good block offset :
  affine_loaded_body_names_check proposal pointer=true ->
  loaded_body_prefix fe (affine_proposed_iterator proposal)(affine_proposed_bound proposal) pointer
    (affine_proposed_body proposal)(affine_loaded_body_stable parameters proposal pointer)
    (affine_loaded_body_ready parameters proposal) i entry ->
  i<Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps entry)) ->
  affine_loaded_body_model parameters proposal=Some code ->
  incl parameters live -> incl(pointer::affine_proposed_pointers proposal) live ->
  temp_agree live(entry_temps entry) checked ->
  checked!(controls(affine_proposed_iterator proposal))=Some(Vint(Int.repr i)) ->
  checked!flag=Some(memory_boolean_word good) ->
  (entry_temps entry)!pointer=Some(Vptr block offset) ->
  exists after,
    exec_stmt fe (entry_ge entry)(entry_env entry) checked(entry_memory entry)
      (affine_loaded_body_scan_statement proposal pointer controls flag) E0 after(entry_memory entry) Out_normal /\
    temp_agree(affine_loaded_child_scan_live proposal controls live) checked after /\
    after!flag=Some(memory_boolean_word(good&&affine_loaded_body_check_result proposal i entry
      (CompCertMemoryActions.MemoryLocation Mint32 block(Ptrofs.unsigned offset)))).
Proof.
  intros NAMES PREFIX ACTIVE LOWER PARAM_LIVE POINTER_LIVE FRAME ROW FLAG POINTER.
  pose proof PREFIX as [READY [CACHE [RANGE REST]]].
  pose proof(affine_scan_names_unique names) as UNIQUE.
  cbn [affine_proposal_nest affine_nest_controls map] in UNIQUE.
  apply NoDup_cons_iff in UNIQUE as [ROOT_UNIQUE UNIQUE]; apply NoDup_cons_iff in UNIQUE as [BOUND_UNIQUE CHILD_UNIQUE].
  pose proof(described_affine_dependencies(affine_package_description package)) as DEPENDENCIES;
    rewrite(affine_package_nest package) in DEPENDENCIES.
  set(values:=affine_scan_values(affine_proposal_nest proposal) controls).
  set(valuation:=memory_source_set_valuation(affine_word_valuation(entry_temps entry))(affine_proposed_iterator proposal) i).
  set(keep:=affine_loaded_child_scan_live proposal controls live).
  assert (ROOT_VALUE : values(affine_proposed_iterator proposal)=controls(affine_proposed_iterator proposal)).
  { unfold values; apply affine_scan_values_iterator; cbn [affine_proposal_nest affine_nest_iterators]; left; reflexivity. }
  assert (FLAG_LIVE : ~In flag live).
  { intro BAD; apply(affine_scan_names_flag_private names),in_or_app; right; exact BAD. }
  assert (FLAG_KEEP : ~In flag keep).
  { unfold keep,affine_loaded_child_scan_live; intros [BAD|[BAD|BAD]]; [| |contradiction].
    - pose proof(proj2(affine_scan_names_private names (affine_proposed_iterator proposal) ltac:(cbn; auto))); congruence.
    - pose proof(proj2(affine_scan_names_private names (affine_proposed_bound proposal) ltac:(cbn; auto))); congruence. }
  assert (WORD_PRIVATE : ~In flag(map values(affine_proposal_layout proposal parameters))).
  { intro BAD; apply in_map_iff in BAD as [identifier [SAME MEMBER]].
    unfold affine_proposal_layout in MEMBER; apply in_app_or in MEMBER as [ITERATOR|PARAMETER].
    - unfold values in SAME; rewrite affine_scan_values_iterator in SAME by exact ITERATOR.
      pose proof(proj2(affine_scan_names_private names identifier
        (proj2(@affine_nest_controls_member _ _)(or_introl ITERATOR)))); congruence.
    - unfold values in SAME; rewrite(affine_scan_names_parameters names identifier PARAMETER) in SAME.
      apply(affine_scan_names_flag_private names),in_or_app; left; rewrite <-SAME; exact PARAMETER. }
  assert (WORDS : affine_scan_word_view(affine_proposed_iterator proposal::parameters) values valuation checked).
  { intros identifier [SAME|MEMBER].
    - subst identifier; rewrite ROOT_VALUE; unfold valuation,memory_source_set_valuation;
        destruct(peq (affine_proposed_iterator proposal)(affine_proposed_iterator proposal)); [exact ROW|contradiction].
    - unfold values; rewrite(affine_scan_names_parameters names identifier MEMBER).
      unfold valuation,memory_source_set_valuation; destruct(peq identifier(affine_proposed_iterator proposal)) as [SAME|OTHER].
      + subst identifier; exfalso.
        pose proof(proj2(@check_affine_guard_parameters_sound _ _ _ _ _ (affine_package_used package) _ MEMBER)) as PRIVATE.
        apply PRIVATE; cbn [affine_nest_mutated affine_proposal_nest]; left; reflexivity.
      + rewrite FRAME by(apply PARAM_LIVE; exact MEMBER); apply(proj2(proj2 READY)); exact MEMBER. }
  unfold affine_loaded_body_scan_statement,affine_loaded_body_check_result.
  fold values valuation.
  eapply affine_scan_execution with(prefix:=[affine_proposed_iterator proposal])(parameters:=parameters)
    (valuation:=valuation)(lower:=0)(live:=keep)(public:=live)(base:=entry_temps entry)
    (test:=affine_observation_result
      (window_multi_pointer_locations(entry_temps entry)(affine_proposed_window_lower proposal)(affine_proposed_window_upper proposal))
      (CompCertMemoryActions.MemoryLocation Mint32 block(Ptrofs.unsigned offset))(affine_proposed_operations proposal))
    (bounds:=affine_proposed_leaf_bounds proposal)(layout:=affine_proposal_layout proposal parameters);
    try eassumption; try reflexivity.
  - exact(proj2 DEPENDENCIES).
  - intros identifier MEMBER; unfold values; apply affine_scan_values_iterator;
      cbn [affine_nest_iterators affine_proposal_nest]; right; exact MEMBER.
  - intros identifier MEMBER.
    destruct(affine_scan_names_private names identifier (or_intror(or_intror MEMBER)))
      as [PRIVATE NOT_FLAG].
    split; [|exact NOT_FLAG]; unfold keep,affine_loaded_child_scan_live.
    intros [SAME|[SAME|BAD]].
    + apply ROOT_UNIQUE; right; rewrite SAME; apply in_map; exact MEMBER.
    + apply BOUND_UNIQUE; rewrite SAME; apply in_map; exact MEMBER.
    + apply PRIVATE,in_or_app; right; exact BAD.
  - unfold keep,affine_loaded_child_scan_live; intros identifier MEMBER; right; right; exact MEMBER.
  - intros identifier MEMBER; apply in_map_iff in MEMBER as [original [<- MEMBER]].
    destruct MEMBER as [SAME|MEMBER].
    + subst original; rewrite ROOT_VALUE; unfold keep,affine_loaded_child_scan_live; left; reflexivity.
    + unfold values; rewrite(affine_scan_names_parameters names original MEMBER).
      unfold keep,affine_loaded_child_scan_live; right; right; apply PARAM_LIVE; exact MEMBER.
  - apply affine_loaded_ready_child_math; [exact READY|lia].
  - constructor.
  - intros point current before protected POINT CURRENT CURRENT_FRAME BEFORE PROTECTED INCLUDED.
    eapply affine_observation_leaf_execution with(public:=live)(base:=entry_temps entry)
      (layout:=affine_proposal_layout proposal parameters); try eassumption.
    intros operation inside OPERATION INSIDE_FRAME INSIDE_WORDS.
    eapply affine_loaded_point_write_test;
      [exact package|exact NAMES|exact PREFIX|exact ACTIVE|exact LOWER|exact POINT|exact OPERATION| |exact INSIDE_WORDS|exact POINTER].
    eapply temp_agree_weaken; [exact POINTER_LIVE|exact INSIDE_FRAME].
Qed.

Print Assumptions affine_loaded_ready_child_math.
Print Assumptions affine_loaded_body_scan_execution.
