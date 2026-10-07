From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution
  ClightNoWrap ClightRedundantSet ClightCountedProtocol ClightCountedLoop ClightLoopSyntax ClightRegionProgress
  ClightSameAddress ClightRectangularLoops ClightFrontendLoopProtocol CompCertMemoryActions.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestPackageGuard AffineNestPackageExamples
  AffineNestMathDomain AffineNestWords AffineNestExit.
From GuardInterface Require Import ClightNestedExpressionCapture ClightNestedExpressionTransport
  ClightNestedExpressionPrefix ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader
  ClightSignedExpressionProgress ClightStrictLoopProgress ClightExpressionHeaderCapture
  ClightQuietDeterminacy ClightDualLoadedUnitSyntax ClightObservedHeaderPrefix ClightCheckPlanFrame
  ClightLoadedAffineNumericExamples ClightLoadedAffineNumericSite ClightLoadedBodyPrefixExamples
  ClightLoadedAffineScanExamples ClightLoadedOffsetAliasExample ClightCapturedAffineNumericGuard
  ClightAffineNestMaterialized ClightWordAddressSeparation ClightReadonlyRewrite ClightLoadedBoundSyntax
  ClightLoadedAffineScanAcceptExample.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition nhe_empty_temps block offset := PTree.set 20%positive (Vint Int.zero)
  (PTree.set 21%positive (Vptr block offset) (PTree.empty val)).
Definition nhe_indexed_source := nested_expression_source 20%positive (signed_load_offset 21%positive Int.one)
  1%positive (signed_indexed_offset 21%positive Int.one Int.one) lns_body.
Definition nhe_indexed_capture := nested_expression_capture 20%positive 31%positive
  (signed_load_offset 21%positive Int.one) 32%positive (signed_indexed_offset 21%positive Int.one Int.one).

(** Only shape[0] is required. There is no shape[1] load, child counter,
    output pointer, or initialized child cache in this execution domain. *)
Theorem nested_empty_capture_skips_child fe ge locals memory block offset raw :
  Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint raw) ->
  Int.signed(Int.add raw Int.one)<=0 ->
  exists prepared,
    exec_stmt fe ge locals (nhe_empty_temps block offset) memory nhe_indexed_capture
      E0 prepared memory Out_normal /\
    prepared!31%positive=Some(Vint(Int.add raw Int.one)) /\
    prepared!32%positive=None /\ prepared!1%positive=None /\ prepared!3%positive=None /\
    exec_stmt fe ge locals prepared memory nhe_indexed_source E0 prepared memory Out_normal.
Proof.
  intros READ NONPOSITIVE.
  assert (FLAG : Int.lt Int.zero (Int.add raw Int.one)=false).
  { unfold Int.lt; change (Int.signed Int.zero) with 0;
      destruct (zlt 0 (Int.signed(Int.add raw Int.one))); [lia|reflexivity]. }
  assert (SOURCE : exec_stmt fe ge locals (nhe_empty_temps block offset) memory nhe_indexed_source
    E0 (nhe_empty_temps block offset) memory Out_normal).
  { apply signed_expression_zero_trip_execution; rewrite <-FLAG.
    apply signed_expression_test_eval; [reflexivity|reflexivity|].
    eapply signed_load_offset_eval; [reflexivity|exact READ]. }
  destruct (@nested_expression_capture_execution fe ge locals (nhe_empty_temps block offset) memory
    20%positive (signed_load_offset 21%positive Int.one) 1%positive
    (signed_indexed_offset 21%positive Int.one Int.one) lns_body 31%positive 32%positive []
    (nhe_empty_temps block offset) memory eq_refl eq_refl eq_refl eq_refl
    ltac:(vm_compute; intuition congruence) ltac:(vm_compute; intuition congruence) ltac:(discriminate)
    ltac:(vm_compute; intuition congruence) SOURCE)
    as [upper [child [prepared_after [CAPTURE [PREPARED [PUBLIC [EVAL CHILD]]]]]]].
  assert (UPPER : upper=Int.add raw Int.one).
  { pose proof (@signed_load_offset_eval ge locals (nhe_empty_temps block offset) memory 21%positive
      Int.one block offset raw eq_refl READ) as EXPECTED.
    pose proof (proj1(expressions_determinate ge locals (nhe_empty_temps block offset) memory) _ _ EVAL _ EXPECTED) as SAME.
    congruence. }
  subst upper; assert (NO_CHILD : child=None).
  { destruct child as [word|]; [destruct CHILD as [ACTIVE REST]; change (Int.lt Int.zero (Int.add raw Int.one)=true) in ACTIVE;
      rewrite FLAG in ACTIVE; discriminate|reflexivity]. }
  subst child.
  exists (PTree.set 31%positive (Vint(Int.add raw Int.one)) (nhe_empty_temps block offset)).
  split; [exact CAPTURE|split; [apply PTree.gss|split; [reflexivity|split; [reflexivity|split; [reflexivity|]]]]].
  apply signed_expression_zero_trip_execution; rewrite <-FLAG.
  apply signed_expression_test_eval; [reflexivity|reflexivity|].
  eapply signed_load_offset_eval; [reflexivity|exact READ].
Qed.

Theorem nested_negative_one_capture_skips_child fe ge locals memory block offset :
  Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint(Int.repr(-1))) -> exists prepared,
    exec_stmt fe ge locals (nhe_empty_temps block offset) memory nhe_indexed_capture E0 prepared memory Out_normal /\
    prepared!31%positive=Some(Vint Int.zero) /\ prepared!32%positive=None.
Proof.
  intro READ; destruct (@nested_empty_capture_skips_child fe ge locals memory block offset (Int.repr(-1))
    READ ltac:(change (0<=0); lia)) as [prepared [RUN [CACHE [CHILD REST]]]].
  assert (WORD : Int.add(Int.repr(-1)) Int.one=Int.zero) by (apply Int.same_if_eq; vm_compute; reflexivity).
  rewrite WORD in CACHE; exists prepared; split; [exact RUN|split; assumption].
Qed.

Theorem nested_overflow_capture_skips_child fe ge locals memory block offset :
  Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint(Int.repr 2147483647)) -> exists prepared,
    exec_stmt fe ge locals (nhe_empty_temps block offset) memory nhe_indexed_capture E0 prepared memory Out_normal /\
    prepared!31%positive=Some(Vint(Int.repr(-2147483648))) /\ prepared!32%positive=None.
Proof.
  intro READ; destruct (@nested_empty_capture_skips_child fe ge locals memory block offset (Int.repr 2147483647))
    as [prepared [RUN [CACHE [CHILD REST]]]]; [exact READ|change (-2147483648<=0); lia|].
  assert (WORD : Int.add(Int.repr 2147483647) Int.one=Int.repr(-2147483648)) by (apply Int.same_if_eq; vm_compute; reflexivity).
  rewrite WORD in CACHE; exists prepared; split; [exact RUN|split; assumption].
Qed.

Definition nhe_alias_temps := PTree.set 20%positive (Vint Int.zero) lns_alias_temps.
Definition nhe_alias_source := nested_expression_source 20%positive (signed_load_offset 11%positive (Int.repr(-1)))
  1%positive (signed_load_offset 11%positive Int.one) lns_body.
Definition nhe_alias_capture := nested_expression_capture 20%positive 31%positive
  (signed_load_offset 11%positive (Int.repr(-1))) 32%positive (signed_load_offset 11%positive Int.one).

(** Both original loaded headers execute. The child initially appears to
    have three iterations; actual stores change its upper word and it stops
    at two. The actual outer loop performs one row. *)
Theorem nested_alias_original_executes fe ge locals : exists exit,
  exec_stmt fe ge locals nhe_alias_temps lbp_two_memory nhe_alias_source E0 exit loa_final Out_normal /\
  exit!20%positive=Some(Vint Int.one) /\ exit!1%positive=Some(Vint(Int.repr 2)).
Proof.
  pose proof (@offset_alias_original_stops_after_two fe ge locals) as INNER_SOURCE.
  pose (scope := statement_temps loa_source).
  assert (PRIVATE : ~In 20%positive scope) by (vm_compute; intuition congruence).
  destruct (@structured_execution_temp_transport fe ge locals lns_alias_temps lbp_two_memory loa_source
    E0 loa_exit loa_final Out_normal INNER_SOURCE scope nhe_alias_temps (statement_temps loa_source)
    (@check_plan_frameable_writes loa_source eq_refl) ltac:(unfold statement_scope,scope; apply incl_refl)
    (@temp_agree_set scope lns_alias_temps 20%positive (Vint Int.zero) PRIVATE))
    as [inner_after [INNER PUBLIC]].
  assert (ROOT_ROW : inner_after!20%positive=Some(Vint Int.zero)).
  { rewrite (@writes_only_frame _ _ _ _ _ _ _ _ _ _ INNER (statement_temps loa_source)
      (@check_plan_frameable_writes loa_source eq_refl) 20%positive PRIVATE); reflexivity. }
  assert (POINTER : inner_after!11%positive=Some(Vptr 1%positive Ptrofs.zero)).
  { rewrite PUBLIC by (vm_compute; intuition congruence); reflexivity. }
  assert (CHILD_ROW : inner_after!1%positive=Some(Vint(Int.repr 2))).
  { rewrite PUBLIC by (vm_compute; intuition congruence); reflexivity. }
  exists (PTree.set 20%positive (Vint Int.one) inner_after); split; [|split; [apply PTree.gss|rewrite PTree.gso by discriminate; exact CHILD_ROW]].
  unfold nhe_alias_source,nested_expression_source; eapply strict_iteration_encode with (body_temps:=inner_after) (body_memory:=loa_final).
  - change true with (Int.lt Int.zero (Int.add(Int.repr 2)(Int.repr(-1)))).
    apply signed_expression_test_eval; [reflexivity|reflexivity|].
    eapply signed_load_offset_eval; [reflexivity|exact lbp_concrete_read].
  - exists Int.zero; split; [exact ROOT_ROW|change (0<2147483647); lia].
  - unfold nested_expression_body; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
      (le1:=nhe_alias_temps) (m1:=lbp_two_memory); [|exact INNER].
    replace nhe_alias_temps with (PTree.set 1%positive (Vint Int.zero) nhe_alias_temps) at 2 by reflexivity.
    constructor; constructor.
  - unfold increment_temps; rewrite ROOT_ROW; change (Int.add Int.zero Int.one) with Int.one.
    apply signed_expression_zero_trip_execution.
    change false with (Int.lt Int.one (Int.add Int.one (Int.repr(-1)))).
    apply signed_expression_test_eval; [reflexivity|apply PTree.gss|].
    eapply signed_load_offset_eval; [rewrite PTree.gso by discriminate; exact POINTER|exact loa_final_read].
Qed.

Theorem nested_alias_capture_two_words fe ge locals : exists prepared_after,
  exec_stmt fe ge locals nhe_alias_temps lbp_two_memory nhe_alias_capture
    E0 (nested_expression_captured 31%positive 32%positive nhe_alias_temps Int.one (Some(Int.repr 3))) lbp_two_memory Out_normal /\
  exec_stmt fe ge locals (nested_expression_captured 31%positive 32%positive nhe_alias_temps Int.one (Some(Int.repr 3)))
    lbp_two_memory nhe_alias_source E0 prepared_after loa_final Out_normal.
Proof.
  destruct (@nested_alias_original_executes fe ge locals) as [exit [SOURCE REST]].
  destruct (@nested_expression_capture_execution fe ge locals nhe_alias_temps lbp_two_memory 20%positive
    (signed_load_offset 11%positive (Int.repr(-1))) 1%positive (signed_load_offset 11%positive Int.one) lns_body
    31%positive 32%positive [] exit loa_final eq_refl eq_refl eq_refl eq_refl
    ltac:(vm_compute; intuition congruence) ltac:(vm_compute; intuition congruence) ltac:(discriminate) ltac:(vm_compute; intuition congruence) SOURCE)
    as [upper [child [prepared_after [CAPTURE [PREPARED [PUBLIC [EVAL CHILD]]]]]]].
  assert (UPPER : upper=Int.one).
  { pose proof (@signed_load_offset_eval ge locals nhe_alias_temps lbp_two_memory 11%positive (Int.repr(-1))
      1%positive Ptrofs.zero (Int.repr 2) eq_refl lbp_concrete_read) as EXPECTED.
    pose proof (proj1(expressions_determinate ge locals nhe_alias_temps lbp_two_memory) _ _ EVAL _ EXPECTED) as SAME.
    assert (WORD : Int.add(Int.repr 2)(Int.repr(-1))=Int.one) by (apply Int.same_if_eq; vm_compute; reflexivity).
    rewrite WORD in SAME; congruence. }
  subst upper; destruct child as [word|]; [destruct CHILD as [ACTIVE CHILD_EVAL]|discriminate CHILD].
  assert (CHILD_WORD : word=Int.repr 3).
  { pose proof (@signed_load_offset_eval ge locals nhe_alias_temps lbp_two_memory 11%positive Int.one
      1%positive Ptrofs.zero (Int.repr 2) eq_refl lbp_concrete_read) as EXPECTED.
    pose proof (proj1(expressions_determinate ge locals nhe_alias_temps lbp_two_memory) _ _ CHILD_EVAL _ EXPECTED) as SAME.
    assert (WORD : Int.add(Int.repr 2) Int.one=Int.repr 3) by (apply Int.same_if_eq; vm_compute; reflexivity).
    rewrite WORD in SAME; congruence. }
  subst word; exists prepared_after; split; assumption.
Qed.

(** Numeric probing can run before cached-source derivation. The current
    parameters are integer words; future public controls and the output
    pointer are absent, so a cached source could not complete its stores. *)
Theorem captured_numeric_probe_executes_without_source fe ge locals memory : exists checked,
  exec_stmt fe ge locals lnf_active_temps memory (affine_package_guard_code (loaded_numeric_package lnf_site))
    E0 checked memory Out_normal /\
  checked!107%positive=Some(Vint Int.one) /\
  checked!2%positive=None /\ checked!3%positive=None /\ checked!5%positive=None /\ checked!10%positive=None /\
  affine_math_domain (affine_proposed_leaf_bounds lnf_proposal) (affine_proposal_layout lnf_proposal affine_memory_example_parameters)
    (affine_proposal_nest lnf_proposal) (affine_word_valuation lnf_active_temps)
    (affine_word_valuation lnf_active_temps (affine_proposed_iterator lnf_proposal)).
Proof.
  destruct (@affine_captured_package_guard_execution _ _ _ _ (loaded_numeric_package lnf_site) fe ge locals
    lnf_active_temps memory ltac:(exists Int.zero; reflexivity) ltac:(exists(Int.repr 2); reflexivity)
    ltac:(repeat constructor; first [exists(Int.repr 2); reflexivity|exists Int.one; reflexivity|exists Int.zero; reflexivity]))
    as [checked [RUN [FRAME [RESULT MATH]]]].
  rewrite nonempty_numeric_flag_accepts in RESULT.
  exists checked; split; [exact RUN|split; [exact RESULT|]].
  split; [rewrite FRAME by (vm_compute; intuition congruence); reflexivity|].
  split; [rewrite FRAME by (vm_compute; intuition congruence); reflexivity|].
  split; [rewrite FRAME by (vm_compute; intuition congruence); reflexivity|].
  split; [rewrite FRAME by (vm_compute; intuition congruence); reflexivity|].
  apply MATH,nonempty_numeric_flag_accepts.
Qed.

Print Assumptions nested_empty_capture_skips_child.
Print Assumptions nested_negative_one_capture_skips_child.
Print Assumptions nested_overflow_capture_skips_child.
Print Assumptions nested_alias_original_executes.
Print Assumptions nested_alias_capture_two_words.
Print Assumptions captured_numeric_probe_executes_without_source.

Theorem nested_alias_first_point_refuses ge locals :
  decision_run (Entry ge locals
    (nested_expression_captured 31%positive 32%positive nhe_alias_temps Int.one (Some(Int.repr 3))) lbp_two_memory)
    (word_address_separation (signed_pointer_temp 3%positive) 11%positive) false.
Proof.
  assert (TEST : expression_test (word_address_equal (signed_pointer_temp 3%positive) 11%positive)
    (Entry ge locals (nested_expression_captured 31%positive 32%positive nhe_alias_temps Int.one (Some(Int.repr 3))) lbp_two_memory) true).
  { change true with (address_flag 1%positive Ptrofs.zero 1%positive Ptrofs.zero).
    eapply word_address_equality_test; [reflexivity|constructor; reflexivity|reflexivity| |exact lbp_concrete_read].
    exact (@Mem.store_valid_access_3 Mint32 lbp_two_memory 1%positive 0(Vint Int.one) lbp_one_memory(proj2_sig lbp_one_memory_state)). }
  unfold word_address_separation; eapply run_test with (b:=true); [exact TEST|constructor].
Qed.
Print Assumptions nested_alias_first_point_refuses.

Definition nhe_child_empty_source := nested_expression_source 20%positive (signed_load_offset 21%positive (Int.repr(-1)))
  1%positive (signed_indexed_offset 21%positive Int.one (Int.repr(-1))) lns_body.
Definition nhe_child_empty_capture := nested_expression_capture 20%positive 31%positive
  (signed_load_offset 21%positive (Int.repr(-1))) 32%positive (signed_indexed_offset 21%positive Int.one (Int.repr(-1))).
Lemma nhe_indexed_child_read :
  Mem.loadv Mint32 lns_first (Vptr 1%positive (signed_indexed_address Ptrofs.zero Int.one))=Some(Vint Int.one).
Proof.
  change (Mem.load Mint32 lns_first 1%positive 4=Some(Vint Int.one)).
  exact (@Mem.load_store_same Mint32 lns_initial 1%positive 4(Vint Int.one) lns_first(proj2_sig lns_first_state)).
Qed.

Theorem nested_active_capture_reads_indexed_child fe ge locals : exists prepared_after,
  exec_stmt fe ge locals (nhe_empty_temps 1%positive Ptrofs.zero) lns_first nhe_child_empty_capture E0
    (nested_expression_captured 31%positive 32%positive (nhe_empty_temps 1%positive Ptrofs.zero) Int.one (Some Int.zero))
    lns_first Out_normal /\
  exec_stmt fe ge locals
    (nested_expression_captured 31%positive 32%positive (nhe_empty_temps 1%positive Ptrofs.zero) Int.one (Some Int.zero))
    lns_first nhe_child_empty_source E0 prepared_after lns_first Out_normal.
Proof.
  pose (initial := nhe_empty_temps 1%positive Ptrofs.zero).
  pose (after := PTree.set 20%positive(Vint Int.one)(PTree.set 1%positive(Vint Int.zero) initial)).
  assert (ROOT_WORD : Int.add(Int.repr 2)(Int.repr(-1))=Int.one) by (apply Int.same_if_eq; vm_compute; reflexivity).
  assert (CHILD_WORD : Int.add Int.one(Int.repr(-1))=Int.zero) by (apply Int.same_if_eq; vm_compute; reflexivity).
  assert (ROOT_EVAL : forall temps, temps!21%positive=Some(Vptr 1%positive Ptrofs.zero) ->
    eval_expr ge locals temps lns_first (signed_load_offset 21%positive (Int.repr(-1))) (Vint Int.one)).
  { intros temps POINTER; rewrite <-ROOT_WORD; eapply signed_load_offset_eval;
      [exact POINTER|exact(proj1(proj2 same_block_bound_reads))]. }
  assert (CHILD_EVAL : forall temps, temps!21%positive=Some(Vptr 1%positive Ptrofs.zero) ->
    eval_expr ge locals temps lns_first (signed_indexed_offset 21%positive Int.one (Int.repr(-1))) (Vint Int.zero)).
  { intros temps POINTER; rewrite <-CHILD_WORD; eapply signed_indexed_offset_eval; [exact POINTER|exact nhe_indexed_child_read]. }
  assert (SOURCE : exec_stmt fe ge locals initial lns_first nhe_child_empty_source E0 after lns_first Out_normal).
  { unfold nhe_child_empty_source,nested_expression_source; eapply strict_iteration_encode with
      (body_temps:=PTree.set 1%positive(Vint Int.zero) initial) (body_memory:=lns_first).
    - change true with(Int.lt Int.zero Int.one); apply signed_expression_test_eval;
        [reflexivity|reflexivity|apply ROOT_EVAL; reflexivity].
    - exists Int.zero; split; [reflexivity|change(0<2147483647); lia].
    - unfold nested_expression_body; eapply exec_Sseq_1 with (t1:=E0)(t2:=E0); [constructor; constructor|].
      apply signed_expression_zero_trip_execution; change false with(Int.lt Int.zero Int.zero).
      apply signed_expression_test_eval; [reflexivity|apply PTree.gss|apply CHILD_EVAL; reflexivity].
    - change (exec_stmt fe ge locals after lns_first (strict_frontend_loop 20%positive
        (signed_expression_test 20%positive(signed_load_offset 21%positive(Int.repr(-1))))
        (nested_expression_body 1%positive(signed_indexed_offset 21%positive Int.one(Int.repr(-1))) lns_body))
        E0 after lns_first Out_normal).
      apply signed_expression_zero_trip_execution; change false with(Int.lt Int.one Int.one).
      apply signed_expression_test_eval; [reflexivity|apply PTree.gss|apply ROOT_EVAL; reflexivity]. }
  destruct (@nested_expression_capture_execution fe ge locals initial lns_first 20%positive
    (signed_load_offset 21%positive(Int.repr(-1))) 1%positive (signed_indexed_offset 21%positive Int.one(Int.repr(-1)))
    lns_body 31%positive 32%positive [] after lns_first eq_refl eq_refl eq_refl eq_refl
    ltac:(vm_compute; intuition congruence) ltac:(vm_compute; intuition congruence) ltac:(discriminate)
    ltac:(vm_compute; intuition congruence) SOURCE)
    as [upper [child [prepared_after [CAPTURE [PREPARED [PUBLIC [EVAL CHILD]]]]]]].
  assert (UPPER : upper=Int.one).
  { pose proof (proj1(expressions_determinate ge locals initial lns_first) _ _ EVAL _ (ROOT_EVAL initial eq_refl)) as SAME; congruence. }
  subst upper; destruct child as [word|]; [destruct CHILD as [ACTIVE READ]|discriminate CHILD].
  assert (WORD : word=Int.zero).
  { pose proof (proj1(expressions_determinate ge locals initial lns_first) _ _ READ _ (CHILD_EVAL initial eq_refl)) as SAME; congruence. }
  subst word; exists prepared_after; split; assumption.
Qed.

Print Assumptions nhe_indexed_child_read.
Print Assumptions nested_active_capture_reads_indexed_child.
