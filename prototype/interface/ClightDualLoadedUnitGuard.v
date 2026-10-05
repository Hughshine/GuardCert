From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightNoWrap
  ClightSameAddress ClightRedundantSet ClightMatrixGuard ClightPureExpr ClightDecisionRule ClightRegionProgress
  ClightCountedLoop ClightCountedProtocol ClightStraightLine ClightLoopSyntax ClightTempFrame.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ReadonlyConditionComposition
  ClightConditionComposition ClightReadonlyLoadedTreeSynthesis ClightStrictIteration ClightLoadedBoundSyntax ClightLoadedBoundGuard
  ClightReadonlyCellSwap ClightStableLoadGuard ClightDualLoadedUnitSyntax ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.

Definition dual_unit_domain row rows outer entry := exists after final,
  forall fe, exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (dual_unit_source row rows outer) E0 after final Out_normal.
Definition loaded_word_domain parameter entry := exists word b ofs,
  (entry_temps entry) ! parameter = Some (Vptr b ofs) /\
  Mem.loadv Mint32 (entry_memory entry) (Vptr b ofs) = Some (Vint word).
Definition loaded_one parameter entry := exists b ofs,
  (entry_temps entry) ! parameter = Some (Vptr b ofs) /\
  Mem.loadv Mint32 (entry_memory entry) (Vptr b ofs) = Some (Vint Int.one).
Definition loaded_one_expr parameter := Ebinop Oeq (signed_load parameter) (Econst_int Int.one type_int32s) type_int32s.
Definition dual_unit_premise row rows columns out entry :=
  register_equals row Int.zero tt entry /\
    (loaded_one rows entry /\ (loaded_one columns entry /\
      (cell_pair_apart out rows entry /\ cell_pair_apart out columns entry))).
Definition dual_unit_guard row rows columns out :=
  Test (register_guard row Int.zero)
    (Test (loaded_one_expr rows)
      (Test (loaded_one_expr columns)
        (Test (same_address_guard out rows) (Decision false)
          (Test (same_address_guard out columns) (Decision false) (Decision true)))
        (Decision false)) (Decision false)) (Decision false).

Lemma loaded_one_expr_test parameter entry word b ofs :
  (entry_temps entry) ! parameter = Some (Vptr b ofs) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr b ofs) = Some (Vint word) ->
  expression_test (loaded_one_expr parameter) entry (Int.eq word Int.one).
Proof.
  destruct entry as [ge locals le memory]; intros P READ; exists (Val.of_bool (Int.eq word Int.one)); split.
  - unfold loaded_one_expr; eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint Int.one); [|constructor|reflexivity].
    apply eval_Elvalue with (loc := b) (ofs := ofs) (bf := Full).
    + apply eval_Ederef, eval_Etempvar; exact P.
    + apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
  - apply bool_of_bool.
Qed.
Lemma loaded_one_expr_sound parameter entry : loaded_word_domain parameter entry ->
  expression_test (loaded_one_expr parameter) entry true -> loaded_one parameter entry.
Proof.
  intros [word [b [ofs [P READ]]]] TEST.
  pose proof (@loaded_one_expr_test parameter entry word b ofs P READ) as KNOWN.
  assert (ONE : Int.eq word Int.one = true) by (eapply readonly_test_determinate; [exact KNOWN|exact TEST]).
  apply Int.same_if_eq in ONE; subst word; exists b,ofs; auto.
Qed.
Lemma dual_unit_domain_entry row rows outer entry : dual_unit_domain row rows outer entry ->
  register_domain row entry /\ loaded_word_domain rows entry.
Proof.
  destruct entry as [ge locals le memory]; intros [after [final SOURCE]].
  destruct (@loaded_source_head (fun _ _ _ _ _ _ _ => False) ge locals row rows outer le memory after final (SOURCE _))
    as [flag TEST].
  destruct (loaded_bound_test_facts TEST) as [x [upper [b [ofs [I [Q [READ _]]]]]]].
  split; [exists x; exact I|exists upper,b,ofs; auto].
Qed.

Section PREFIX.
Variables row rows column columns out : ident.
Variables body outer : statement.
Hypothesis CJ : column <> columns.
Hypothesis CP : column <> out.
Hypothesis BODY : flatten_region body = [dual_unit_store out].
Hypothesis OUTER : flatten_region outer = [dual_unit_reset column; loaded_bound_loop column columns body].

Lemma dual_unit_inner_prefix fe ge locals le memory :
  dual_unit_domain row rows outer (Entry ge locals le memory) ->
  expression_test (loaded_bound_test row rows) (Entry ge locals le memory) true ->
  exists after final, exec_stmt fe ge locals (PTree.set column (Vint Int.zero) le) memory
    (loaded_bound_loop column columns body) E0 after final Out_normal.
Proof.
  intros [after [final SOURCE]] ACTIVE.
  destruct (@strict_active_iteration fe ge locals row (loaded_bound_test row rows) outer le memory after final
    (@dual_unit_outer_normal out column columns body outer BODY OUTER)
    (@dual_unit_outer_quiet out column columns body outer BODY OUTER) ACTIVE (SOURCE fe))
    as [middle [mem [next [nextmem [RUN _]]]]].
  apply (@flattened_pair_execution fe ge locals outer (dual_unit_reset column)
    (loaded_bound_loop column columns body) le memory middle mem OUTER) in RUN;
    destruct (sequence_normal_decode RUN) as [reset [resetmem [RESET INNER]]].
  inversion RESET; subst; match goal with V : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
    apply scalar_const_inv in V; subst end.
  eexists; eexists; exact INNER.
Qed.
Lemma dual_unit_outer_active ge locals le memory :
  dual_unit_domain row rows outer (Entry ge locals le memory) ->
  register_equals row Int.zero tt (Entry ge locals le memory) -> loaded_one rows (Entry ge locals le memory) ->
  expression_test (loaded_bound_test row rows) (Entry ge locals le memory) true.
Proof.
  intros _ I [b [ofs [Q READ]]].
  change true with (Int.lt Int.zero Int.one); eapply loaded_bound_test_eval; eassumption.
Qed.
Lemma dual_unit_columns_domain ge locals le memory :
  dual_unit_domain row rows outer (Entry ge locals le memory) ->
  register_equals row Int.zero tt (Entry ge locals le memory) -> loaded_one rows (Entry ge locals le memory) ->
  loaded_word_domain columns (Entry ge locals le memory).
Proof.
  intros DOMAIN ZERO ONE.
  destruct (@dual_unit_inner_prefix (fun _ _ _ _ _ _ _ => False) ge locals le memory DOMAIN
    (dual_unit_outer_active DOMAIN ZERO ONE)) as [after [final RUN]].
  destruct (loaded_source_head RUN) as [flag TEST].
  destruct (loaded_bound_test_facts TEST) as [x [upper [b [ofs [I [Q [READ _]]]]]]].
  exists upper,b,ofs; cbn [entry_temps entry_memory] in Q, READ |- *; rewrite PTree.gso in Q by congruence; auto.
Qed.
Lemma dual_unit_first_store (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop) ge locals le memory :
  dual_unit_domain row rows outer (Entry ge locals le memory) ->
  register_equals row Int.zero tt (Entry ge locals le memory) -> loaded_one rows (Entry ge locals le memory) ->
  loaded_one columns (Entry ge locals le memory) ->
  exists b ofs final, le ! out = Some (Vptr b ofs) /\
    Mem.storev Mint32 memory (Vptr b ofs) (Vint (Int.repr 2)) = Some final.
Proof.
  intros DOMAIN ZERO ONE [q [qofs [Q READ]]].
  destruct (@dual_unit_inner_prefix fe ge locals le memory DOMAIN (dual_unit_outer_active DOMAIN ZERO ONE))
    as [after [final RUN]].
  assert (ACTIVE : expression_test (loaded_bound_test column columns)
    (Entry ge locals (PTree.set column (Vint Int.zero) le) memory) true).
  { change true with (Int.lt Int.zero Int.one); eapply loaded_bound_test_eval;
      [apply PTree.gss|rewrite PTree.gso by congruence; exact Q|exact READ]. }
  assert (NORMAL : normal_statement body = true) by
    (apply flatten_normal_certificate; rewrite BODY; constructor; [reflexivity|constructor]).
  destruct (@strict_active_iteration fe ge locals column (loaded_bound_test column columns) body _ memory after final
    NORMAL (@dual_unit_body_quiet out body BODY) ACTIVE RUN) as [middle [mem [next [nextmem [STORE _]]]]].
  apply (flattened_singleton_execution BODY) in STORE.
  destruct (dual_unit_store_decode STORE) as [b [ofs [P [_ RAW]]]].
  exists b,ofs,mem; rewrite PTree.gso in P by congruence; auto.
Qed.
Lemma dual_unit_address_domains entry : dual_unit_domain row rows outer entry ->
  register_equals row Int.zero tt entry -> loaded_one rows entry -> loaded_one columns entry ->
  address_domain out rows entry /\ address_domain out columns entry.
Proof.
  destruct entry as [ge locals le memory]; intros DOMAIN ZERO ONE TWO.
  destruct (@dual_unit_first_store (fun _ _ _ _ _ _ _ => False) ge locals le memory DOMAIN ZERO ONE TWO)
    as [p [po [final [P STORE]]]].
  destruct ONE as [q [qo [Q READ]]], TWO as [r [ro [R READ2]]].
  assert (VP : Mem.valid_pointer memory p (Ptrofs.unsigned po) = true)
    by (apply writable_word_valid_pointer; exact (proj1 (@storev_word_facts _ _ _ _ _ STORE))).
  split; [exists p,po,q,qo|exists p,po,r,ro]; repeat split; try assumption;
    eapply loaded_address_valid; eassumption.
Qed.
End PREFIX.

Definition loaded_one_condition fe O (observe : fragment_observation -> O -> Prop) parameter domain
  (DEFINED : forall entry, domain entry -> loaded_word_domain parameter entry) :
  readonly_condition (readonly_clight_host fe observe) domain (loaded_one parameter)
    (Test (loaded_one_expr parameter) (Decision true) (Decision false)).
Proof.
  apply readonly_expression_condition.
  - intros entry DOMAIN; destruct (DEFINED entry DOMAIN) as [word [b [ofs [P READ]]]].
    exists (Int.eq word Int.one); eapply loaded_one_expr_test; eassumption.
  - intros entry DOMAIN TEST; apply loaded_one_expr_sound; [apply DEFINED; exact DOMAIN|exact TEST].
Defined.
Definition address_apart_condition fe O (observe : fragment_observation -> O -> Prop) p q domain
  (DEFINED : forall entry, domain entry -> address_domain p q entry) :
  readonly_condition (readonly_clight_host fe observe) domain (cell_pair_apart p q)
    (Test (same_address_guard p q) (Decision false) (Decision true)).
Proof.
  constructor.
  - intros entry DOMAIN; apply readonly_decision_run_safe with (answer := negb (address_accept p q entry)).
    eapply run_test; [apply (proj2 (@address_guard_correct p q entry _ (DEFINED entry DOMAIN))); reflexivity|].
    destruct (address_accept p q entry); constructor.
  - intros entry DOMAIN; exists (negb (address_accept p q entry)), entry; split; [|reflexivity].
    eapply run_test; [apply (proj2 (@address_guard_correct p q entry _ (DEFINED entry DOMAIN))); reflexivity|].
    destruct (address_accept p q entry); constructor.
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    inversion RUN; subst.
    match goal with LEAF : decision_run _ (if ?b then Decision false else Decision true) true |- _ =>
      destruct b; inversion LEAF; subst end.
    apply stable_addresses_apart; [apply DEFINED; exact DOMAIN|].
    apply negb_true_iff; symmetry; apply (proj1 (@address_guard_correct p q entry false (DEFINED entry DOMAIN))); assumption.
Defined.

Definition dual_unit_condition fe O (observe : fragment_observation -> O -> Prop) row rows column columns out body outer
  (CJ : column <> columns) (CP : column <> out)
  (BODY : flatten_region body = [dual_unit_store out])
  (OUTER : flatten_region outer = [dual_unit_reset column; loaded_bound_loop column columns body]) :
  readonly_condition (readonly_clight_host fe observe) (dual_unit_domain row rows outer)
    (dual_unit_premise row rows columns out) (dual_unit_guard row rows columns out).
Proof.
  unfold dual_unit_guard, dual_unit_premise.
  change (readonly_condition (readonly_clight_host fe observe) (dual_unit_domain row rows outer)
    (fun entry => register_equals row Int.zero tt entry /\
      (loaded_one rows entry /\ (loaded_one columns entry /\ (cell_pair_apart out rows entry /\ cell_pair_apart out columns entry))))
    (then_check (clight_readonly_check_algebra fe observe)
      (Test (register_guard row Int.zero) (Decision true) (Decision false))
      (Test (loaded_one_expr rows) (Test (loaded_one_expr columns)
        (Test (same_address_guard out rows) (Decision false)
          (Test (same_address_guard out columns) (Decision false) (Decision true))) (Decision false)) (Decision false)))).
  apply sequence_readonly_conditions.
  - apply readonly_expression_condition.
    + intros entry DOMAIN; exists (register_flag row Int.zero entry); apply register_expression_test;
        exact (proj1 (dual_unit_domain_entry DOMAIN)).
    + intros entry DOMAIN TEST; pose proof (proj1 (dual_unit_domain_entry DOMAIN)) as REG.
      apply register_flag_evidence; [exact REG|].
      eapply readonly_test_determinate; [apply register_expression_test; exact REG|exact TEST].
  - change (readonly_condition (readonly_clight_host fe observe)
      (fun entry => dual_unit_domain row rows outer entry /\ register_equals row Int.zero tt entry)
      (fun entry => loaded_one rows entry /\ (loaded_one columns entry /\
        (cell_pair_apart out rows entry /\ cell_pair_apart out columns entry)))
      (then_check (clight_readonly_check_algebra fe observe)
        (Test (loaded_one_expr rows) (Decision true) (Decision false))
        (Test (loaded_one_expr columns) (Test (same_address_guard out rows) (Decision false)
          (Test (same_address_guard out columns) (Decision false) (Decision true))) (Decision false)))).
    apply sequence_readonly_conditions.
    + apply loaded_one_condition; intros entry [DOMAIN _]; exact (proj2 (dual_unit_domain_entry DOMAIN)).
    + change (readonly_condition (readonly_clight_host fe observe)
        (fun entry => (dual_unit_domain row rows outer entry /\ register_equals row Int.zero tt entry) /\ loaded_one rows entry)
        (fun entry => loaded_one columns entry /\ (cell_pair_apart out rows entry /\ cell_pair_apart out columns entry))
        (then_check (clight_readonly_check_algebra fe observe)
          (Test (loaded_one_expr columns) (Decision true) (Decision false))
          (Test (same_address_guard out rows) (Decision false)
            (Test (same_address_guard out columns) (Decision false) (Decision true))))).
      apply sequence_readonly_conditions.
      * apply loaded_one_condition; intros [ge locals le memory] [[DOMAIN ZERO] ONE].
        exact (@dual_unit_columns_domain row rows column columns out body outer BODY OUTER ge locals le memory DOMAIN ZERO ONE).
      * change (readonly_condition (readonly_clight_host fe observe)
          (fun entry => ((dual_unit_domain row rows outer entry /\ register_equals row Int.zero tt entry) /\ loaded_one rows entry) /\ loaded_one columns entry)
          (fun entry => cell_pair_apart out rows entry /\ cell_pair_apart out columns entry)
          (then_check (clight_readonly_check_algebra fe observe)
            (Test (same_address_guard out rows) (Decision false) (Decision true))
            (Test (same_address_guard out columns) (Decision false) (Decision true)))).
        apply sequence_readonly_conditions.
        -- apply address_apart_condition; intros entry [[[DOMAIN ZERO] ONE] TWO].
           exact (proj1 (@dual_unit_address_domains row rows column columns out body outer CJ CP BODY OUTER entry DOMAIN ZERO ONE TWO)).
        -- apply address_apart_condition; intros entry [[[[DOMAIN ZERO] ONE] TWO] _].
           exact (proj2 (@dual_unit_address_domains row rows column columns out body outer CJ CP BODY OUTER entry DOMAIN ZERO ONE TWO)).
Defined.

Print Assumptions loaded_one_expr_sound.
Print Assumptions dual_unit_columns_domain.
Print Assumptions dual_unit_first_store.
Print Assumptions dual_unit_address_domains.
Print Assumptions dual_unit_condition.
