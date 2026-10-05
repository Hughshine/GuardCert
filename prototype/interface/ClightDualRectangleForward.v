From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr ClightCountedLoop ClightFrontendLoopProtocol
  ClightLoopExecution ClightStraightLine ClightTempFrame ClightTempFootprint ClightProjectedExecution ClightLoopSyntax
  ClightRegionProgress ClightRectangularStore ClightRectangularGuard ClightRectangularLoops ClightRectangularRegion CompCertMemoryEquivalence.
From GuardInterface Require Import ClightReadonlyRewrite ClightLoadedBoundSyntax ClightStrictLoopProgress ClightStableLoopCondition
  ClightReadonlyLoadedTreeSynthesis ClightQuietDeterminacy ClightRegionBoundary ClightReadonlyProjectedCompiler
  ClightLoadedRectangleAtoms ClightLoadedRectangleMemory ClightLoadedRectangleForward
  ClightDualRectanglePrefix ClightDualRectangleGuard ClightDualRectangleLoop.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma dual_rect_private_scope d array row rows column columns body outer cache live :
  cache <> row -> cache <> rows -> cache <> column -> cache <> columns -> ~ In cache live ->
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body] ->
  ~ In cache (statement_temps (dual_rect_source row rows outer) ++ live).
Proof.
  intros CR CQ CC CM FRESH BODY OUTER.
  assert (BODY_SCOPE : ~ In cache (statement_temps body)).
  { rewrite <- (flatten_statement_temps body); rewrite BODY.
    cbn [concat map statement_temps expression_temps rect_store rect_lvalue rect_index rect_value].
    repeat rewrite loaded_rectangle_constant_temps; repeat rewrite in_app_iff; cbn; intuition congruence. }
  assert (OUTER_SCOPE : ~ In cache (statement_temps outer)).
  { rewrite <- (flatten_statement_temps outer); rewrite OUTER.
    cbn [concat map statement_temps expression_temps rectangle_reset loaded_bound_loop strict_frontend_loop
      loaded_bound_test signed_load signed_pointer_temp counter_increment]; repeat rewrite in_app_iff; cbn; intuition congruence. }
  cbn [dual_rect_source loaded_bound_loop strict_frontend_loop statement_temps expression_temps
    loaded_bound_test signed_load signed_pointer_temp counter_increment]; repeat rewrite in_app_iff; cbn; intuition congruence.
Qed.

Theorem dual_rect_domain_from_source d fe ge locals le memory array row rows column columns body outer after final :
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body] ->
  exec_stmt fe ge locals le memory (dual_rect_source row rows outer) E0 after final Out_normal ->
  dual_rect_domain row rows outer (Entry ge locals le memory).
Proof.
  intros BODY OUTER SOURCE; exists after,final; intro other; eapply (@quiet_execution_preserved fe other ge ge);
    [split; [reflexivity|intros; reflexivity]|exact SOURCE|].
  exact (@dual_rect_source_quiet d array row rows column columns body outer BODY OUTER).
Qed.

Theorem dual_rect_forward d (VALID : rectangle_layout_valid d) fe live
  array row rows column columns row_cache column_cache body outer entry observed :
  row <> column -> row <> rows -> row <> columns -> column <> rows -> column <> columns ->
  row_cache <> row -> row_cache <> rows -> row_cache <> column -> row_cache <> columns ->
  column_cache <> row -> column_cache <> rows -> column_cache <> column -> column_cache <> columns ->
  row_cache <> column_cache -> ~ In row_cache live -> ~ In column_cache live ->
  flatten_region body = [rect_store d array row column] ->
  flatten_region outer = [rectangle_reset column; loaded_bound_loop column columns body] ->
  dual_rect_domain row rows outer entry -> dual_rect_property d array row rows columns entry ->
  clight_fragment_run fe (dual_rect_source row rows outer) entry observed ->
  exists transformed, clight_fragment_run fe (dual_rect_candidate d array row rows column columns row_cache column_cache) entry transformed /\
    boundary_observe (public_exit_ports live) observed transformed.
Proof.
  intros RC RN RM CN CM CR CQ CC CK KR KQ KC KM DISTINCT FRESH FRESH2 BODY OUTER DOMAIN [SETUP ALIASES] SOURCE.
  destruct (proj2 (dual_rect_domain_entry DOMAIN)) as [upper [q [qo [Q READ]]]].
  destruct SETUP as [ZERO [NR [MR [width [r [ro [R READ2]]]]]]].
  pose proof (@dual_rect_word_known rows entry upper q qo Q READ) as NWORD.
  pose proof (@dual_rect_word_known columns entry width r ro R READ2) as MWORD.
  rewrite NWORD in NR; rewrite MWORD in MR.
  assert (ALIASES' : forall i j, 0 <= i < Int.signed upper -> 0 <= j < Int.signed width ->
    loaded_rectangle_alias_flag d array rows i j entry = false /\ loaded_rectangle_alias_flag d array columns i j entry = false).
  { intros i j IR JR; apply ALIASES; [rewrite NWORD|rewrite MWORD]; assumption. }
  clear ALIASES NWORD MWORD.
  destruct entry as [ge locals le memory], observed as [trace after final outcome]; cbn [entry_temps entry_memory] in Q,READ,R,READ2,ZERO.
  pose proof (@dual_rect_source_quiet d array row rows column columns body outer BODY OUTER) as QUIET.
  pose proof (@quiet_execution_silent fe ge locals le memory _ trace after final outcome SOURCE QUIET) as SILENT; subst trace.
  assert (NORMAL : outcome = Out_normal).
  { eapply normal_statement_execution; [|exact SOURCE].
    cbn [dual_rect_source loaded_bound_loop strict_frontend_loop normal_statement quiet_statement counter_increment] in QUIET |- *; exact QUIET. }
  subst outcome.
  destruct (@dual_rect_open_row fe ge locals le memory d array row rows column columns body outer 0 upper q qo after final
    BODY OUTER ltac:(lia) ZERO Q READ SOURCE) as [exit [mem [next [nextmem [INNER REST]]]]].
  assert (I0 : (PTree.set column (Vint Int.zero) le) ! row = Some (Vint (Int.repr 0))) by
    (rewrite PTree.gso by congruence; exact ZERO).
  assert (R0 : (PTree.set column (Vint Int.zero) le) ! columns = Some (Vptr r ro)) by
    (rewrite PTree.gso by congruence; exact R).
  destruct (@dual_rect_inner_step d VALID fe ge locals _ memory array row column columns body 0 0 width r ro exit mem
    RC BODY ltac:(pose proof (rectangle_limits VALID); lia) MR ltac:(lia) I0 (PTree.gss _ _ _) R0 READ2 INNER)
    as [block [middle [ARRAY PREFIX]]].
  assert (APART : forall i j, 0 <= i < Int.signed upper -> 0 <= j < Int.signed width ->
    Vptr block (loaded_rectangle_offset d i j) <> Vptr q qo /\ Vptr block (loaded_rectangle_offset d i j) <> Vptr r ro).
  { intros i j IR JR; destruct (ALIASES' i j IR JR) as [AQ AM]; split.
    - exact (@loaded_rectangle_alias_apart d array rows i j (Entry ge locals le memory) block q qo ARRAY Q AQ).
    - exact (@loaded_rectangle_alias_apart d array columns i j (Entry ge locals le memory) block r ro ARRAY R AM). }
  pose proof (@dual_rect_private_scope d array row rows column columns body outer row_cache live CR CQ CC CK FRESH BODY OUTER) as PRIVATE.
  pose proof (@dual_rect_private_scope d array row rows column columns body outer column_cache live KR KQ KC KM FRESH2 BODY OUTER) as PRIVATE2.
  set (target1 := PTree.set row_cache (Vint upper) le).
  set (target := PTree.set column_cache (Vint width) target1).
  assert (AGREE : temp_agree (statement_temps (dual_rect_source row rows outer) ++ live) le target).
  { eapply temp_agree_trans; [exact (@temp_agree_set _ le row_cache (Vint upper) PRIVATE)|].
    exact (@temp_agree_set _ target1 column_cache (Vint width) PRIVATE2). }
  destruct (@structured_execution_temp_transport fe ge locals le memory (dual_rect_source row rows outer)
    E0 after final Out_normal SOURCE (statement_temps (dual_rect_source row rows outer) ++ live) target [row;column]
    (@dual_rect_source_writes d array row rows column columns body outer BODY OUTER)
    ltac:(unfold statement_scope; intros id IN; apply in_or_app; left; exact IN) AGREE)
    as [target_after [TRANSPORT PUBLIC]].
  assert (INV : dual_rect_outer_snapshot (Int.signed upper) row rows columns row_cache column_cache upper width q qo r ro target memory).
  { exists 0; split; [lia|split; [unfold target,target1; rewrite !PTree.gso by congruence; exact ZERO|]].
    unfold dual_rect_values,target,target1; repeat split; repeat rewrite PTree.gso by congruence; auto using PTree.gss. }
  destruct (@dual_rect_outer_cached d VALID fe ge locals array row rows column columns row_cache column_cache body outer block q r qo ro upper width
    RC RN RM CN CM CR CC KR KC BODY OUTER ARRAY NR MR APART target memory E0 target_after final Out_normal INV TRANSPORT)
    as [CACHED AFTER].
  assert (TARGET_ROW : target ! row = Some (Vint Int.zero)) by (unfold target,target1; rewrite !PTree.gso by congruence; exact ZERO).
  assert (TARGET_ROWS : target ! row_cache = Some (Vint (Int.repr (Int.signed upper)))) by
    (unfold target,target1; rewrite PTree.gso by congruence; rewrite Int.repr_signed; apply PTree.gss).
  assert (TARGET_COLS : target ! column_cache = Some (Vint (Int.repr (Int.signed width)))) by
    (unfold target; rewrite Int.repr_signed; apply PTree.gss).
  pose proof (@rectangle_local d VALID array row row_cache column column_cache body
    (Ssequence (rectangle_reset column) (frontend_counted_loop column column_cache body))
    ltac:(congruence) RC CC ltac:(congruence) ltac:(congruence) BODY eq_refl fe ge locals target memory target_after final
    (Int.signed upper) (Int.signed width) TARGET_ROW TARGET_ROWS TARGET_COLS (Int.signed_range upper) (Int.signed_range width) NR MR CACHED) as SWAPPED.
  exists (FragmentObservation E0 target_after final Out_normal); split.
  - unfold clight_fragment_run,dual_rect_candidate; cbn.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := target1) (m1 := memory).
    + unfold target1; constructor; apply eval_Elvalue with (loc := q) (ofs := qo) (bf := Full).
      * apply eval_Ederef,eval_Etempvar; exact Q.
      * apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := target) (m1 := memory); [|exact SWAPPED].
      unfold target; constructor; apply eval_Elvalue with (loc := r) (ofs := ro) (bf := Full).
      * apply eval_Ederef,eval_Etempvar; unfold target1; rewrite PTree.gso by congruence; exact R.
      * apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ2].
  - unfold boundary_observe; cbn; split; [reflexivity|split; [reflexivity|split]].
    + eapply temp_agree_weaken; [|apply temp_agree_sym; exact PUBLIC]; intros id IN; apply in_or_app; right; exact IN.
    + apply memory_equivalent_refl.
Qed.
Print Assumptions dual_rect_private_scope.
Print Assumptions dual_rect_domain_from_source.
Print Assumptions dual_rect_forward.
