From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightSameAddress ClightTempFrame ClightTempFootprint
  ClightProjectedExecution ClightCountedLoop ClightFramedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightLoopExecution ClightLoopSyntax ClightRegionProgress
  ClightStraightLine ClightRedundantSet CompCertMemoryEquivalence.
From GuardInterface Require Import ClightReadonlyRewrite ClightRegionBoundary ClightReadonlyProjectedCompiler
  ClightCountedLocalization ClightIndexedLoadBody ClightIndexedLoadDomain ClightIndexedAliasGuard ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition indexed_load_candidate iterator bound out parameter cache :=
  Ssequence (Sset cache (word_load parameter))
    (frontend_counted_loop iterator bound (indexed_cached_body out cache iterator)).
Lemma indexed_loop_quiet out parameter iterator bound body :
  flatten_region body = [indexed_load_body out parameter iterator] ->
  quiet_statement (frontend_counted_loop iterator bound body) = true.
Proof. intro FLAT; cbn [frontend_counted_loop quiet_statement counter_increment];
  rewrite (@indexed_source_quiet out parameter iterator body FLAT); reflexivity. Qed.

Theorem indexed_iterations_cached fe ge locals out parameter cache iterator body base block offset q qofs loaded count lower before final :
  flatten_region body = [indexed_load_body out parameter iterator] ->
  iterator <> out -> iterator <> parameter -> cache <> out -> cache <> iterator ->
  base ! out = Some (Vptr block offset) -> base ! parameter = Some (Vptr q qofs) ->
  counted_iterations (canonical_body_run fe ge locals body base iterator) count lower before final ->
  (forall k, lower <= k < lower+Z.of_nat count ->
    Vptr block (indexed_word_offset offset (Int.repr k)) <> Vptr q qofs) ->
  Mem.loadv Mint32 before (Vptr q qofs) = Some loaded ->
  counted_iterations (canonical_body_run fe ge locals (indexed_cached_body out cache iterator)
    (PTree.set cache loaded base) iterator) count lower before final /\
  Mem.loadv Mint32 final (Vptr q qofs) = Some loaded.
Proof.
  intros FLAT IO IQ CP CI OUT PARAMETER POINTS; induction POINTS; intros APART READ.
  - split; [constructor|exact READ].
  - unfold canonical_body_run in H; apply (flattened_singleton_execution FLAT) in H.
    assert (P : (PTree.set iterator (Vint (Int.repr x)) base) ! out = Some (Vptr block offset)) by
      (rewrite PTree.gso by congruence; exact OUT).
    assert (Q : (PTree.set iterator (Vint (Int.repr x)) base) ! parameter = Some (Vptr q qofs)) by
      (rewrite PTree.gso by congruence; exact PARAMETER).
    pose proof (@indexed_load_body_preserves_parameter fe ge locals _ s0 out parameter iterator
      (Int.repr x) block offset q qofs loaded s1 (PTree.gss _ _ _) P Q READ
      ltac:(apply APART; rewrite Nat2Z.inj_succ; lia) H) as NEXT_READ.
    destruct (IHPOINTS ltac:(intros k RANGE; apply APART; rewrite Nat2Z.inj_succ; lia) NEXT_READ) as [TAIL LAST_READ].
    split; [econstructor; [|exact TAIL]|exact LAST_READ].
    unfold canonical_body_run; eapply indexed_load_body_cached.
    + exact Q.
    + exact READ.
    + rewrite PTree.gso by congruence; apply PTree.gss.
    + apply temp_agree_set_both, temp_agree_set; cbn; intros [SAME|[SAME|BAD]]; congruence.
    + exact H.
Qed.

Theorem indexed_load_forward fe live iterator bound out parameter cache body cap entry observed :
  iterator <> bound -> iterator <> out -> iterator <> parameter ->
  cache <> iterator -> cache <> bound -> cache <> out -> ~ In cache live ->
  flatten_region body = [indexed_load_body out parameter iterator] ->
  indexed_load_domain iterator bound out parameter entry ->
  indexed_guard_property iterator bound out parameter cap tt entry ->
  clight_fragment_run fe (frontend_counted_loop iterator bound body) entry observed ->
  exists transformed, clight_fragment_run fe (indexed_load_candidate iterator bound out parameter cache) entry transformed /\
    boundary_observe (public_exit_ports live) observed transformed.
Proof.
  intros DISTINCT IO IQ CI CN CP FRESH FLAT [I [N DOMAIN]] [ZERO [[ND RANGE] APART]] SOURCE.
  destruct entry as [ge locals base memory], observed as [trace after final outcome].
  pose proof (@quiet_execution_silent fe ge locals base memory _ trace after final outcome
    SOURCE (@indexed_loop_quiet out parameter iterator bound body FLAT)) as SILENT; subst trace.
  assert (NORMAL : normal_statement (frontend_counted_loop iterator bound body) = true).
  { exact (@indexed_loop_quiet out parameter iterator bound body FLAT). }
  pose proof (@normal_statement_execution fe ge locals _ NORMAL base memory E0 after final outcome SOURCE) as EXIT; subst outcome.
  destruct N as [upper UPPER].
  destruct (DOMAIN ZERO (proj1 RANGE)) as [block [offset [q [qofs [loaded [OUT [PARAMETER [READ WORDS]]]]]]]].
  cbn [entry_temps entry_memory] in ZERO, UPPER, RANGE, APART, OUT, PARAMETER, READ.
  unfold temp_word in RANGE, APART; rewrite UPPER in RANGE, APART.
  assert (LENGTH : Int.signed upper = 0 + Z.of_nat (Z.to_nat (Int.signed upper))) by (rewrite Z2Nat.id by lia; lia).
  destruct (@counted_body_decode fe ge locals iterator bound body base memory after final
    (Z.to_nat (Int.signed upper)) 0 (Int.signed upper) DISTINCT
    (@indexed_source_normal out parameter iterator body FLAT) (@indexed_source_writes out parameter iterator body FLAT)
    ltac:(unfold signed_range; change (-2147483648 <= 0 <= 2147483647); lia)
    (Int.signed_range upper) LENGTH ZERO ltac:(rewrite Int.repr_signed; exact UPPER) SOURCE) as [POINTS PUBLIC_EXIT].
  assert (SEPARATE : forall k, 0 <= k < 0 + Z.of_nat (Z.to_nat (Int.signed upper)) ->
    Vptr block (indexed_word_offset offset (Int.repr k)) <> Vptr q qofs).
  { intros k POINT; rewrite Z2Nat.id in POINT by lia.
    exact (@indexed_alias_apart out parameter k (Entry ge locals base memory) block offset q qofs OUT PARAMETER
      (APART k ltac:(cbn in POINT; exact POINT))). }
  destruct (@indexed_iterations_cached fe ge locals out parameter cache iterator body base block offset q qofs loaded
    (Z.to_nat (Int.signed upper)) 0 memory final FLAT IO IQ CP CI OUT PARAMETER POINTS SEPARATE READ) as [CACHED LAST_READ].
  assert (CANDIDATE : exec_stmt fe ge locals (PTree.set cache loaded base) memory
    (frontend_counted_loop iterator bound (indexed_cached_body out cache iterator)) E0
    (PTree.set iterator (Vint (Int.repr (Int.signed upper))) (PTree.set cache loaded base)) final Out_normal).
  { eapply counted_body_encode with (count := Z.to_nat (Int.signed upper)) (lower := 0) (upper := Int.signed upper);
      [exact DISTINCT|constructor| |apply Int.signed_range|exact LENGTH| | |exact CACHED].
    - unfold signed_range; change (-2147483648 <= 0 <= 2147483647); lia.
    - rewrite PTree.gso by congruence; exact ZERO.
    - rewrite PTree.gso by congruence; rewrite Int.repr_signed; exact UPPER. }
  exists (FragmentObservation E0 (PTree.set iterator (Vint (Int.repr (Int.signed upper)))
    (PTree.set cache loaded base)) final Out_normal); split.
  - unfold clight_fragment_run, indexed_load_candidate; cbn.
    replace E0 with (E0 ** E0) by reflexivity; eapply exec_Sseq_1; [|exact CANDIDATE].
    apply exec_Sset; apply eval_Elvalue with (loc := q) (ofs := qofs) (bf := Full).
    + apply eval_Ederef, eval_Etempvar; exact PARAMETER.
    + apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
  - unfold boundary_observe; cbn; split; [reflexivity|split; [reflexivity|split]].
    + rewrite PUBLIC_EXIT; apply temp_agree_set_both, temp_agree_sym, temp_agree_set; exact FRESH.
    + apply memory_equivalent_refl.
Qed.
Print Assumptions indexed_iterations_cached.
Print Assumptions indexed_load_forward.
