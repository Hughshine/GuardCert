From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightMatrixGuard ClightCondition ClightNoWrap ClightRedundantSet ClightPureExpr ClightSameAddress
  ClightCountedLoop ClightCountedProtocol ClightZeroTrip ClightFrontendLoopProtocol ClightFrontendRegion ClightLoopExecution ClightLoopSyntax
  ClightStraightLine ClightTempFrame ClightRegionProgress.
From GuardInterface Require Import ClightReadonlyCellSwap ClightCountedLocalization ClightIndexedLoadBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma indexed_source_writes out parameter iterator body :
  flatten_region body = [indexed_load_body out parameter iterator] -> writes_only [] body.
Proof. intro FLAT; apply flatten_writes_certificate; rewrite FLAT; repeat constructor. Qed.
Lemma indexed_source_normal out parameter iterator body :
  flatten_region body = [indexed_load_body out parameter iterator] -> normal_statement body = true.
Proof. intro FLAT; apply flatten_normal_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. Qed.
Lemma indexed_source_quiet out parameter iterator body :
  flatten_region body = [indexed_load_body out parameter iterator] -> quiet_statement body = true.
Proof. intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. Qed.

Theorem indexed_iterations_writable fe ge locals out parameter iterator body base block offset count lower before final :
  flatten_region body = [indexed_load_body out parameter iterator] -> iterator <> out ->
  base ! out = Some (Vptr block offset) ->
  counted_iterations (canonical_body_run fe ge locals body base iterator) count lower before final ->
  forall k, lower <= k < lower + Z.of_nat count ->
  writable_word before block (indexed_word_offset offset (Int.repr k)).
Proof.
  intros FLAT IO OUT POINTS; induction POINTS; intros k RANGE.
  - cbn in RANGE; lia.
  - unfold canonical_body_run in H; apply (flattened_singleton_execution FLAT) in H.
    destruct (@indexed_load_body_facts fe ge locals (PTree.set iterator (Vint (Int.repr x)) base)
      s0 out parameter iterator (Int.repr x) _ s1 (PTree.gss _ _ _) H)
      as [b [ofs [q [qofs [loaded [stored [P [Q [LOAD STORE]]]]]]]]].
    rewrite PTree.gso in P by congruence.
    assert (SAME : Vptr b ofs = Vptr block offset) by congruence; injection SAME; intros; subst.
    destruct (@storev_word_facts _ _ _ _ _ STORE) as [WORD RAW].
    destruct (Z.eq_dec k x) as [EQUAL|LATER]; [subst k; exact WORD|].
    assert (TAIL : x + 1 <= k < x + 1 + Z.of_nat n) by (rewrite Nat2Z.inj_succ in RANGE; lia).
    destruct (IHPOINTS k TAIL) as [VALID BOUND]; split; [|exact BOUND].
    eapply Mem.store_valid_access_2; [exact RAW|exact VALID].
Qed.

Definition indexed_load_domain iterator bound out parameter entry :=
  register_domain iterator entry /\ register_domain bound entry /\
  (register_equals iterator Int.zero tt entry -> 0 < Int.signed (temp_word bound (entry_temps entry)) ->
    exists block offset q qofs loaded,
      (entry_temps entry) ! out = Some (Vptr block offset) /\
      (entry_temps entry) ! parameter = Some (Vptr q qofs) /\
      Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some loaded /\
      forall k, 0 <= k < Int.signed (temp_word bound (entry_temps entry)) ->
        writable_word (entry_memory entry) block (indexed_word_offset offset (Int.repr k))).

Theorem indexed_load_domain_from_source fe ge locals le memory iterator bound out parameter body after final :
  iterator <> bound -> iterator <> out -> iterator <> parameter ->
  flatten_region body = [indexed_load_body out parameter iterator] ->
  exec_stmt fe ge locals le memory (frontend_counted_loop iterator bound body) E0 after final Out_normal ->
  indexed_load_domain iterator bound out parameter (Entry ge locals le memory).
Proof.
  intros IN IO IQ FLAT SOURCE.
  destruct (@frontend_entry_test fe ge locals le memory iterator bound body after final SOURCE) as [flag TEST].
  destruct (@counter_test_domain iterator bound (Entry ge locals le memory) flag TEST) as [i [n [I N]]].
  split; [exists i; exact I|split; [exists n; exact N|]].
  intros ZERO POS; cbn [entry_temps entry_memory] in *; unfold temp_word in POS; rewrite N in POS.
  assert (LENGTH : Int.signed n = 0 + Z.of_nat (Z.to_nat (Int.signed n))) by (rewrite Z2Nat.id by lia; lia).
  destruct (@counted_body_decode fe ge locals iterator bound body le memory after final
    (Z.to_nat (Int.signed n)) 0 (Int.signed n) IN
    (@indexed_source_normal out parameter iterator body FLAT) (@indexed_source_writes out parameter iterator body FLAT)
    ltac:(unfold signed_range; change (-2147483648 <= 0 <= 2147483647); lia)
    (Int.signed_range n) LENGTH ZERO ltac:(rewrite Int.repr_signed; exact N) SOURCE) as [POINTS EXIT].
  assert (NONEMPTY : Z.to_nat (Int.signed n) <> 0%nat).
  { intro EMPTY; pose proof (Z2Nat.id (Int.signed n) ltac:(lia)); rewrite EMPTY in H; cbn in H; lia. }
  assert (FIRST : exists middle, canonical_body_run fe ge locals body le iterator 0 memory middle).
  { inversion POINTS; subst.
    - congruence.
    - eexists; eassumption. }
  destruct FIRST as [middle FIRST]; unfold canonical_body_run in FIRST.
  apply (flattened_singleton_execution FLAT) in FIRST.
  destruct (@indexed_load_body_facts fe ge locals (PTree.set iterator (Vint (Int.repr 0)) le)
    memory out parameter iterator (Int.repr 0) _ middle (PTree.gss _ _ _) FIRST)
    as [block [offset [q [qofs [loaded [stored [P [Q [LOAD STORE]]]]]]]]].
  rewrite PTree.gso in P by congruence; rewrite PTree.gso in Q by congruence.
  exists block, offset, q, qofs, loaded; split; [exact P|split; [exact Q|split; [exact LOAD|]]].
  intros k RANGE; unfold temp_word in RANGE; rewrite N in RANGE.
  eapply indexed_iterations_writable; [exact FLAT|exact IO|exact P|exact POINTS|].
  rewrite Z2Nat.id by lia; cbn; exact RANGE.
Qed.
Print Assumptions indexed_iterations_writable.
Print Assumptions indexed_load_domain_from_source.
