From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightSameAddress ClightTempFrame ClightTempFootprint
  ClightProjectedExecution ClightCountedLoop ClightFramedLoop ClightCountedProtocol
  ClightFrontendLoopProtocol ClightLoopExecution ClightLoopSyntax ClightRegionProgress
  ClightStraightLine ClightRedundantSet CompCertMemoryEquivalence.
From GuardInterface Require Import ClightReadonlyRewrite ClightRegionBoundary ClightReadonlyProjectedCompiler
  ClightCountedLocalization ClightStableLoadBody ClightStableLoadGuard ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition stable_load_candidate iterator bound out parameter cache :=
  Ssequence (Sset cache (word_load parameter))
    (frontend_counted_loop iterator bound (cached_load_body out cache iterator)).

Lemma stable_source_body_writes out parameter iterator body :
  flatten_region body = [stable_load_body out parameter iterator] -> writes_only [] body.
Proof. intro FLAT; apply flatten_writes_certificate; rewrite FLAT; constructor; [constructor|constructor]. Qed.

Lemma stable_source_body_normal out parameter iterator body :
  flatten_region body = [stable_load_body out parameter iterator] -> normal_statement body = true.
Proof. intro FLAT; apply flatten_normal_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. Qed.

Lemma stable_source_loop_quiet iterator bound out parameter body :
  flatten_region body = [stable_load_body out parameter iterator] ->
  quiet_statement (frontend_counted_loop iterator bound body) = true.
Proof.
  intro FLAT; assert (BODY : quiet_statement body = true).
  { apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. }
  cbn [frontend_counted_loop quiet_statement counter_increment]; rewrite BODY; reflexivity.
Qed.

Theorem stable_iterations_cached fe ge locals out parameter cache iterator body base b offset loaded count lower before final :
  flatten_region body = [stable_load_body out parameter iterator] ->
  iterator <> out -> iterator <> parameter -> cache <> out -> cache <> iterator ->
  base ! parameter = Some (Vptr b offset) -> base ! out <> base ! parameter ->
  counted_iterations (canonical_body_run fe ge locals body base iterator) count lower before final ->
  Mem.loadv Mint32 before (Vptr b offset) = Some loaded ->
  counted_iterations (canonical_body_run fe ge locals (cached_load_body out cache iterator)
    (PTree.set cache loaded base) iterator) count lower before final /\
  Mem.loadv Mint32 final (Vptr b offset) = Some loaded.
Proof.
  intros FLAT IO IQ CP CI PARAMETER APART POINTS; induction POINTS; intro READ.
  - split; [constructor|exact READ].
  - unfold canonical_body_run in H.
    apply (flattened_singleton_execution FLAT) in H.
    assert (Q : (PTree.set iterator (Vint (Int.repr x)) base) ! parameter = Some (Vptr b offset)).
    { rewrite PTree.gso by congruence; exact PARAMETER. }
    assert (DIFFERENT : (PTree.set iterator (Vint (Int.repr x)) base) ! out <>
      (PTree.set iterator (Vint (Int.repr x)) base) ! parameter).
    { repeat rewrite PTree.gso by congruence; exact APART. }
    pose proof (stable_load_body_preserves_parameter Q READ DIFFERENT H) as NEXT_READ.
    destruct (IHPOINTS NEXT_READ) as [TAIL LAST_READ].
    split; [econstructor; [|exact TAIL]|exact LAST_READ].
    unfold canonical_body_run; eapply stable_load_body_cached.
    + exact Q.
    + exact READ.
    + rewrite PTree.gso by congruence; apply PTree.gss.
    + apply temp_agree_set_both, temp_agree_set.
      cbn; intros [SAME|[SAME|BAD]]; congruence.
    + exact H.
Qed.

Theorem stable_load_forward fe live iterator bound out parameter cache body entry observed :
  iterator <> bound -> iterator <> out -> iterator <> parameter ->
  cache <> iterator -> cache <> bound -> cache <> out -> ~ In cache live ->
  flatten_region body = [stable_load_body out parameter iterator] ->
  stable_load_guard_domain iterator bound out parameter entry ->
  stable_load_guard_property iterator bound out parameter tt entry ->
  clight_fragment_run fe (frontend_counted_loop iterator bound body) entry observed ->
  exists transformed, clight_fragment_run fe (stable_load_candidate iterator bound out parameter cache) entry transformed /\
    boundary_observe (public_exit_ports live) observed transformed.
Proof.
  intros DISTINCT IO IQ CI CN CP FRESH FLAT [I [N DOMAIN]] [ZERO [ACTIVE APART]] SOURCE.
  destruct entry as [ge locals base memory], observed as [trace after final outcome].
  pose proof (@quiet_execution_silent fe ge locals base memory _ trace after final outcome
    SOURCE (@stable_source_loop_quiet iterator bound out parameter body FLAT)) as SILENT; subst trace.
  assert (NORMAL : normal_statement (frontend_counted_loop iterator bound body) = true).
  { cbn [normal_statement frontend_counted_loop].
    exact (@stable_source_loop_quiet iterator bound out parameter body FLAT). }
  pose proof (@normal_statement_execution fe ge locals _ NORMAL base memory E0 after final outcome SOURCE)
    as EXIT; subst outcome.
  destruct N as [upper UPPER].
  destruct (@counter_condition_active ge locals base memory iterator bound ACTIVE)
    as [index [other [INDEX [OTHER POSITIVE]]]].
  unfold register_equals in ZERO; cbn [entry_temps] in ZERO, UPPER.
  assert (INDEX_ZERO : index = Int.zero) by congruence; subst index.
  assert (UPPER_SAME : other = upper) by congruence; subst other.
  change (0 < Int.signed upper) in POSITIVE.
  destruct (proj2 (DOMAIN ZERO ACTIVE)) as [b [offset [loaded [PARAMETER READ]]]].
  cbn [entry_temps entry_memory] in PARAMETER, READ.
  assert (LENGTH : Int.signed upper = 0 + Z.of_nat (Z.to_nat (Int.signed upper))) by
    (rewrite Z2Nat.id by lia; lia).
  destruct (@counted_body_decode fe ge locals iterator bound body base memory after final
    (Z.to_nat (Int.signed upper)) 0 (Int.signed upper) DISTINCT
    (@stable_source_body_normal out parameter iterator body FLAT)
    (@stable_source_body_writes out parameter iterator body FLAT)
    ltac:(unfold signed_range; change (-2147483648 <= 0 <= 2147483647); lia)
    (Int.signed_range upper) LENGTH ZERO ltac:(rewrite Int.repr_signed; exact UPPER) SOURCE)
    as [POINTS PUBLIC_EXIT].
  destruct (@stable_iterations_cached fe ge locals out parameter cache iterator body base b offset loaded
    (Z.to_nat (Int.signed upper)) 0 memory final FLAT IO IQ CP CI PARAMETER APART POINTS READ)
    as [CACHED LAST_READ].
  assert (CANDIDATE : exec_stmt fe ge locals (PTree.set cache loaded base) memory
    (frontend_counted_loop iterator bound (cached_load_body out cache iterator)) E0
    (PTree.set iterator (Vint (Int.repr (Int.signed upper))) (PTree.set cache loaded base)) final Out_normal).
  { eapply counted_body_encode with (count := Z.to_nat (Int.signed upper)) (lower := 0) (upper := Int.signed upper);
      [exact DISTINCT|constructor| |apply Int.signed_range|exact LENGTH| | |exact CACHED].
    - unfold signed_range; change (-2147483648 <= 0 <= 2147483647); lia.
    - rewrite PTree.gso by congruence; exact ZERO.
    - rewrite PTree.gso by congruence; rewrite Int.repr_signed; exact UPPER. }
  exists (FragmentObservation E0
    (PTree.set iterator (Vint (Int.repr (Int.signed upper))) (PTree.set cache loaded base)) final Out_normal).
  split.
  - unfold clight_fragment_run, stable_load_candidate; cbn.
    replace E0 with (E0 ** E0) by reflexivity; eapply exec_Sseq_1; [|exact CANDIDATE].
    apply exec_Sset; apply eval_Elvalue with (loc := b) (ofs := offset) (bf := Full).
    + apply eval_Ederef, eval_Etempvar; exact PARAMETER.
    + apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
  - unfold boundary_observe; cbn; split; [reflexivity|split; [reflexivity|split]].
    + rewrite PUBLIC_EXIT; apply temp_agree_set_both, temp_agree_sym, temp_agree_set; exact FRESH.
    + apply memory_equivalent_refl.
Qed.

Print Assumptions stable_iterations_cached.
Print Assumptions stable_load_forward.
