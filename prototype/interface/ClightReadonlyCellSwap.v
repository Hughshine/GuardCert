From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Maps Coqlib.
From compcert.common Require Import AST Values Memory Events Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Csyntax Csem Clight ClightBigstep.
From compcert.x86 Require Import Asm.
From Guard Require Import AbstractGuard SemanticFacts ClightGuard ClightCondition ClightPureExpr
  ClightPositiveCheck ClightDecisionRule ClightNoWrap ClightSameAddress ClightRegionProgress ClightStraightLine ClightLoopExecution
  ClightSyntaxEquality ClightLoopSyntax ClightProgressClassifier CompCertStoreSchedule.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyTreeSynthesis ClightQuietDeterminacy ClightLoopBridge ClightReadonlyCompiler
  ClightAdministrative ClightPreloadCompiler.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition cell_store pointer value := Sassign (word_load pointer) (Econst_int value type_int32u).
Definition cell_pair p q first second := Ssequence (cell_store p first) (cell_store q second).
Definition writable_word memory block offset :=
  Mem.valid_access memory Mint32 block (Ptrofs.unsigned offset) Writable /\
  Ptrofs.unsigned offset + 4 <= Ptrofs.modulus.
Definition cell_pair_domain p q entry := exists b1 ofs1 b2 ofs2,
  (entry_temps entry) ! p = Some (Vptr b1 ofs1) /\
  (entry_temps entry) ! q = Some (Vptr b2 ofs2) /\
  writable_word (entry_memory entry) b1 ofs1 /\ writable_word (entry_memory entry) b2 ofs2.
Definition cell_pair_apart p q entry := (entry_temps entry) ! p <> (entry_temps entry) ! q.
Definition cell_pair_accept p q entry := negb (address_accept p q entry).
Definition cell_pair_test p q := Test (same_address_guard p q) (Decision false) (Decision true).

Lemma writable_word_valid_pointer memory block offset : writable_word memory block offset ->
  Mem.valid_pointer memory block (Ptrofs.unsigned offset) = true.
Proof.
  intros [[PERM ALIGN] BOUND]; apply Mem.valid_pointer_nonempty_perm.
  eapply Mem.perm_implies; [apply PERM; change (size_chunk Mint32) with 4; lia|constructor].
Qed.

Lemma cell_pair_address_domain p q entry : cell_pair_domain p q entry -> address_domain p q entry.
Proof.
  intros [b1 [ofs1 [b2 [ofs2 [P [Q [FIRST SECOND]]]]]]].
  exists b1, ofs1, b2, ofs2; repeat split; auto using writable_word_valid_pointer.
Qed.

Lemma cell_pair_accept_sound p q entry : cell_pair_domain p q entry ->
  cell_pair_accept p q entry = true -> cell_pair_apart p q entry.
Proof.
  intros [b1 [ofs1 [b2 [ofs2 [P [Q REST]]]]]] ACCEPT SAME.
  assert (EQ : Vptr b1 ofs1 = Vptr b2 ofs2) by congruence; inversion EQ; subst.
  unfold cell_pair_accept, address_accept, address_flag in ACCEPT; rewrite P, Q in ACCEPT.
  rewrite Pos.eqb_refl, Ptrofs.eq_true in ACCEPT; discriminate.
Qed.

Definition cell_pair_dimension p q : property_dimension clight_entry unit (cell_pair_domain p q).
Proof.
  refine {| atom_property := fun _ => cell_pair_apart p q;
    decide_atom := fun _ entry => Some (cell_pair_accept p q entry) |}.
  intros [] entry accepted DOMAIN DECIDE; injection DECIDE as SAME; subst accepted.
  destruct (cell_pair_accept p q entry) eqn:RESULT; cbn [decision_evidence].
  - exact (cell_pair_accept_sound DOMAIN RESULT).
  - unfold cell_pair_accept in RESULT; apply negb_false_iff in RESULT.
    destruct (address_accept_sound p q entry RESULT) as [value [P Q]].
    intro APART; apply APART; congruence.
Defined.

Lemma cell_pair_test_exact p q entry accepted : cell_pair_domain p q entry ->
  (decision_run entry (cell_pair_test p q) accepted <-> accepted = cell_pair_accept p q entry).
Proof.
  intro DOMAIN.
  assert (RUN : decision_run entry (cell_pair_test p q) (cell_pair_accept p q entry)).
  { unfold cell_pair_test, cell_pair_accept; eapply run_test.
    - apply (proj2 (@address_guard_correct p q entry (address_accept p q entry)
        (cell_pair_address_domain DOMAIN))); reflexivity.
    - destruct (address_accept p q entry); constructor. }
  split; [intro OTHER; eapply (@pure_tree_determinate (cell_pair_test p q));
    [repeat constructor|exact OTHER|exact RUN]|].
  intro SAME; subst accepted; exact RUN.
Qed.

Definition cell_pair_primitives p q : check_primitives decision_test_language (cell_pair_domain p q)
  (decide_atom (cell_pair_dimension p q)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_test_language (cell_pair_domain p q)
    (decide_atom (cell_pair_dimension p q)) (fun _ => Decision true) (fun _ => cell_pair_test p q) _ _).
  - intros [] entry accepted DOMAIN; cbn [decision_test_language checked_valid cell_pair_dimension decide_atom].
    split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst accepted; constructor].
  - intros [] entry accepted expected DOMAIN DECIDE; cbn [cell_pair_dimension decide_atom] in DECIDE.
    injection DECIDE as SAME; subst expected; apply cell_pair_test_exact; exact DOMAIN.
Defined.

Theorem known_cell_alias_negation p q entry : cell_pair_domain p q entry ->
  (entry_temps entry) ! p = (entry_temps entry) ! q ->
  formula_accepts (decide_atom (cell_pair_dimension p q)) (Complement (Fact tt)) entry = true.
Proof.
  intros DOMAIN SAME; cbn [cell_pair_dimension decide_atom formula_accepts formula_execute].
  destruct (cell_pair_accept p q entry) eqn:RESULT; [|reflexivity].
  exfalso; apply (cell_pair_accept_sound DOMAIN RESULT); exact SAME.
Qed.

Definition cell_pair_tree p q := synthesize_decision_tree (cell_pair_primitives p q) (Fact tt).
Definition cell_pair_condition fe p q : readonly_condition (readonly_clight_host fe (@eq fragment_observation))
  (cell_pair_domain p q) (cell_pair_apart p q) (cell_pair_tree p q).
Proof.
  apply synthesized_scalar_tree_condition with (D := cell_pair_dimension p q) (premise := Fact tt).
  - intros []; repeat constructor.
  - intros []; repeat constructor.
Defined.

Lemma distinct_aligned_words_disjoint memory b1 ofs1 b2 ofs2 first second :
  writable_word memory b1 ofs1 -> writable_word memory b2 ofs2 -> Vptr b1 ofs1 <> Vptr b2 ofs2 ->
  stores_disjoint (StoreAction Mint32 b1 (Ptrofs.unsigned ofs1) first)
    (StoreAction Mint32 b2 (Ptrofs.unsigned ofs2) second).
Proof.
  intros [[VALID1 ALIGN1] BOUND1] [[VALID2 ALIGN2] BOUND2] DIFFERENT.
  change (4 | Ptrofs.unsigned ofs1) in ALIGN1; change (4 | Ptrofs.unsigned ofs2) in ALIGN2.
  unfold stores_disjoint; cbn [action_block action_offset action_chunk size_chunk].
  destruct (peq b1 b2) as [SAME|DISTINCT]; [subst b2|auto].
  assert (OFFSETS : Ptrofs.unsigned ofs1 <> Ptrofs.unsigned ofs2).
  { intro EQ; apply DIFFERENT; f_equal; rewrite <- (Ptrofs.repr_unsigned ofs1), <- (Ptrofs.repr_unsigned ofs2); congruence. }
  destruct ALIGN1 as [x X], ALIGN2 as [y Y]; right; lia.
Qed.

Lemma cell_store_encode fe ge locals temps memory p value block offset final :
  temps ! p = Some (Vptr block offset) ->
  Mem.storev Mint32 memory (Vptr block offset) (Vint value) = Some final ->
  exec_stmt fe ge locals temps memory (cell_store p value) E0 temps final Out_normal.
Proof.
  intros POINTER STORE; unfold cell_store, word_load, pointer_temp.
  eapply exec_Sassign with (v := Vint value) (v2 := Vint value) (bf := Full).
  - apply eval_Ederef; constructor; exact POINTER.
  - constructor.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|exact STORE].
Qed.

Lemma cell_store_decode fe ge locals temps memory p value trace after final out :
  exec_stmt fe ge locals temps memory (cell_store p value) trace after final out ->
  exists block offset, temps ! p = Some (Vptr block offset) /\ trace = E0 /\ after = temps /\
    out = Out_normal /\ Mem.storev Mint32 memory (Vptr block offset) (Vint value) = Some final.
Proof.
  unfold cell_store, word_load, pointer_temp; intro RUN; inversion RUN; subst.
  match goal with LVALUE : eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ => inversion LVALUE; subst end.
  match goal with POINTER : eval_expr _ _ _ _ (Etempvar _ _) _ |- _ => apply scalar_temp_inv in POINTER end.
  match goal with VALUE : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply scalar_const_inv in VALUE; subst end.
  match goal with CAST : sem_cast _ _ _ _ = Some _ |- _ => inversion CAST; subst end.
  match goal with STORE : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion STORE; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  eexists; eexists; repeat split; eauto.
Qed.

Lemma storev_word_facts memory block offset value final :
  Mem.storev Mint32 memory (Vptr block offset) value = Some final ->
  writable_word memory block offset /\ Mem.store Mint32 memory block (Ptrofs.unsigned offset) value = Some final.
Proof.
  cbn [Mem.storev]; destruct (zle (Ptrofs.unsigned offset + size_chunk Mint32) Ptrofs.modulus) as [BOUND|]; [|discriminate].
  intro STORE; split; [split; [eapply Mem.store_valid_access_3; exact STORE|exact BOUND]|exact STORE].
Qed.

Lemma word_storev_from_store memory block offset value final :
  writable_word memory block offset ->
  Mem.store Mint32 memory block (Ptrofs.unsigned offset) value = Some final ->
  Mem.storev Mint32 memory (Vptr block offset) value = Some final.
Proof.
  intros [VALID BOUND] STORE; cbn [Mem.storev]; rewrite zle_true by exact BOUND; exact STORE.
Qed.

Lemma cell_pair_decode fe p q first second entry observed :
  clight_fragment_run fe (cell_pair p q first second) entry observed ->
  exists b1 ofs1 b2 ofs2 middle,
    (entry_temps entry) ! p = Some (Vptr b1 ofs1) /\
    (entry_temps entry) ! q = Some (Vptr b2 ofs2) /\
    observed = FragmentObservation E0 (entry_temps entry) (fragment_memory observed) Out_normal /\
    Mem.storev Mint32 (entry_memory entry) (Vptr b1 ofs1) (Vint first) = Some middle /\
    Mem.storev Mint32 middle (Vptr b2 ofs2) (Vint second) = Some (fragment_memory observed).
Proof.
  destruct entry as [ge locals temps memory], observed as [trace after final out]; cbn; intro RUN.
  cbn [clight_fragment_run] in RUN.
  pose proof (@quiet_execution_silent fe ge locals temps memory (cell_pair p q first second)
    trace after final out RUN eq_refl) as SILENT; subst trace.
  pose proof (@normal_statement_execution fe ge locals (cell_pair p q first second)
    eq_refl temps memory E0 after final out RUN) as NORMAL; subst out.
  destruct (sequence_normal_decode RUN) as [middle_temps [middle [FIRST SECOND]]].
  destruct (cell_store_decode FIRST) as [b1 [ofs1 [P [_ [TEMPS [_ STORE1]]]]]]; cbn in TEMPS; subst middle_temps.
  destruct (cell_store_decode SECOND) as [b2 [ofs2 [Q [_ [TEMPS [_ STORE2]]]]]]; cbn in TEMPS; subst after.
  exists b1, ofs1, b2, ofs2, middle; auto.
Qed.

Lemma cell_pair_source_domain fe p q first second entry observed :
  clight_fragment_run fe (cell_pair p q first second) entry observed -> cell_pair_domain p q entry.
Proof.
  intro RUN; destruct (cell_pair_decode RUN) as [b1 [ofs1 [b2 [ofs2 [middle [P [Q [EXIT [FIRST SECOND]]]]]]]]].
  destruct (@storev_word_facts _ _ _ _ _ FIRST) as [[VALID1 BOUND1] STORE1].
  destruct (@storev_word_facts _ _ _ _ _ SECOND) as [[VALID2 BOUND2] STORE2].
  exists b1, ofs1, b2, ofs2; split; [exact P|split; [exact Q|split]].
  - split; assumption.
  - split; [eapply Mem.store_valid_access_2; eassumption|exact BOUND2].
Qed.

Lemma cell_pair_forward fe p q first second entry observed :
  cell_pair_domain p q entry -> cell_pair_apart p q entry ->
  clight_fragment_run fe (cell_pair p q first second) entry observed ->
  clight_fragment_run fe (cell_pair q p second first) entry observed.
Proof.
  intros DOMAIN APART RUN.
  destruct (cell_pair_decode RUN) as [b1 [ofs1 [b2 [ofs2 [middle [P [Q [EXIT [FIRST SECOND]]]]]]]]].
  destruct (@storev_word_facts _ _ _ _ _ FIRST) as [SAFE1 STORE1].
  destruct (@storev_word_facts _ _ _ _ _ SECOND) as [[VALID2 BOUND2] STORE2].
  assert (SAFE2 : writable_word (entry_memory entry) b2 ofs2).
  { split; [eapply Mem.store_valid_access_2; eassumption|exact BOUND2]. }
  assert (DISTINCT : Vptr b1 ofs1 <> Vptr b2 ofs2) by (intro SAME; apply APART; rewrite P, Q, SAME; reflexivity).
  destruct (@disjoint_stores_reorder (StoreAction Mint32 b1 (Ptrofs.unsigned ofs1) (Vint first))
    (StoreAction Mint32 b2 (Ptrofs.unsigned ofs2) (Vint second)) (entry_memory entry) middle (fragment_memory observed)
    (@distinct_aligned_words_disjoint _ _ _ _ _ (Vint first) (Vint second) SAFE1 SAFE2 DISTINCT)
    STORE1 STORE2) as [swapped [SWAP2 SWAP1]].
  rewrite EXIT; unfold clight_fragment_run, cell_pair; cbn; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - eapply cell_store_encode; [exact Q|apply word_storev_from_store; [exact SAFE2|exact SWAP2]].
  - eapply cell_store_encode; [exact P|apply word_storev_from_store; [|exact SWAP1]].
    split; [eapply Mem.store_valid_access_1; [exact SWAP2|exact (proj1 SAFE1)]|exact (proj2 SAFE1)].
Qed.

Definition cell_pair_rule p q first second : readonly_clight_rule (cell_pair p q first second).
Proof.
  refine {| readonly_candidate := cell_pair q p second first; readonly_guard := cell_pair_tree p q;
    readonly_domain := cell_pair_domain p q; readonly_premise := cell_pair_apart p q |}.
  - intro temps; apply cell_pair_condition.
  - intros temps entry observed [DOMAIN APART]; split.
    + intros [raw [RUN SAME]]; subst raw; exists observed; split; [|reflexivity].
      apply cell_pair_forward with (p := q) (q := p); [|congruence|exact RUN].
      destruct DOMAIN as [b1 [ofs1 [b2 [ofs2 [P [Q [FIRST SECOND]]]]]]].
      exists b2, ofs2, b1, ofs1; auto.
    + intros [raw [RUN SAME]]; subst raw; exists observed; split; [|reflexivity].
      apply cell_pair_forward; assumption.
  - intros temps p0 e le m le' m' RUN.
    eapply cell_pair_source_domain with (observed := FragmentObservation E0 le' m' Out_normal); exact RUN.
Defined.

Definition propose_cell_pair source : option ((ident * Int.int) * (ident * Int.int)) :=
  match source with
  | Ssequence (Sassign (Ederef (Etempvar p _) _) (Econst_int first _))
      (Sassign (Ederef (Etempvar q _) _) (Econst_int second _)) => Some ((p,first),(q,second))
  | _ => None end.

Definition choose_cell_pair_normalized source : option (readonly_clight_rule source).
Proof.
  destruct (propose_cell_pair source) as [[[p first] [q second]]|]; [|exact None].
  destruct (statement_eq source (cell_pair p q first second)) as [SAME|DIFFERENT]; [|exact None].
  rewrite SAME; exact (Some (cell_pair_rule p q first second)).
Defined.

Definition choose_cell_pair source := match choose_cell_pair_normalized (trim_skips source) with
  | Some rule => Some (trim_readonly_rule source rule) | None => None end.
Definition compile_readonly_cell_pairs := compile_readonly_rewrites choose_cell_pair progress_supported.
Theorem compile_readonly_cell_pairs_correct p target :
  compile_readonly_cell_pairs p = OK target -> backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply compile_readonly_rewrites_correct, progress_supported_sound. Qed.

Print Assumptions cell_pair_condition.
Print Assumptions known_cell_alias_negation.
Print Assumptions distinct_aligned_words_disjoint.
Print Assumptions cell_pair_source_domain.
Print Assumptions cell_pair_forward.
Print Assumptions cell_pair_rule.
Print Assumptions compile_readonly_cell_pairs_correct.
