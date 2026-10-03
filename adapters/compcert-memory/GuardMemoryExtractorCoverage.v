From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Linalg Misc.
From polcert.src Require Import PolyBase.
From polcert.polygen Require Import Result.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryIndexedTrace GuardMemoryExtractorTrace GuardMemorySequencePolyhedral.
Import ListNotations.
Set Implicit Arguments.

Lemma memory_extracted_prefix_domain env_depth iterator_depth constraints instruction env suffix :
  MemoryExtractor.pi_has_lifted_prefix env_depth iterator_depth constraints instruction ->
  length env = (env_depth+iterator_depth)%nat ->
  length suffix = (PL.pi_depth instruction-iterator_depth)%nat ->
  in_poly (rev (rev suffix++env)) (PL.pi_poly instruction) = true ->
  in_poly env constraints = true.
Proof.
  intros [added [tail [DEPTH DOMAIN]]] LENGTH SUFFIX MEMBER.
  rewrite DOMAIN in MEMBER.
  assert (FULL : length (rev (rev suffix++env)) = (env_depth+PL.pi_depth instruction)%nat).
  { rewrite length_rev,length_app,length_rev,SUFFIX,LENGTH; lia. }
  apply MemoryExtractor.in_poly_normalize_affine_list_rev_app_inv in MEMBER as [BASE _]; [|exact FULL].
  rewrite rev_involutive in BASE.
  assert (ADDED : added = length (rev suffix)) by (rewrite length_rev,SUFFIX; lia).
  rewrite ADDED,MemoryExtractor.in_poly_lift_affine_list_n_app in BASE; exact BASE.
Qed.

Theorem memory_extractor_trace_coverage :
  (forall st constraints env_depth iterator_depth schedule instructions env base site instruction suffix,
    MemoryExtractor.extract_stmt st constraints env_depth iterator_depth schedule = Okk instructions ->
    length env = (env_depth+iterator_depth)%nat ->
    nth_error instructions site = Some instruction ->
    length suffix = (PL.pi_depth instruction-iterator_depth)%nat ->
    in_poly (rev (rev suffix++env)) (PL.pi_poly instruction) = true ->
    exists event, In event (indexed_memory_loop_trace base st env) /\
      indexed_event_site event = (base+site)%nat /\
      event_environment (indexed_event_payload event) = rev suffix++env) /\
  (forall sts constraints env_depth iterator_depth schedule position instructions env base site instruction suffix,
    MemoryExtractor.extract_stmts sts constraints env_depth iterator_depth schedule position = Okk instructions ->
    length env = (env_depth+iterator_depth)%nat ->
    nth_error instructions site = Some instruction ->
    length suffix = (PL.pi_depth instruction-iterator_depth)%nat ->
    in_poly (rev (rev suffix++env)) (PL.pi_poly instruction) = true ->
    exists event, In event (indexed_memory_list_trace base sts env) /\
      indexed_event_site event = (base+site)%nat /\
      event_environment (indexed_event_payload event) = rev suffix++env).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH constraints env_depth iterator_depth schedule instructions env base site instruction suffix
      EXTRACT LENGTH NTH SUFFIX DOMAIN.
    apply MemoryExtractor.extract_stmt_loop_success_inv in EXTRACT as [lower_constraint [upper_constraint [LOWER [UPPER EXTRACT]]]].
    assert (PREFIX : MemoryExtractor.pi_has_lifted_prefix env_depth (S iterator_depth)
      (MemoryExtractor.lift_affine_list constraints++[lower_constraint;upper_constraint]) instruction).
    { eapply MemoryExtractor.extract_stmt_has_lifted_prefix; [exact EXTRACT|eapply nth_error_In; exact NTH]. }
    destruct PREFIX as [added [tail [DEPTH POLY]]].
    destruct suffix as [|index suffix]; [cbn in SUFFIX; lia|].
    assert (CHILD_SUFFIX : length suffix = (PL.pi_depth instruction-S iterator_depth)%nat) by (cbn in SUFFIX; lia).
    assert (CHILD_ENV : length (index::env) = (env_depth+S iterator_depth)%nat) by (cbn; lia).
    assert (CHILD_DOMAIN : in_poly (rev (rev suffix++index::env)) (PL.pi_poly instruction) = true).
    { cbn [rev] in DOMAIN; rewrite <- app_assoc in DOMAIN; exact DOMAIN. }
    assert (BOUNDS : (L.eval_expr env lower <= index < L.eval_expr env upper)%Z).
    { assert (ALL : in_poly (index::env)
        (MemoryExtractor.lift_affine_list constraints++[lower_constraint;upper_constraint]) = true).
      { eapply memory_extracted_prefix_domain; [exists added,tail; split; [exact DEPTH|exact POLY]|exact CHILD_ENV|exact CHILD_SUFFIX|exact CHILD_DOMAIN]. }
      exact (proj2 (MemoryExtractor.loop_constraints_complete_lifted lower upper env _ constraints
        lower_constraint upper_constraint index LENGTH LOWER UPPER ALL)). }
    destruct (IH _ _ _ _ _ (index::env) base site instruction suffix EXTRACT CHILD_ENV NTH CHILD_SUFFIX CHILD_DOMAIN)
      as [event [MEMBER [SITE ENV]]].
    exists event; split.
    + cbn; apply in_flat_map; exists index; split; [apply Zrange_in; exact BOUNDS|exact MEMBER].
    + split; [exact SITE|]; rewrite ENV; cbn; rewrite <- app_assoc; reflexivity.
  - intros instruction arguments constraints env_depth iterator_depth schedule instructions env base site operation suffix
      EXTRACT LENGTH NTH SUFFIX DOMAIN.
    apply MemoryExtractor.extract_stmt_instr_success_inv in EXTRACT as [transformation [writes [reads [_ [_ EXTRACT]]]]].
    subst instructions; destruct site as [|site]; cbn in NTH; [inversion NTH; subst operation|destruct site; discriminate].
    cbn in SUFFIX; rewrite Nat.sub_diag in SUFFIX; destruct suffix; [|discriminate].
    exists (IndexedMemoryEvent base (MemoryLoopEvent instruction env (map (L.eval_expr env) arguments))).
    cbn; split; [auto|split; [lia|reflexivity]].
  - intros sts IH constraints env_depth iterator_depth schedule instructions env base site instruction suffix
      EXTRACT LENGTH NTH SUFFIX DOMAIN; cbn in EXTRACT; eapply IH; eassumption.
  - intros test body IH constraints env_depth iterator_depth schedule instructions env base site instruction suffix
      EXTRACT LENGTH NTH SUFFIX DOMAIN.
    apply MemoryExtractor.extract_stmt_guard_success_inv in EXTRACT as [test_constraints [TEST EXTRACT]].
    assert (GUARD : L.eval_test env test = true).
    { apply MemoryExtractor.test_to_aff_complete_normalized with (cols := (env_depth+iterator_depth)%nat) (constrs := test_constraints);
        [exact TEST|exact LENGTH|].
      assert (ALL : in_poly env (constraints++MemoryExtractor.normalize_affine_list (env_depth+iterator_depth)%nat test_constraints) = true).
      { eapply memory_extracted_prefix_domain; [eapply MemoryExtractor.extract_stmt_has_lifted_prefix; [exact EXTRACT|eapply nth_error_In; exact NTH]|exact LENGTH|exact SUFFIX|exact DOMAIN]. }
      rewrite in_poly_app in ALL; apply andb_prop in ALL; exact (proj2 ALL). }
    destruct (IH _ _ _ _ _ env base site instruction suffix EXTRACT LENGTH NTH SUFFIX DOMAIN) as [event [MEMBER REST]].
    exists event; split; [cbn; rewrite GUARD; exact MEMBER|exact REST].
  - intros constraints env_depth iterator_depth schedule position instructions env base site instruction suffix
      EXTRACT LENGTH NTH SUFFIX DOMAIN.
    apply MemoryExtractor.extract_stmts_nil_success_inv in EXTRACT; subst instructions; destruct site; discriminate.
  - intros st IH sts REST constraints env_depth iterator_depth schedule position instructions env base site instruction suffix
      EXTRACT LENGTH NTH SUFFIX DOMAIN.
    apply MemoryExtractor.extract_stmts_cons_success_inv in EXTRACT as [head [tail [HEAD [TAIL EXTRACT]]]].
    subst instructions; destruct (lt_dec site (length head)) as [LEFT|RIGHT].
    + rewrite nth_error_app1 in NTH by exact LEFT.
      destruct (IH _ _ _ _ _ env base site instruction suffix HEAD LENGTH NTH SUFFIX DOMAIN) as [event [MEMBER DETAILS]].
      exists event; split; [cbn; apply in_or_app; left; exact MEMBER|exact DETAILS].
    + rewrite nth_error_app2 in NTH by lia.
      destruct (REST _ _ _ _ _ _ env (base+memory_leaf_count st)%nat (site-length head)%nat instruction suffix
        TAIL LENGTH NTH SUFFIX DOMAIN) as [event [MEMBER [SITE ENV]]].
      exists event; split; [cbn; apply in_or_app; right; exact MEMBER|].
      split; [rewrite SITE; rewrite (memory_extractor_leaf_count HEAD) in RIGHT |- *; lia|exact ENV].
Qed.

Theorem memory_extracted_trace_coverage_iff st instructions env point :
  MemoryExtractor.extract_stmt st [] (length env) O [] = Okk instructions ->
  (In point (map (memory_extracted_event_point instructions) (indexed_memory_loop_trace O st env)) <->
   memory_sequence_valid_point (rev env) instructions point).
Proof.
  intro EXTRACT; split.
  - intro MEMBER; unfold memory_sequence_valid_point; rewrite length_rev.
    eapply memory_extracted_trace_point_valid; [exact EXTRACT|exact MEMBER].
  - intros [instruction [NTH [PREFIX [BELONG LENGTH]]]].
    rewrite length_rev in PREFIX,LENGTH.
    set (suffix := skipn (length env) (PL.ip_index point)).
    assert (INDEX : PL.ip_index point = rev env++suffix).
    { pose proof (firstn_skipn (length env) (PL.ip_index point)) as DECOMPOSE.
      rewrite PREFIX in DECOMPOSE; symmetry; exact DECOMPOSE. }
    assert (SUFFIX : length suffix = PL.pi_depth instruction).
    { unfold suffix; rewrite length_skipn,LENGTH; lia. }
    assert (DOMAIN : in_poly (rev (rev suffix++env)) (PL.pi_poly instruction) = true).
    { rewrite rev_app_distr,rev_involutive,<- INDEX; exact (proj1 BELONG). }
    destruct (proj1 memory_extractor_trace_coverage st [] (length env) O [] instructions env O
      (PL.ip_nth point) instruction suffix EXTRACT ltac:(lia) NTH
      ltac:(rewrite Nat.sub_0_r; exact SUFFIX) DOMAIN) as [event [MEMBER [SITE ENV]]].
    cbn in SITE.
    apply in_map_iff; exists event; split; [|exact MEMBER].
    unfold memory_extracted_event_point; rewrite SITE.
    assert (LOOKUP : nth (PL.ip_nth point) instructions memory_empty_poly_instruction = instruction)
      by (eapply nth_error_nth; exact NTH).
    rewrite LOOKUP; unfold memory_point_of_extracted_event; rewrite ENV,rev_app_distr,rev_involutive,<- INDEX.
    unfold PL.belongs_to in BELONG; destruct BELONG as [_ [TRANSFORM [STAMP [INSTRUCTION DEPTH]]]].
    destruct point; cbn in *; rewrite SITE,<- TRANSFORM,<- STAMP,<- INSTRUCTION,<- DEPTH; reflexivity.
Qed.
Print Assumptions memory_extractor_trace_coverage.
Print Assumptions memory_extracted_trace_coverage_iff.
