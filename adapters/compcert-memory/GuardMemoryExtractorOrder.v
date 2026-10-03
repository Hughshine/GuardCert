From Stdlib Require Import List ZArith Lia Sorting.Sorted.
From polcert.lib Require Import Linalg Misc.
From polcert.src Require Import Base PolyBase.
From polcert.polygen Require Import Result.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryLoopTrace GuardMemoryIndexedTrace
  GuardMemoryExtractorTrace GuardMemoryExtractorCoverage GuardMemoryTraceUniqueness
  GuardMemoryPolyhedralRectangles GuardMemoryTiledRectangles GuardMemorySequenceOrder.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_local_extracted_event_point base instructions event :=
  memory_point_of_extracted_event
    (nth (indexed_event_site event-base)%nat instructions memory_empty_poly_instruction) event.

Lemma memory_local_point_append_left base head tail event :
  (indexed_event_site event-base < length head)%nat ->
  memory_local_extracted_event_point base (head++tail) event = memory_local_extracted_event_point base head event.
Proof. intro BOUND; unfold memory_local_extracted_event_point; rewrite app_nth1 by exact BOUND; reflexivity. Qed.
Lemma memory_local_point_append_right base head tail event :
  (base+length head <= indexed_event_site event)%nat ->
  memory_local_extracted_event_point base (head++tail) event =
    memory_local_extracted_event_point (base+length head)%nat tail event.
Proof.
  intro BOUND; unfold memory_local_extracted_event_point; rewrite app_nth2 by lia.
  replace (indexed_event_site event-base-length head)%nat with
    (indexed_event_site event-(base+length head))%nat by lia; reflexivity.
Qed.

Lemma memory_extracted_timestamp_prefix instruction event env env_depth iterator_depth schedule :
  MemoryExtractor.pi_has_lifted_sched_prefix env_depth iterator_depth schedule instruction ->
  length env = (env_depth+iterator_depth)%nat ->
  length (event_environment (indexed_event_payload event)) = (env_depth+PL.pi_depth instruction)%nat ->
  (exists prefix, event_environment (indexed_event_payload event) = prefix++env) ->
  exists suffix, PL.ip_time_stamp (memory_point_of_extracted_event instruction event) =
    affine_product schedule env++suffix.
Proof.
  intros [added [tail [DEPTH SCHEDULE]]] LENGTH FULL [prefix ENV].
  assert (ADDED : added = length prefix) by (rewrite ENV,length_app,LENGTH in FULL; lia).
  exists (affine_product tail (event_environment (indexed_event_payload event))).
  change (affine_product (PL.pi_schedule instruction) (rev (event_environment (indexed_event_payload event))) =
    affine_product schedule env ++ affine_product tail (event_environment (indexed_event_payload event))).
  rewrite SCHEDULE,MemoryExtractor.normalize_affine_list_rev_affine_product
    by (rewrite length_rev; exact FULL).
  rewrite rev_involutive,MemoryExtractor.affine_product_app,ENV,ADDED.
  rewrite MemoryExtractor.affine_product_lift_affine_list_n_app; reflexivity.
Qed.

Theorem memory_extracted_stmt_timestamp_prefix st constraints env_depth iterator_depth schedule instructions env base event :
  MemoryExtractor.extract_stmt st constraints env_depth iterator_depth schedule = Okk instructions ->
  length env = (env_depth+iterator_depth)%nat -> in_poly env constraints = true ->
  In event (indexed_memory_loop_trace base st env) ->
  exists suffix, PL.ip_time_stamp (memory_local_extracted_event_point base instructions event) =
    affine_product schedule env++suffix.
Proof.
  intros EXTRACT LENGTH DOMAIN MEMBER.
  destruct (proj1 memory_extractor_trace_metadata st constraints env_depth iterator_depth schedule instructions env base event
    EXTRACT LENGTH DOMAIN MEMBER) as [instruction [NTH [_ [FULL _]]]].
  assert (LOOKUP : nth (indexed_event_site event-base)%nat instructions memory_empty_poly_instruction = instruction)
    by (eapply nth_error_nth; exact NTH).
  unfold memory_local_extracted_event_point; rewrite LOOKUP.
  eapply memory_extracted_timestamp_prefix; [|exact LENGTH|exact FULL|].
  - eapply MemoryExtractor.extract_stmt_has_lifted_sched_prefix; [exact EXTRACT|eapply nth_error_In; exact NTH].
  - exact (proj1 indexed_memory_environment_extension st base env event MEMBER).
Qed.

Lemma memory_strongly_sorted_flat_map_on {A B} (R : B -> B -> Prop) (Q : A -> A -> Prop) f xs :
  StronglySorted Q xs -> (forall x, In x xs -> StronglySorted R (f x)) ->
  (forall x y first second, In x xs -> In y xs -> Q x y -> In first (f x) -> In second (f y) -> R first second) ->
  StronglySorted R (flat_map f xs).
Proof.
  intros ORDER; induction ORDER as [|x xs ORDER IH NEXT]; intros INNER CROSS; cbn; [constructor|].
  apply memory_strongly_sorted_append.
  - apply INNER; cbn; auto.
  - apply IH.
    + intros y MEMBER; apply INNER; right; exact MEMBER.
    + intros a b first second LEFT_IN RIGHT_IN REL FIRST SECOND.
      eapply CROSS; [right; exact LEFT_IN|right; exact RIGHT_IN|exact REL|exact FIRST|exact SECOND].
  - intros first second FIRST SECOND; apply in_flat_map in SECOND as [y [MEMBER SECOND]].
    apply (CROSS x y first second); [left; reflexivity|right; exact MEMBER|exact (proj1 (Forall_forall _ _) NEXT y MEMBER)|exact FIRST|exact SECOND].
Qed.
Lemma memory_timestamp_prefix_lt prefix first second left right :
  first < second -> lex_compare (prefix++first::left) (prefix++second::right) = Lt.
Proof.
  intro ORDER; induction prefix; cbn; [|rewrite Z.compare_refl; exact IHprefix].
  rewrite (proj2 (Z.compare_lt_iff first second) ORDER); reflexivity.
Qed.

Lemma memory_local_head_points st base env head tail :
  length head = memory_leaf_count st ->
  map (memory_local_extracted_event_point base (head++tail)) (indexed_memory_loop_trace base st env) =
    map (memory_local_extracted_event_point base head) (indexed_memory_loop_trace base st env).
Proof.
  intro LENGTH; apply map_ext_in; intros event MEMBER; apply memory_local_point_append_left.
  rewrite LENGTH; pose proof (proj1 indexed_memory_site_bounds_contracts st base env event MEMBER); lia.
Qed.
Lemma memory_local_tail_points st sts base env head tail :
  length head = memory_leaf_count st ->
  map (memory_local_extracted_event_point base (head++tail))
    (indexed_memory_list_trace (base+memory_leaf_count st)%nat sts env) =
  map (memory_local_extracted_event_point (base+memory_leaf_count st)%nat tail)
    (indexed_memory_list_trace (base+memory_leaf_count st)%nat sts env).
Proof.
  intro LENGTH; apply map_ext_in; intros event MEMBER; rewrite <- LENGTH.
  apply memory_local_point_append_right; rewrite LENGTH.
  pose proof (proj2 indexed_memory_site_bounds_contracts sts (base+memory_leaf_count st)%nat env event MEMBER); lia.
Qed.

Theorem memory_extracted_list_timestamp_position sts :
  forall constraints env_depth iterator_depth schedule position instructions env base event,
    MemoryExtractor.extract_stmts sts constraints env_depth iterator_depth schedule position = Okk instructions ->
    length env = (env_depth+iterator_depth)%nat -> in_poly env constraints = true ->
    In event (indexed_memory_list_trace base sts env) ->
    exists ordinal suffix, (position <= ordinal)%nat /\
      PL.ip_time_stamp (memory_local_extracted_event_point base instructions event) =
        affine_product schedule env++Z.of_nat ordinal::suffix.
Proof.
  induction sts as [|st sts IH]; intros constraints env_depth iterator_depth schedule position instructions env base event
    EXTRACT LENGTH DOMAIN MEMBER; [contradiction|].
  apply MemoryExtractor.extract_stmts_cons_success_inv in EXTRACT as [head [tail [HEAD [TAIL EXTRACT]]]].
  subst instructions; cbn in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
  - rewrite memory_local_point_append_left.
    2: { rewrite (memory_extractor_leaf_count HEAD).
         pose proof (proj1 indexed_memory_site_bounds_contracts st base env event MEMBER); lia. }
    destruct (@memory_extracted_stmt_timestamp_prefix st constraints env_depth iterator_depth
      (schedule++[(repeat 0 (env_depth+iterator_depth),Z.of_nat position)]) head env base event
      HEAD LENGTH DOMAIN MEMBER) as [suffix STAMP].
    exists position,suffix; split; [lia|].
    rewrite MemoryExtractor.affine_product_sched_prefix_seq in STAMP.
    rewrite STAMP,<- app_assoc; reflexivity.
  - rewrite memory_local_point_append_right.
    2: { rewrite (memory_extractor_leaf_count HEAD).
         pose proof (proj2 indexed_memory_site_bounds_contracts sts (base+memory_leaf_count st)%nat env event MEMBER); lia. }
    rewrite (memory_extractor_leaf_count HEAD).
    destruct (IH _ _ _ _ _ _ env (base+memory_leaf_count st)%nat event TAIL LENGTH DOMAIN MEMBER)
      as [ordinal [suffix [ORDINAL STAMP]]].
    exists ordinal,suffix; split; [lia|exact STAMP].
Qed.

Theorem memory_extractor_trace_order :
  (forall st constraints env_depth iterator_depth schedule instructions env base,
    MemoryExtractor.extract_stmt st constraints env_depth iterator_depth schedule = Okk instructions ->
    length env = (env_depth+iterator_depth)%nat -> in_poly env constraints = true ->
    StronglySorted memory_sequence_sched_lt
      (map (memory_local_extracted_event_point base instructions) (indexed_memory_loop_trace base st env))) /\
  (forall sts constraints env_depth iterator_depth schedule position instructions env base,
    MemoryExtractor.extract_stmts sts constraints env_depth iterator_depth schedule position = Okk instructions ->
    length env = (env_depth+iterator_depth)%nat -> in_poly env constraints = true ->
    StronglySorted memory_sequence_sched_lt
      (map (memory_local_extracted_event_point base instructions) (indexed_memory_list_trace base sts env))).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH constraints env_depth iterator_depth schedule instructions env base EXTRACT LENGTH DOMAIN.
    apply MemoryExtractor.extract_stmt_loop_success_inv in EXTRACT as [lower_constraint [upper_constraint [LOWER [UPPER EXTRACT]]]].
    assert (CHILD_DOMAIN : forall index, In index (Zrange (L.eval_expr env lower) (L.eval_expr env upper)) ->
      in_poly (index::env) (MemoryExtractor.lift_affine_list constraints++[lower_constraint;upper_constraint]) = true).
    { intros index RANGE; eapply MemoryExtractor.loop_constraints_sound_lifted;
        [exact LENGTH|exact LOWER|exact UPPER|exact DOMAIN|apply Zrange_in; exact RANGE]. }
    cbn; rewrite memory_map_flat_map.
    eapply memory_strongly_sorted_flat_map_on with (Q := Z.lt).
    + rewrite <- (map_id (Zrange (L.eval_expr env lower) (L.eval_expr env upper))).
      apply memory_strongly_sorted_range; auto.
    + intros index RANGE; eapply (IH _ env_depth (S iterator_depth) _ instructions (index::env) base);
        [exact EXTRACT|cbn; lia|apply CHILD_DOMAIN; exact RANGE].
    + intros first second point other FIRST_RANGE SECOND_RANGE ORDER FIRST SECOND.
      apply in_map_iff in FIRST as [first_event [<- FIRST]].
      apply in_map_iff in SECOND as [second_event [<- SECOND]].
      destruct (@memory_extracted_stmt_timestamp_prefix body
        (MemoryExtractor.lift_affine_list constraints++[lower_constraint;upper_constraint]) env_depth (S iterator_depth)
        (MemoryExtractor.lift_affine_list schedule++[(1::repeat 0 (env_depth+iterator_depth),0)])
        instructions (first::env) base first_event EXTRACT ltac:(cbn; lia) (CHILD_DOMAIN first FIRST_RANGE) FIRST)
        as [left STAMP].
      destruct (@memory_extracted_stmt_timestamp_prefix body
        (MemoryExtractor.lift_affine_list constraints++[lower_constraint;upper_constraint]) env_depth (S iterator_depth)
        (MemoryExtractor.lift_affine_list schedule++[(1::repeat 0 (env_depth+iterator_depth),0)])
        instructions (second::env) base second_event EXTRACT ltac:(cbn; lia) (CHILD_DOMAIN second SECOND_RANGE) SECOND)
        as [right OTHER_STAMP].
      rewrite MemoryExtractor.affine_product_sched_prefix_loop in STAMP,OTHER_STAMP.
      unfold memory_sequence_sched_lt; rewrite STAMP,OTHER_STAMP,<- !app_assoc.
      apply memory_timestamp_prefix_lt; exact ORDER.
  - intros instruction arguments constraints env_depth iterator_depth schedule instructions env base EXTRACT LENGTH DOMAIN.
    cbn; constructor; [constructor|constructor].
  - intros sts IH constraints env_depth iterator_depth schedule instructions env base EXTRACT LENGTH DOMAIN.
    cbn in EXTRACT |- *; eapply IH; eassumption.
  - intros test body IH constraints env_depth iterator_depth schedule instructions env base EXTRACT LENGTH DOMAIN.
    apply MemoryExtractor.extract_stmt_guard_success_inv in EXTRACT as [test_constraints [TEST EXTRACT]].
    cbn; destruct (L.eval_test env test) eqn:EVAL; [|constructor].
    eapply (IH _ env_depth iterator_depth schedule instructions env base); [exact EXTRACT|exact LENGTH|].
    eapply MemoryExtractor.guard_constraints_sound_in_poly; eassumption.
  - intros constraints env_depth iterator_depth schedule position instructions env base EXTRACT LENGTH DOMAIN.
    cbn; constructor.
  - intros st IH sts REST constraints env_depth iterator_depth schedule position instructions env base EXTRACT LENGTH DOMAIN.
    apply MemoryExtractor.extract_stmts_cons_success_inv in EXTRACT as [head [tail [HEAD [TAIL EXTRACT]]]].
    subst instructions; cbn; rewrite map_app,
      (@memory_local_head_points st base env head tail (memory_extractor_leaf_count HEAD)),
      (@memory_local_tail_points st sts base env head tail (memory_extractor_leaf_count HEAD)).
    apply memory_strongly_sorted_append.
    + eapply IH; [exact HEAD|exact LENGTH|exact DOMAIN].
    + eapply REST; [exact TAIL|exact LENGTH|exact DOMAIN].
    + intros first second FIRST SECOND.
      apply in_map_iff in FIRST as [first_event [<- FIRST]].
      apply in_map_iff in SECOND as [second_event [<- SECOND]].
      destruct (@memory_extracted_stmt_timestamp_prefix st constraints env_depth iterator_depth
        (schedule++[(repeat 0 (env_depth+iterator_depth),Z.of_nat position)]) head env base first_event
        HEAD LENGTH DOMAIN FIRST) as [left STAMP].
      destruct (@memory_extracted_list_timestamp_position sts constraints env_depth iterator_depth schedule (S position)
        tail env (base+memory_leaf_count st)%nat second_event TAIL LENGTH DOMAIN SECOND)
        as [ordinal [right [ORDINAL OTHER_STAMP]]].
      rewrite MemoryExtractor.affine_product_sched_prefix_seq in STAMP.
      unfold memory_sequence_sched_lt; rewrite STAMP,OTHER_STAMP,<- app_assoc.
      apply memory_timestamp_prefix_lt; lia.
Qed.

Theorem memory_extracted_trace_points_sorted st instructions env :
  MemoryExtractor.extract_stmt st [] (length env) O [] = Okk instructions ->
  StronglySorted memory_sequence_sched_lt
    (map (memory_extracted_event_point instructions) (indexed_memory_loop_trace O st env)).
Proof.
  intro EXTRACT.
  assert (POINTS : map (memory_extracted_event_point instructions) (indexed_memory_loop_trace O st env) =
    map (memory_local_extracted_event_point O instructions) (indexed_memory_loop_trace O st env)).
  { apply map_ext; intro event; unfold memory_extracted_event_point,memory_local_extracted_event_point;
      rewrite Nat.sub_0_r; reflexivity. }
  rewrite POINTS; eapply (proj1 memory_extractor_trace_order); [exact EXTRACT|lia|reflexivity].
Qed.
Print Assumptions memory_extracted_stmt_timestamp_prefix.
Print Assumptions memory_extracted_list_timestamp_position.
Print Assumptions memory_extracted_trace_points_sorted.
