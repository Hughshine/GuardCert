From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation Sorting.SetoidList.
From polcert.lib Require Import Misc Linalg LinalgExt ListExt ImpureAlarmConfig.
From polcert.src Require Import Base PolyBase PointWitness ExtractorFrontend PrepareCodegen SelectionSort.
From polcert.polygen Require Import PolIRs Result.
From Vpl Require Import Impure.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

From Guard Require Import PolCertExtractorCoverage.
Module PolCertExtractorOrderFor (IRs : POLIRS).
Module Coverage := PolCertExtractorCoverageFor IRs.
Include Coverage.

Fixpoint source_zseq (start : Z) (count : nat) : list Z :=
  match count with O => [] | S n => start :: source_zseq (start+1) n end.
Lemma source_zseq_bounds count : forall start x,
  In x (source_zseq start count) -> start <= x < start+Z.of_nat count.
Proof.
  induction count; intros start x MEMBER; cbn in MEMBER; [contradiction|].
  rewrite Nat2Z.inj_succ; destruct MEMBER as [<-|MEMBER]; [lia|].
  specialize (IHcount (start+1) x MEMBER); lia.
Qed.
Lemma memory_strongly_sorted_append {A} (R : A -> A -> Prop) first second :
  StronglySorted R first -> StronglySorted R second ->
  (forall a b, In a first -> In b second -> R a b) ->
  StronglySorted R (first ++ second).
Proof.
  intros FIRST SECOND; induction FIRST; intro CROSS; cbn; [exact SECOND|].
  constructor.
  - apply IHFIRST; intros; apply CROSS; cbn; auto.
  - apply Forall_app; split; [exact H|].
    apply Forall_forall; intros; apply CROSS; cbn; auto.
Qed.
Lemma memory_strongly_sorted_zseq {A} (R : A -> A -> Prop) (f : Z -> A) :
  (forall x y, x < y -> R (f x) (f y)) ->
  forall count start, StronglySorted R (map f (source_zseq start count)).
Proof.
  intros MONOTONE count; induction count; intro start; cbn; constructor.
  - apply IHcount.
  - apply Forall_forall; intros value MEMBER.
    apply in_map_iff in MEMBER as [x [<- MEMBER]].
    apply MONOTONE; pose proof (@source_zseq_bounds _ _ _ MEMBER); lia.
Qed.
Lemma memory_strongly_sorted_nodup {A} (R : A -> A -> Prop) xs :
  (forall x, ~ R x x) -> StronglySorted R xs -> NoDup xs.
Proof.
  intros IRREFLEXIVE SORTED; induction SORTED; constructor; auto.
  intro MEMBER; apply Forall_forall with (x := a) in H; [apply (IRREFLEXIVE a H)|exact MEMBER].
Qed.
Lemma memory_range_zseq count : forall lower upper,
  upper = lower + Z.of_nat count -> Zrange lower upper = source_zseq lower count.
Proof.
  induction count; intros lower upper LENGTH; cbn.
  - rewrite Zrange_empty by lia; reflexivity.
  - rewrite Zrange_begin by (rewrite Nat2Z.inj_succ in LENGTH; lia).
    f_equal; apply IHcount; rewrite Nat2Z.inj_succ in LENGTH; lia.
Qed.
Lemma memory_strongly_sorted_range {A} (R : A -> A -> Prop) (f : Z -> A) lower upper :
  (forall x y, x < y -> R (f x) (f y)) -> StronglySorted R (map f (Zrange lower upper)).
Proof.
  intro ORDER; destruct (Z_lt_ge_dec lower upper) as [LT|EMPTY].
  - rewrite (@memory_range_zseq (Z.to_nat (upper-lower)) lower upper)
      by (rewrite Z2Nat.id by lia; lia).
    apply memory_strongly_sorted_zseq; exact ORDER.
  - rewrite Zrange_empty by lia; constructor.
Qed.
Lemma memory_strongly_sorted_project {A} (R Q : A -> A -> Prop) xs :
  (forall x y, R x y -> Q x y) -> StronglySorted R xs -> StronglySorted Q xs.
Proof.
  intros IMPL SORTED; induction SORTED; constructor; auto.
  apply Forall_forall; intros x MEMBER; apply IMPL; eapply Forall_forall; eauto.
Qed.
Definition memory_sequence_sched_lt (first second : PL.InstrPoint) :=
  lex_compare (PL.ILSema.ip_time_stamp first) (PL.ILSema.ip_time_stamp second) = Lt.
Lemma memory_sequence_sched_irrefl point : ~ memory_sequence_sched_lt point point.
Proof. unfold memory_sequence_sched_lt; rewrite lex_compare_reflexive; discriminate. Qed.
Lemma memory_sequence_strict_order_properties points : StronglySorted memory_sequence_sched_lt points ->
  NoDup points /\ Sorted PL.instr_point_sched_le points /\
  (forall first second, In first points -> In second points ->
    PL.ILSema.instr_point_sched_eq first second -> first = second).
Proof.
  intro ORDER; split.
  - apply memory_strongly_sorted_nodup with (R := memory_sequence_sched_lt);
      [apply memory_sequence_sched_irrefl|exact ORDER].
  - split.
    + apply StronglySorted_Sorted; eapply memory_strongly_sorted_project; [|exact ORDER].
      intros first second LT; left; exact LT.
    + induction ORDER as [|point points ORDER IH NEXT]; intros first second FIRST SECOND EQUAL;
        [contradiction|].
      destruct FIRST as [<-|FIRST]; destruct SECOND as [<-|SECOND]; auto.
      * pose proof (proj1 (Forall_forall _ _) NEXT _ SECOND) as LT.
        unfold memory_sequence_sched_lt in LT.
        unfold PL.ILSema.instr_point_sched_eq,PL.ILSema.instr_point_sched_eqb in EQUAL.
        apply comparison_eqb_iff_eq in EQUAL; congruence.
      * pose proof (proj1 (Forall_forall _ _) NEXT _ FIRST) as LT.
        unfold memory_sequence_sched_lt in LT.
        unfold PL.ILSema.instr_point_sched_eq,PL.ILSema.instr_point_sched_eqb in EQUAL.
        apply comparison_eqb_iff_eq in EQUAL.
        rewrite lex_compare_antisym in EQUAL; rewrite LT in EQUAL; discriminate.
Qed.

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

End PolCertExtractorOrderFor.
