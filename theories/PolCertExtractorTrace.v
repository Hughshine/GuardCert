From Stdlib Require Import List Bool ZArith Lia Sorting.Sorted Sorting.Permutation Sorting.SetoidList.
From polcert.lib Require Import Misc Linalg LinalgExt ListExt ImpureAlarmConfig.
From polcert.src Require Import Base PolyBase PointWitness ExtractorFrontend PrepareCodegen SelectionSort.
From polcert.polygen Require Import PolIRs Result.
From Vpl Require Import Impure.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

From Guard Require Import PolCertSourceTrace.
(** Parameterized successor of GuardMemoryExtractorTrace; instruction values and
    memory effects come only from the supplied POLIRS instance. *)
Module PolCertExtractorTraceFor (IRs : POLIRS).
Module Trace := PolCertSourceTraceFor IRs.
Include Trace.
Module MemoryExtractor := ExtractorFrontend IRs.

Fixpoint memory_source_instructions (st : L.stmt) : list IRs.Instr.t :=
  match st with
  | L.Instr instruction _ => [instruction]
  | L.Seq sts => memory_source_instruction_list sts
  | L.Loop _ _ body | L.Guard _ body => memory_source_instructions body
  end
with memory_source_instruction_list (sts : L.stmt_list) : list IRs.Instr.t :=
  match sts with
  | L.SNil => []
  | L.SCons st rest => memory_source_instructions st ++ memory_source_instruction_list rest
  end.

Theorem memory_extractor_static_sites :
  (forall st constraints env_depth iterator_depth schedule instructions,
    MemoryExtractor.extract_stmt st constraints env_depth iterator_depth schedule = Okk instructions ->
    map PL.pi_instr instructions = memory_source_instructions st) /\
  (forall sts constraints env_depth iterator_depth schedule position instructions,
    MemoryExtractor.extract_stmts sts constraints env_depth iterator_depth schedule position = Okk instructions ->
    map PL.pi_instr instructions = memory_source_instruction_list sts).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH constraints env_depth iterator_depth schedule instructions EXTRACT.
    apply MemoryExtractor.extract_stmt_loop_success_inv in EXTRACT as [lower_constraint [upper_constraint [_ [_ EXTRACT]]]].
    cbn; eapply IH; exact EXTRACT.
  - intros instruction arguments constraints env_depth iterator_depth schedule instructions EXTRACT.
    apply MemoryExtractor.extract_stmt_instr_success_inv in EXTRACT as [transformation [writes [reads [_ [_ EXTRACT]]]]].
    subst instructions; reflexivity.
  - intros sts IH constraints env_depth iterator_depth schedule instructions EXTRACT.
    cbn in EXTRACT |- *; eapply IH; exact EXTRACT.
  - intros test body IH constraints env_depth iterator_depth schedule instructions EXTRACT.
    apply MemoryExtractor.extract_stmt_guard_success_inv in EXTRACT as [test_constraints [_ EXTRACT]].
    cbn; eapply IH; exact EXTRACT.
  - intros constraints env_depth iterator_depth schedule position instructions EXTRACT.
    apply MemoryExtractor.extract_stmts_nil_success_inv in EXTRACT; subst instructions; reflexivity.
  - intros st IH sts REST constraints env_depth iterator_depth schedule position instructions EXTRACT.
    apply MemoryExtractor.extract_stmts_cons_success_inv in EXTRACT as [head [tail [HEAD [TAIL EXTRACT]]]].
    subst instructions; cbn; rewrite map_app; f_equal; [eapply IH|eapply REST]; eassumption.
Qed.

Lemma memory_source_leaf_counts :
  (forall st, length (memory_source_instructions st) = memory_leaf_count st) /\
  (forall sts, length (memory_source_instruction_list sts) = memory_list_leaf_count sts).
Proof.
  apply trace_stmt_list_ind; cbn; intros; auto; rewrite length_app; congruence.
Qed.
Lemma memory_extractor_leaf_count st constraints env_depth iterator_depth schedule instructions :
  MemoryExtractor.extract_stmt st constraints env_depth iterator_depth schedule = Okk instructions ->
  length instructions = memory_leaf_count st.
Proof.
  intro EXTRACT; pose proof (proj1 memory_extractor_static_sites _ _ _ _ _ _ EXTRACT) as SITES.
  rewrite <- (proj1 memory_source_leaf_counts st),<- SITES,length_map; reflexivity.
Qed.

Arguments memory_extractor_leaf_count {st constraints env_depth iterator_depth schedule instructions} _.

Theorem indexed_memory_instruction_sites :
  (forall st base env event,
    In event (indexed_memory_loop_trace base st env) ->
    nth_error (memory_source_instructions st) (indexed_event_site event - base)%nat =
      Some (event_instruction (indexed_event_payload event))) /\
  (forall sts base env event,
    In event (indexed_memory_list_trace base sts env) ->
    nth_error (memory_source_instruction_list sts) (indexed_event_site event - base)%nat =
      Some (event_instruction (indexed_event_payload event))).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH base env event MEMBER; cbn in MEMBER |- *.
    apply in_flat_map in MEMBER as [index [_ MEMBER]]; eapply IH; exact MEMBER.
  - intros instruction arguments base env event MEMBER; cbn in MEMBER |- *.
    destruct MEMBER as [<-|ABSENT]; [cbn; rewrite Nat.sub_diag; reflexivity|contradiction].
  - intros sts IH; exact IH.
  - intros test body IH base env event MEMBER; cbn in MEMBER |- *.
    destruct (L.eval_test env test); [eapply IH; exact MEMBER|contradiction].
  - intros base env event MEMBER; contradiction.
  - intros st IH sts REST base env event MEMBER; cbn in MEMBER |- *.
    apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + rewrite nth_error_app1.
      * eapply IH; exact MEMBER.
      * rewrite (proj1 memory_source_leaf_counts st).
        pose proof (proj1 indexed_memory_site_bounds_contracts st base env event MEMBER); lia.
    + rewrite nth_error_app2.
      * rewrite (proj1 memory_source_leaf_counts st).
        replace (indexed_event_site event - base - memory_leaf_count st)%nat with
          (indexed_event_site event - (base+memory_leaf_count st))%nat by lia.
        eapply REST; exact MEMBER.
      * rewrite (proj1 memory_source_leaf_counts st).
        pose proof (proj2 indexed_memory_site_bounds_contracts sts (base+memory_leaf_count st)%nat env event MEMBER); lia.
Qed.

Theorem memory_extracted_event_instruction st constraints env_depth iterator_depth schedule instructions env event :
  MemoryExtractor.extract_stmt st constraints env_depth iterator_depth schedule = Okk instructions ->
  In event (indexed_memory_loop_trace O st env) ->
  exists instruction,
    nth_error instructions (indexed_event_site event) = Some instruction /\
    PL.pi_instr instruction = event_instruction (indexed_event_payload event).
Proof.
  intros EXTRACT MEMBER.
  pose proof (proj1 indexed_memory_instruction_sites st O env event MEMBER) as SITE.
  rewrite Nat.sub_0_r in SITE.
  rewrite <- (proj1 memory_extractor_static_sites _ _ _ _ _ _ EXTRACT),nth_error_map in SITE.
  destruct (nth_error instructions (indexed_event_site event)) as [instruction|] eqn:NTH;
    [cbn in SITE; inversion SITE; subst|discriminate].
  exists instruction; split; [reflexivity|reflexivity].
Qed.

Definition memory_extracted_event_metadata env_depth instructions base event :=
  exists instruction,
    nth_error instructions (indexed_event_site event-base)%nat = Some instruction /\
    PL.pi_instr instruction = event_instruction (indexed_event_payload event) /\
    length (event_environment (indexed_event_payload event)) =
      (env_depth + PL.pi_depth instruction)%nat /\
    in_poly (rev (event_environment (indexed_event_payload event))) (PL.pi_poly instruction) = true /\
    PL.pi_point_witness instruction = PSWIdentity (PL.pi_depth instruction) /\
    affine_product (PL.pi_transformation instruction)
      (rev (event_environment (indexed_event_payload event))) =
      event_arguments (indexed_event_payload event).

Theorem memory_extractor_trace_metadata :
  (forall st constraints env_depth iterator_depth schedule instructions env base event,
    MemoryExtractor.extract_stmt st constraints env_depth iterator_depth schedule = Okk instructions ->
    length env = (env_depth+iterator_depth)%nat -> in_poly env constraints = true ->
    In event (indexed_memory_loop_trace base st env) ->
    memory_extracted_event_metadata env_depth instructions base event) /\
  (forall sts constraints env_depth iterator_depth schedule position instructions env base event,
    MemoryExtractor.extract_stmts sts constraints env_depth iterator_depth schedule position = Okk instructions ->
    length env = (env_depth+iterator_depth)%nat -> in_poly env constraints = true ->
    In event (indexed_memory_list_trace base sts env) ->
    memory_extracted_event_metadata env_depth instructions base event).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH constraints env_depth iterator_depth schedule instructions env base event
      EXTRACT LENGTH DOMAIN MEMBER.
    apply MemoryExtractor.extract_stmt_loop_success_inv in EXTRACT as [lower_constraint [upper_constraint [LOWER [UPPER EXTRACT]]]].
    cbn in MEMBER; apply in_flat_map in MEMBER as [index [RANGE MEMBER]].
    eapply (IH _ env_depth (S iterator_depth) _ instructions (index::env) base event);
      [exact EXTRACT|cbn; lia| |exact MEMBER].
    eapply MemoryExtractor.loop_constraints_sound_lifted; [exact LENGTH|exact LOWER|exact UPPER|exact DOMAIN|].
    apply Zrange_in; exact RANGE.
  - intros instruction arguments constraints env_depth iterator_depth schedule instructions env base event
      EXTRACT LENGTH DOMAIN MEMBER.
    apply MemoryExtractor.extract_stmt_instr_success_inv in EXTRACT as [transformation [writes [reads [TRANSFORM [_ EXTRACT]]]]].
    subst instructions; cbn in MEMBER; destruct MEMBER as [<-|ABSENT]; [|contradiction].
    unfold memory_extracted_event_metadata; cbn; rewrite Nat.sub_diag.
    eexists; split; [reflexivity|]; split; [reflexivity|]; split; [exact LENGTH|].
    split.
    + change (in_poly (rev env) (MemoryExtractor.normalize_affine_list_rev (env_depth+iterator_depth)%nat constraints) = true).
      unfold in_poly; rewrite MemoryExtractor.normalize_affine_list_rev_satisfies_constraint
        by (rewrite length_rev; exact LENGTH).
      rewrite rev_involutive; exact DOMAIN.
    + split; [reflexivity|].
      change (affine_product (MemoryExtractor.normalize_affine_list_rev (env_depth+iterator_depth)%nat transformation) (rev env) = map (L.eval_expr env) arguments).
      rewrite MemoryExtractor.exprlist_to_aff_rev_normalized_correct with (es := arguments)
        by (exact TRANSFORM || (rewrite length_rev; exact LENGTH)).
      rewrite rev_involutive; reflexivity.
  - intros sts IH constraints env_depth iterator_depth schedule instructions env base event
      EXTRACT LENGTH DOMAIN MEMBER; cbn in EXTRACT; eapply IH; eassumption.
  - intros test body IH constraints env_depth iterator_depth schedule instructions env base event
      EXTRACT LENGTH DOMAIN MEMBER.
    apply MemoryExtractor.extract_stmt_guard_success_inv in EXTRACT as [test_constraints [TEST EXTRACT]].
    cbn in MEMBER; destruct (L.eval_test env test) eqn:EVAL; [|contradiction].
    eapply (IH _ env_depth iterator_depth schedule instructions env base event);
      [exact EXTRACT|exact LENGTH| |exact MEMBER].
    eapply MemoryExtractor.guard_constraints_sound_in_poly; eassumption.
  - intros constraints env_depth iterator_depth schedule position instructions env base event
      EXTRACT LENGTH DOMAIN MEMBER; contradiction.
  - intros st IH sts REST constraints env_depth iterator_depth schedule position instructions env base event
      EXTRACT LENGTH DOMAIN MEMBER.
    apply MemoryExtractor.extract_stmts_cons_success_inv in EXTRACT as [head [tail [HEAD [TAIL EXTRACT]]]].
    subst instructions; cbn in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER].
    + destruct (IH _ _ _ _ _ _ _ _ HEAD LENGTH DOMAIN MEMBER) as [instruction [NTH DETAILS]].
      exists instruction; split; [rewrite nth_error_app1; [exact NTH|]|exact DETAILS].
      rewrite (memory_extractor_leaf_count HEAD).
      pose proof (proj1 indexed_memory_site_bounds_contracts st base env event MEMBER); lia.
    + destruct (REST _ _ _ _ _ _ _ _ _ TAIL LENGTH DOMAIN MEMBER) as [instruction [NTH DETAILS]].
      exists instruction; split; [|exact DETAILS].
      rewrite nth_error_app2.
      * rewrite (memory_extractor_leaf_count HEAD).
        replace (indexed_event_site event-base-memory_leaf_count st)%nat with
          (indexed_event_site event-(base+memory_leaf_count st))%nat by lia; exact NTH.
      * rewrite (memory_extractor_leaf_count HEAD).
        pose proof (proj2 indexed_memory_site_bounds_contracts sts (base+memory_leaf_count st)%nat env event MEMBER); lia.
Qed.

Definition memory_point_of_extracted_event instruction event : PL.InstrPoint :=
  {| PL.ILSema.ip_nth := indexed_event_site event;
     PL.ILSema.ip_index := rev (event_environment (indexed_event_payload event));
     PL.ILSema.ip_transformation := PL.current_transformation_of instruction
       (rev (event_environment (indexed_event_payload event)));
     PL.ILSema.ip_time_stamp := affine_product (PL.pi_schedule instruction)
       (rev (event_environment (indexed_event_payload event)));
     PL.ILSema.ip_instruction := PL.pi_instr instruction;
     PL.ILSema.ip_depth := PL.pi_depth instruction |}.

Lemma memory_extracted_point_belongs instruction event :
  in_poly (rev (event_environment (indexed_event_payload event))) (PL.pi_poly instruction) = true ->
  PL.belongs_to (memory_point_of_extracted_event instruction event) instruction.
Proof. intro DOMAIN; unfold PL.belongs_to,memory_point_of_extracted_event; cbn; auto. Qed.

Lemma memory_extracted_point_execution instruction event before after :
  PL.pi_instr instruction = event_instruction (indexed_event_payload event) ->
  PL.pi_point_witness instruction = PSWIdentity (PL.pi_depth instruction) ->
  affine_product (PL.pi_transformation instruction)
    (rev (event_environment (indexed_event_payload event))) = event_arguments (indexed_event_payload event) ->
  (PL.instr_point_sema (memory_point_of_extracted_event instruction event) before after <->
   indexed_memory_event_step event before after).
Proof.
  intros INSTRUCTION IDENTITY ARGUMENTS.
  assert (CURRENT : PL.current_transformation_of instruction
    (rev (event_environment (indexed_event_payload event))) = PL.pi_transformation instruction).
  { unfold PL.current_transformation_of,PL.current_transformation_at; rewrite IDENTITY; reflexivity. }
  split.
  - intro RUN; inversion RUN as [writes reads STEP].
    change (IRs.Instr.instr_semantics (PL.pi_instr instruction)
      (affine_product (PL.current_transformation_of instruction
        (rev (event_environment (indexed_event_payload event))))
        (rev (event_environment (indexed_event_payload event)))) writes reads before after) in STEP.
    rewrite CURRENT,ARGUMENTS,INSTRUCTION in STEP; exists writes,reads; exact STEP.
  - intros [writes [reads STEP]].
    apply PL.ILSema.ip_sema_intro with (wcs := writes) (rcs := reads).
    change (IRs.Instr.instr_semantics (PL.pi_instr instruction)
      (affine_product (PL.current_transformation_of instruction
        (rev (event_environment (indexed_event_payload event))))
        (rev (event_environment (indexed_event_payload event)))) writes reads before after).
    rewrite CURRENT,ARGUMENTS,INSTRUCTION; exact STEP.
Qed.

Theorem indexed_memory_environment_extension :
  (forall st base env event,
    In event (indexed_memory_loop_trace base st env) ->
    exists prefix, event_environment (indexed_event_payload event) = prefix ++ env) /\
  (forall sts base env event,
    In event (indexed_memory_list_trace base sts env) ->
    exists prefix, event_environment (indexed_event_payload event) = prefix ++ env).
Proof.
  apply trace_stmt_list_ind.
  - intros lower upper body IH base env event MEMBER; cbn in MEMBER.
    apply in_flat_map in MEMBER as [index [_ MEMBER]].
    destruct (IH base (index::env) event MEMBER) as [prefix ENV].
    exists (prefix++[index]); rewrite ENV,<- app_assoc; reflexivity.
  - intros instruction arguments base env event MEMBER; cbn in MEMBER.
    destruct MEMBER as [<-|ABSENT]; [exists []; reflexivity|contradiction].
  - intros sts IH; exact IH.
  - intros test body IH base env event MEMBER; cbn in MEMBER.
    destruct (L.eval_test env test); [eapply IH; exact MEMBER|contradiction].
  - intros base env event MEMBER; contradiction.
  - intros st IH sts REST base env event MEMBER; cbn in MEMBER; apply in_app_or in MEMBER as [MEMBER|MEMBER];
      [eapply IH|eapply REST]; exact MEMBER.
Qed.

Definition memory_empty_poly_instruction : PL.PolyInstr :=
  {| PL.pi_depth := O; PL.pi_instr := IRs.Instr.dummy_instr;
     PL.pi_poly := []; PL.pi_schedule := []; PL.pi_point_witness := PSWIdentity O;
     PL.pi_transformation := []; PL.pi_access_transformation := [];
     PL.pi_waccess := []; PL.pi_raccess := [] |}.
Definition memory_extracted_event_point instructions event :=
  memory_point_of_extracted_event
    (nth (indexed_event_site event) instructions memory_empty_poly_instruction) event.

Lemma memory_extracted_trace_event_step st instructions env event before after :
  MemoryExtractor.extract_stmt st [] (length env) O [] = Okk instructions ->
  In event (indexed_memory_loop_trace O st env) ->
  (indexed_memory_event_step event before after <->
   PL.instr_point_sema (memory_extracted_event_point instructions event) before after).
Proof.
  intros EXTRACT MEMBER.
  destruct (proj1 memory_extractor_trace_metadata st [] (length env) O [] instructions env O event
    EXTRACT ltac:(lia) eq_refl MEMBER) as [instruction [NTH [INSTRUCTION [LENGTH [DOMAIN [IDENTITY ARGUMENTS]]]]]].
  rewrite Nat.sub_0_r in NTH.
  unfold memory_extracted_event_point; assert (LOOKUP : nth (indexed_event_site event) instructions memory_empty_poly_instruction = instruction)
    by (eapply nth_error_nth; exact NTH).
  rewrite LOOKUP.
  symmetry; apply memory_extracted_point_execution; assumption.
Qed.

Arguments memory_extracted_trace_event_step {st instructions env event before after} _ _.

Theorem memory_extracted_trace_execution st instructions env before after :
  MemoryExtractor.extract_stmt st [] (length env) O [] = Okk instructions ->
  L.loop_semantics st env before after ->
  PL.instr_point_list_semantics
    (map (memory_extracted_event_point instructions) (indexed_memory_loop_trace O st env)) before after.
Proof.
  intros EXTRACT RUN; apply indexed_memory_loop_execution with (base := O) in RUN.
  eapply indexed_memory_trace_points_forward; [|exact RUN].
  intros event first final MEMBER STEP.
  apply (proj1 (@memory_extracted_trace_event_step st instructions env event first final EXTRACT MEMBER)); exact STEP.
Qed.

Theorem memory_extracted_trace_point_valid st instructions env point :
  MemoryExtractor.extract_stmt st [] (length env) O [] = Okk instructions ->
  In point (map (memory_extracted_event_point instructions) (indexed_memory_loop_trace O st env)) ->
  exists instruction,
    nth_error instructions (PL.ip_nth point) = Some instruction /\
    firstn (length env) (PL.ip_index point) = rev env /\
    PL.belongs_to point instruction /\
    length (PL.ip_index point) = (length env + PL.pi_depth instruction)%nat.
Proof.
  intros EXTRACT MEMBER; apply in_map_iff in MEMBER as [event [<- MEMBER]].
  destruct (proj1 memory_extractor_trace_metadata st [] (length env) O [] instructions env O event
    EXTRACT ltac:(lia) eq_refl MEMBER) as [instruction [NTH [INSTRUCTION [LENGTH [DOMAIN [IDENTITY ARGUMENTS]]]]]].
  rewrite Nat.sub_0_r in NTH.
  assert (LOOKUP : nth (indexed_event_site event) instructions memory_empty_poly_instruction = instruction)
    by (eapply nth_error_nth; exact NTH).
  unfold memory_extracted_event_point; rewrite LOOKUP.
  exists instruction; split; [exact NTH|]; split.
  - destruct (proj1 indexed_memory_environment_extension st O env event MEMBER) as [prefix ENV].
    change (firstn (length env) (rev (event_environment (indexed_event_payload event))) = rev env).
    rewrite ENV,rev_app_distr,firstn_app.
    rewrite firstn_all2 by (rewrite length_rev; lia).
    replace (length env-length (rev env))%nat with O by (rewrite length_rev; lia).
    cbn; rewrite app_nil_r; reflexivity.
  - split; [apply memory_extracted_point_belongs; exact DOMAIN|].
    change (length (rev (event_environment (indexed_event_payload event))) = (length env+PL.pi_depth instruction)%nat).
    rewrite length_rev; exact LENGTH.
Qed.
Print Assumptions memory_extractor_static_sites.
Print Assumptions memory_extracted_event_instruction.
Print Assumptions memory_extractor_trace_metadata.
Print Assumptions memory_extracted_trace_execution.
Print Assumptions memory_extracted_trace_point_valid.

End PolCertExtractorTraceFor.
