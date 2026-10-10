From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightLoopSyntax ClightTempFrame ClightGlobalScope ClightRegionProgress ClightSkipPrefix.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleInitializedReductionSource
  GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeModelData
  GuardMemoryDoubleSourceTreeModel GuardMemoryDoubleSourceTreeSyntax GuardMemoryDoubleSourceTreeExit
  GuardMemoryDoubleSourceTreeState GuardMemoryDoubleRectangularNestData GuardMemoryLongControl GuardMemoryLongLoopControl
  GuardMemoryLongRangeSource GuardMemoryLongRangeCaptureSource GuardMemoryLongExpressionCapture GuardMemoryDoubleSignedRangeSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma double_tree_initial_execution ge locals temps memory start :
  eval_expr ge locals temps memory (double_tree_initial start) (Vlong (Int64.repr (Int.signed start))).
Proof. unfold double_tree_initial; eapply eval_Ecast; [constructor|reflexivity]. Qed.
Lemma double_tree_entry_set ge locals headers header_values controls control_values temps memory iterator value :
  ~ In iterator controls -> double_source_tree_entry ge locals headers header_values controls control_values temps memory ->
  double_source_tree_entry ge locals headers header_values controls control_values
    (PTree.set iterator (Vlong (Int64.repr value)) temps) memory.
Proof.
  intros FRESH [WORDS HEADERS]; split; [|exact HEADERS].
  intros key MEMBER; rewrite PTree.gso by (intro SAME; subst; contradiction); apply WORDS; exact MEMBER.
Qed.
Lemma double_tree_entry_child ge locals headers header_values controls control_values temps memory iterator value :
  ~ In iterator controls -> double_source_tree_entry ge locals headers header_values controls control_values temps memory ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  double_source_tree_entry ge locals headers header_values (controls++[iterator])
    (double_source_control_value control_values iterator value) temps memory.
Proof.
  intros FRESH [WORDS HEADERS] VALUE; split; [eapply double_source_control_words; eassumption|exact HEADERS].
Qed.
Lemma double_tree_entry_parent ge locals headers header_values controls control_values temps memory iterator value :
  ~ In iterator controls ->
  double_source_tree_entry ge locals headers header_values (controls++[iterator])
    (double_source_control_value control_values iterator value) temps memory ->
  double_source_tree_entry ge locals headers header_values controls control_values temps memory.
Proof.
  intros FRESH [WORDS HEADERS]; split; [|exact HEADERS].
  intros key MEMBER; pose proof (WORDS key (in_or_app _ _ _ (or_introl MEMBER))) as WORD.
  unfold double_source_control_value in WORD; destruct (peq key iterator); [subst; contradiction|exact WORD].
Qed.

Section SOURCE_TREE.
Variable p : program.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable layouts : PTree.t (list Z).
Variable headers : list ident.
Variable header_values : ident -> Z.
Hypothesis GLOBAL : preserving_globals (globalenv p) ge.

(** All source executions and exits are derived from concrete Clight services.
    Domain premises cover ranges and resolved cells; the installed factory must
    derive them from its accepted entry condition. Only active headers need load
    receipts, and neither this theorem nor its proof executes source at runtime. *)
Theorem double_source_tree_execution_memory tree : forall controls control_values temps memory after final,
  double_source_tree_checked p controls tree -> double_source_tree_shared_layout tree layouts ->
  double_source_tree_scope tree locals -> double_source_tree_header_exclusions tree headers ->
  incl (double_source_tree_active_headers header_values tree) headers ->
  double_source_tree_model_facts tree controls header_values control_values ge layouts ->
  double_source_tree_entry ge locals headers header_values controls control_values temps memory ->
  (exec_stmt fe ge locals temps memory (double_source_tree_code tree) E0 after final Out_normal <->
   double_source_tree_memory tree header_values (map control_values controls) (global_double_locations ge layouts) memory final /\
   after=double_source_tree_exit header_values tree temps).
Proof.
  induction tree; intros controls control_values temps memory after final CHECK LAYOUT SCOPE EXCLUSIONS ACTIVE FACTS ENTRY.
  - cbn [double_source_tree_code double_source_tree_memory double_source_tree_exit double_source_tree_exit_assignments
      double_rectangular_set_assignments]; split.
    + intro RUN; inversion RUN; subst; auto.
    + intros [MEMORY TEMPS]; subst; constructor.
  - destruct FACTS as [write [reads [WRITE READS]]].
    assert (POINT : exec_stmt fe ge locals temps memory body E0 temps final Out_normal <->
      double_source_model_point (double_source_instruction_model instruction) (map control_values controls)
        (RuntimeState (global_double_locations ge layouts) memory) (RuntimeState (global_double_locations ge layouts) final)).
    { eapply checked_double_source_shared_execution_iff;
        [exact CHECK|apply LAYOUT; left; reflexivity|exact GLOBAL|apply SCOPE; left; reflexivity|exact (proj1 ENTRY)|exact WRITE|exact READS]. }
    cbn [double_source_tree_code double_source_tree_memory double_source_tree_exit double_source_tree_exit_assignments
      double_rectangular_set_assignments]; split.
    + intro RUN; destruct (@checked_double_source_assignment_effects p controls body instruction fe ge locals temps memory
        E0 after final Out_normal CHECK RUN) as [_ [SAME _]]; subst after; split; [apply POINT; exact RUN|reflexivity].
    + intros [MODEL SAME]; subst after; apply POINT; exact MODEL.
  - destruct CHECK as [CHECK1 CHECK2]; destruct FACTS as [FACTS1 FACTS2].
    assert (LAYOUT1 : double_source_tree_shared_layout tree1 layouts).
    { intros instruction MEMBER; apply LAYOUT,in_or_app; left; exact MEMBER. }
    assert (LAYOUT2 : double_source_tree_shared_layout tree2 layouts).
    { intros instruction MEMBER; apply LAYOUT,in_or_app; right; exact MEMBER. }
    assert (SCOPE1 : double_source_tree_scope tree1 locals).
    { intros instruction MEMBER; apply SCOPE,in_or_app; left; exact MEMBER. }
    assert (SCOPE2 : double_source_tree_scope tree2 locals).
    { intros instruction MEMBER; apply SCOPE,in_or_app; right; exact MEMBER. }
    assert (EXCLUSIONS1 : double_source_tree_header_exclusions tree1 headers).
    { intros instruction header POINT HEADER; apply EXCLUSIONS; [apply in_or_app; left; exact POINT|exact HEADER]. }
    assert (EXCLUSIONS2 : double_source_tree_header_exclusions tree2 headers).
    { intros instruction header POINT HEADER; apply EXCLUSIONS; [apply in_or_app; right; exact POINT|exact HEADER]. }
    assert (ACTIVE1 : incl (double_source_tree_active_headers header_values tree1) headers).
    { intros header MEMBER; apply ACTIVE,in_or_app; left; exact MEMBER. }
    assert (ACTIVE2 : incl (double_source_tree_active_headers header_values tree2) headers).
    { intros header MEMBER; apply ACTIVE,in_or_app; right; exact MEMBER. }
    cbn [double_source_tree_code double_source_tree_memory]; rewrite double_source_tree_exit_sequence; split.
    + intro RUN; destruct (sequence_normal_decode RUN) as [middle [next [FIRST SECOND]]].
      destruct (@IHtree1 controls control_values temps memory middle next CHECK1 LAYOUT1 SCOPE1 EXCLUSIONS1 ACTIVE1 FACTS1 ENTRY)
        as [FORWARD1 BACKWARD1]; destruct (FORWARD1 FIRST) as [MODEL1 EXIT1].
      pose proof (@double_source_tree_entry_preserved p controls tree1 fe ge locals headers header_values control_values
        temps memory E0 middle next Out_normal CHECK1 GLOBAL SCOPE1 EXCLUSIONS1 ENTRY FIRST) as NEXT_ENTRY.
      destruct (proj1 (@IHtree2 controls control_values middle next after final CHECK2 LAYOUT2 SCOPE2 EXCLUSIONS2 ACTIVE2 FACTS2 NEXT_ENTRY)
        SECOND) as [MODEL2 EXIT2].
      split; [exists next; auto|rewrite <- EXIT1; exact EXIT2].
    + intros [[next [MODEL1 MODEL2]] EXIT];
        set (middle := double_source_tree_exit header_values tree1 temps).
      assert (FIRST : exec_stmt fe ge locals temps memory (double_source_tree_code tree1) E0 middle next Out_normal).
      { apply (proj2 (@IHtree1 controls control_values temps memory middle next CHECK1 LAYOUT1 SCOPE1 EXCLUSIONS1 ACTIVE1 FACTS1 ENTRY));
          split; [exact MODEL1|reflexivity]. }
      pose proof (@double_source_tree_entry_preserved p controls tree1 fe ge locals headers header_values control_values
        temps memory E0 middle next Out_normal CHECK1 GLOBAL SCOPE1 EXCLUSIONS1 ENTRY FIRST) as NEXT_ENTRY.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact FIRST|].
      apply (proj2 (@IHtree2 controls control_values middle next after final CHECK2 LAYOUT2 SCOPE2 EXCLUSIONS2 ACTIVE2 FACTS2 NEXT_ENTRY));
        split; [exact MODEL2|exact EXIT].
  - destruct CHECK as [FRESH [DECL CHILD]]; destruct FACTS as [UPPER CHILD_FACTS].
    assert (ITERATOR_FRAME : ~ In iterator (double_source_tree_writes tree)).
    { eapply double_source_tree_writes_avoid; [exact CHILD|apply in_or_app; right; left; reflexivity]. }
    assert (BOUND_MEMBER : In (tree_bound_header bound) headers) by (apply ACTIVE; left; reflexivity).
    assert (CHILD_ACTIVE : forall value, Int.signed start<=value<double_tree_bound_value header_values bound ->
      incl (double_source_tree_active_headers header_values tree) headers).
    { intros value RANGE header MEMBER; apply ACTIVE; right.
      cbn [double_source_tree_active_headers].
      rewrite (proj2 (Z.ltb_lt (Int.signed start) (double_tree_bound_value header_values bound)) ltac:(lia)); exact MEMBER. }
    set (invariant := double_source_tree_entry ge locals headers header_values controls control_values).
    set (physical := fun value => double_source_tree_memory tree header_values (map control_values controls++[value])
      (global_double_locations ge layouts)).
    assert (BRIDGE : forall value le m le' m', Int.signed start<=value<double_tree_bound_value header_values bound ->
      invariant le m -> le ! iterator=Some (Vlong (Int64.repr value)) ->
      (exec_stmt fe ge locals le m (double_source_tree_code tree) E0 le' m' Out_normal <->
        physical value m m' /\ le'=double_source_tree_exit header_values tree le)).
    { intros value le m le' m' RANGE INV VALUE.
      pose proof (@IHtree (controls++[iterator]) (double_source_control_value control_values iterator value)
        le m le' m' CHILD LAYOUT SCOPE EXCLUSIONS (CHILD_ACTIVE value RANGE) (CHILD_FACTS value RANGE)
        (@double_tree_entry_child ge locals headers header_values controls control_values le m iterator value FRESH INV VALUE)) as CORRECT.
      rewrite double_source_control_values in CORRECT by exact FRESH; exact CORRECT. }
    assert (BODY_ENTRY : forall value le m le' m', Int.signed start<=value<double_tree_bound_value header_values bound ->
      invariant le m -> le ! iterator=Some (Vlong (Int64.repr value)) ->
      exec_stmt fe ge locals le m (double_source_tree_code tree) E0 le' m' Out_normal -> invariant le' m').
    { intros value le m le' m' RANGE INV VALUE RUN.
      apply (@double_tree_entry_parent ge locals headers header_values controls control_values le' m' iterator value FRESH).
      eapply (@double_source_tree_entry_preserved p (controls++[iterator]) tree fe ge locals headers header_values
        (double_source_control_value control_values iterator value) le m E0 le' m' Out_normal);
        [exact CHILD|exact GLOBAL|exact SCOPE|exact EXCLUSIONS| |exact RUN].
      eapply double_tree_entry_child; eassumption. }
    assert (HEADER : forall le m value, invariant le m ->
      Int.signed start<=value<=Z.max (Int.signed start) (double_tree_bound_value header_values bound) ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      expression_test (Ebinop Olt (Etempvar iterator memory_long_type) (double_tree_bound_code bound) memory_signed_int_type)
        (Entry ge locals le m) (value <? double_tree_bound_value header_values bound)).
    { intros le m value INV RANGE VALUE; exists (Val.of_bool (value <? double_tree_bound_value header_values bound)); split.
      - eapply memory_long_test_execution;
          [reflexivity|apply double_tree_bound_type| |exact UPPER|constructor; exact VALUE|].
        + pose proof (@memory_i32_range_is_i64 (Int.signed start) (Int.signed_range start)) as LOWER.
          destruct (Z_le_dec (Int.signed start) (double_tree_bound_value header_values bound));
            rewrite ?Z.max_r,?Z.max_l in RANGE by lia; lia.
        + eapply double_tree_bound_observed_execution; [exact BOUND_MEMBER|exact (proj2 INV)].
      - destruct (value <? double_tree_bound_value header_values bound); reflexivity. }
    pose proof (@memory_long_from_range_equivalence fe ge locals iterator (double_tree_initial start)
      (Ebinop Olt (Etempvar iterator memory_long_type) (double_tree_bound_code bound) memory_signed_int_type)
      (double_source_tree_code tree) (Int.signed start) (double_tree_bound_value header_values bound) invariant physical
      (fun _ => double_source_tree_exit header_values tree)
      ltac:(intros; apply double_tree_initial_execution) HEADER
      ltac:(intros le m tr le' m' out RUN; eapply double_source_tree_completed_normal; eassumption)
      ltac:(intros le m tr le' m' RUN; eapply writes_only_frame;
        [exact RUN|eapply double_source_tree_writes_only; exact CHILD|exact ITERATOR_FRAME])
      BRIDGE BODY_ENTRY
      ltac:(intros le m value INV; apply double_tree_entry_set; [exact FRESH|exact INV])
      temps memory after final ENTRY) as CORRECT.
    rewrite (@double_source_tree_range_settled_exit header_values raw iterator start bound tree temps ITERATOR_FRAME) in CORRECT.
    cbn [double_source_tree_code double_source_tree_memory].
    destruct raw; [rewrite (long_raw_from_execution iterator (double_tree_initial start) (double_tree_bound_code bound)
      (double_source_tree_code tree) fe ge locals temps memory E0 after final Out_normal)|]; exact CORRECT.
Qed.
End SOURCE_TREE.

Corollary double_source_tree_source_Loop p tree controls control_values fe ge locals layouts headers header_values temps memory after final :
  preserving_globals (globalenv p) ge -> double_source_tree_checked p controls tree ->
  double_source_tree_shared_layout tree layouts -> double_source_tree_scope tree locals ->
  double_source_tree_header_exclusions tree headers -> incl (double_source_tree_active_headers header_values tree) headers ->
  double_source_tree_model_facts tree controls header_values control_values ge layouts ->
  double_source_tree_entry ge locals headers header_values controls control_values temps memory ->
  (exec_stmt fe ge locals temps memory (double_source_tree_code tree) E0 after final Out_normal <->
   SL.loop_semantics (double_source_tree_model (double_source_tree_parameters tree) (length controls) tree)
     (rev (map control_values controls)++map header_values (double_source_tree_parameters tree))
     (RuntimeState (global_double_locations ge layouts) memory) (RuntimeState (global_double_locations ge layouts) final) /\
   after=double_source_tree_exit header_values tree temps).
Proof.
  intros GLOBAL CHECK LAYOUT SCOPE EXCLUSIONS ACTIVE FACTS ENTRY.
  pose proof (@double_source_tree_model_memory tree (map control_values controls) header_values
    (global_double_locations ge layouts) memory final) as MODEL; rewrite map_length in MODEL.
  rewrite MODEL; eapply double_source_tree_execution_memory; eassumption.
Qed.

Print Assumptions double_tree_initial_execution.
Print Assumptions double_tree_entry_set.
Print Assumptions double_tree_entry_child.
Print Assumptions double_tree_entry_parent.
Print Assumptions double_source_tree_execution_memory.
Print Assumptions double_source_tree_source_Loop.
