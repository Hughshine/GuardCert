From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightGlobalScope ClightRegionProgress ClightSkipPrefix ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryDoubleLocations GuardMemoryLongControl
  GuardMemoryLiteralDoubleTreeData GuardMemoryLiteralDoubleTreeSyntax
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleInitializedReductionSource
  GuardMemoryDoubleSourceLoopModel GuardMemoryDoubleSignedRangeSource
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeState GuardMemoryDoubleSourceTreeSource
  GuardMemoryDoubleSourceTreeModelData GuardMemoryDoubleSourceTreeModel GuardMemoryDoubleSourceTreeExit
  GuardMemoryLongRangeSource GuardMemoryLongRangeCaptureSource GuardMemoryLongExpressionCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition literal_double_tree_entry := double_source_prefix_words.
Definition literal_double_tree_exit tree := double_source_tree_exit literal_double_parameter_value (literal_double_tree_skeleton tree).
Definition literal_double_tree_memory tree := double_source_tree_memory (literal_double_tree_skeleton tree) literal_double_parameter_value.
Definition literal_double_tree_facts tree controls values ge layouts :=
  double_source_tree_model_facts (literal_double_tree_skeleton tree) controls literal_double_parameter_value values ge layouts.

Lemma literal_double_tree_entry_preserved p controls tree fe ge locals temps memory trace after final outcome values :
  literal_double_source_tree_checked p controls tree -> literal_double_tree_entry controls values temps ->
  exec_stmt fe ge locals temps memory (literal_double_source_tree_code tree) trace after final outcome ->
  literal_double_tree_entry controls values after.
Proof.
  intros CHECK ENTRY RUN key MEMBER.
  assert (SAME : after ! key=temps ! key).
  { eapply writes_only_frame; [exact RUN|eapply literal_double_source_tree_writes_only; exact CHECK|].
    eapply literal_double_source_writes_avoid; eassumption. }
  rewrite SAME; apply ENTRY; exact MEMBER.
Qed.
Lemma literal_double_tree_entry_child controls values temps iterator value :
  ~ In iterator controls -> literal_double_tree_entry controls values temps ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  literal_double_tree_entry (controls++[iterator]) (double_source_control_value values iterator value) temps.
Proof. intros; eapply double_source_control_words; eassumption. Qed.
Lemma literal_double_tree_entry_parent controls values temps iterator value :
  ~ In iterator controls ->
  literal_double_tree_entry (controls++[iterator]) (double_source_control_value values iterator value) temps ->
  literal_double_tree_entry controls values temps.
Proof.
  intros FRESH ENTRY key MEMBER.
  pose proof (ENTRY key (in_or_app _ _ _ (or_introl MEMBER))) as WORD.
  unfold double_source_control_value in WORD; destruct (peq key iterator); [subst; contradiction|exact WORD].
Qed.
Lemma literal_double_tree_entry_set controls values temps iterator value :
  ~ In iterator controls -> literal_double_tree_entry controls values temps ->
  literal_double_tree_entry controls values (PTree.set iterator (Vlong (Int64.repr value)) temps).
Proof.
  intros FRESH ENTRY key MEMBER; rewrite PTree.gso by (intro SAME; subst; contradiction).
  apply ENTRY; exact MEMBER.
Qed.

Section SOURCE.
Variable p : program.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable layouts : PTree.t (list Z).
Hypothesis GLOBAL : preserving_globals (globalenv p) ge.

Theorem literal_double_source_tree_execution_memory tree : forall controls values temps memory after final,
  literal_double_source_tree_checked p controls tree ->
  double_source_tree_shared_layout (literal_double_tree_skeleton tree) layouts ->
  double_source_tree_scope (literal_double_tree_skeleton tree) locals ->
  literal_double_tree_facts tree controls values ge layouts -> literal_double_tree_entry controls values temps ->
  (exec_stmt fe ge locals temps memory (literal_double_source_tree_code tree) E0 after final Out_normal <->
   literal_double_tree_memory tree (map values controls) (global_double_locations ge layouts) memory final /\
   after=literal_double_tree_exit tree temps).
Proof.
  induction tree; intros controls values temps memory after final CHECK LAYOUT SCOPE FACTS ENTRY.
  - cbn [literal_double_source_tree_code literal_double_tree_memory literal_double_tree_exit literal_double_tree_skeleton
      double_source_tree_memory double_source_tree_exit double_source_tree_exit_assignments
      GuardMemoryDoubleRectangularNestData.double_rectangular_set_assignments]; split.
    + intro RUN; inversion RUN; subst; auto.
    + intros [MEMORY TEMPS]; subst; constructor.
  - destruct FACTS as [write [reads [WRITE READS]]].
    assert (POINT : exec_stmt fe ge locals temps memory body E0 temps final Out_normal <->
      double_source_model_point (double_source_instruction_model instruction) (map values controls)
        (RuntimeState (global_double_locations ge layouts) memory) (RuntimeState (global_double_locations ge layouts) final)).
    { eapply checked_double_source_shared_execution_iff;
        [exact CHECK|apply LAYOUT; left; reflexivity|exact GLOBAL|apply SCOPE; left; reflexivity|exact ENTRY|exact WRITE|exact READS]. }
    cbn [literal_double_source_tree_code literal_double_tree_memory literal_double_tree_exit literal_double_tree_skeleton
      double_source_tree_memory double_source_tree_exit double_source_tree_exit_assignments
      GuardMemoryDoubleRectangularNestData.double_rectangular_set_assignments]; split.
    + intro RUN; destruct (@checked_double_source_assignment_effects p controls body instruction fe ge locals temps memory
        E0 after final Out_normal CHECK RUN) as [_ [SAME _]]; subst after; split; [apply POINT; exact RUN|reflexivity].
    + intros [MODEL SAME]; subst after; apply POINT; exact MODEL.
  - destruct CHECK as [CHECK1 CHECK2]; destruct FACTS as [FACTS1 FACTS2].
    assert (LAYOUT1 : double_source_tree_shared_layout (literal_double_tree_skeleton tree1) layouts).
    { intros instruction MEMBER; apply LAYOUT,in_or_app; left; exact MEMBER. }
    assert (LAYOUT2 : double_source_tree_shared_layout (literal_double_tree_skeleton tree2) layouts).
    { intros instruction MEMBER; apply LAYOUT,in_or_app; right; exact MEMBER. }
    assert (SCOPE1 : double_source_tree_scope (literal_double_tree_skeleton tree1) locals).
    { intros instruction MEMBER; apply SCOPE,in_or_app; left; exact MEMBER. }
    assert (SCOPE2 : double_source_tree_scope (literal_double_tree_skeleton tree2) locals).
    { intros instruction MEMBER; apply SCOPE,in_or_app; right; exact MEMBER. }
    cbn [literal_double_source_tree_code literal_double_tree_memory literal_double_tree_skeleton double_source_tree_memory].
    change (exec_stmt fe ge locals temps memory (Ssequence (literal_double_source_tree_code tree1)
      (literal_double_source_tree_code tree2)) E0 after final Out_normal <->
      (exists middle, literal_double_tree_memory tree1 (map values controls) (global_double_locations ge layouts) memory middle /\
        literal_double_tree_memory tree2 (map values controls) (global_double_locations ge layouts) middle final) /\
      after=double_source_tree_exit literal_double_parameter_value
        (DoubleTreeSequence (literal_double_tree_skeleton tree1) (literal_double_tree_skeleton tree2)) temps).
    rewrite double_source_tree_exit_sequence; split.
    + intro RUN; destruct (sequence_normal_decode RUN) as [middle [next [FIRST SECOND]]].
      destruct (proj1 (@IHtree1 controls values temps memory middle next CHECK1 LAYOUT1 SCOPE1 FACTS1 ENTRY) FIRST)
        as [MODEL1 EXIT1].
      pose proof (@literal_double_tree_entry_preserved p controls tree1 fe ge locals temps memory E0 middle next
        Out_normal values CHECK1 ENTRY FIRST) as NEXT_ENTRY.
      destruct (proj1 (@IHtree2 controls values middle next after final CHECK2 LAYOUT2 SCOPE2 FACTS2 NEXT_ENTRY) SECOND)
        as [MODEL2 EXIT2].
      split; [exists next; auto|].
      change (after=literal_double_tree_exit tree2 (literal_double_tree_exit tree1 temps)).
      rewrite <- EXIT1; exact EXIT2.
    + intros [[next [MODEL1 MODEL2]] EXIT]; set (middle := literal_double_tree_exit tree1 temps).
      assert (FIRST : exec_stmt fe ge locals temps memory (literal_double_source_tree_code tree1) E0 middle next Out_normal).
      { apply (proj2 (@IHtree1 controls values temps memory middle next CHECK1 LAYOUT1 SCOPE1 FACTS1 ENTRY)); auto. }
      pose proof (@literal_double_tree_entry_preserved p controls tree1 fe ge locals temps memory E0 middle next
        Out_normal values CHECK1 ENTRY FIRST) as NEXT_ENTRY.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact FIRST|].
      apply (proj2 (@IHtree2 controls values middle next after final CHECK2 LAYOUT2 SCOPE2 FACTS2 NEXT_ENTRY)); auto.
  - destruct CHECK as [FRESH [DECODE [LIMIT CHILD]]].
    unfold literal_double_tree_facts in FACTS; cbn [literal_double_tree_skeleton double_source_tree_model_facts] in FACTS.
    rewrite literal_double_skeleton_bound in FACTS; destruct FACTS as [UPPER CHILD_FACTS].
    assert (ITERATOR_FRAME : ~ In iterator (literal_double_source_tree_writes tree)).
    { eapply literal_double_source_writes_avoid; [exact CHILD|apply in_or_app; right; left; reflexivity]. }
    set (invariant := literal_double_tree_entry controls values).
    set (physical := fun value => literal_double_tree_memory tree (map values controls++[value])
      (global_double_locations ge layouts)).
    assert (BRIDGE : forall value le m le' m', Int.signed start<=value<upper ->
      invariant le -> le ! iterator=Some (Vlong (Int64.repr value)) ->
      (exec_stmt fe ge locals le m (literal_double_source_tree_code tree) E0 le' m' Out_normal <->
        physical value m m' /\ le'=literal_double_tree_exit tree le)).
    { intros value le m le' m' RANGE INV VALUE.
      pose proof (@IHtree (controls++[iterator]) (double_source_control_value values iterator value)
        le m le' m' CHILD LAYOUT SCOPE (CHILD_FACTS value RANGE)
        (@literal_double_tree_entry_child controls values le iterator value FRESH INV VALUE)) as CORRECT.
      rewrite double_source_control_values in CORRECT by exact FRESH; exact CORRECT. }
    assert (BODY_ENTRY : forall value le m le' m', Int.signed start<=value<upper ->
      invariant le -> le ! iterator=Some (Vlong (Int64.repr value)) ->
      exec_stmt fe ge locals le m (literal_double_source_tree_code tree) E0 le' m' Out_normal -> invariant le').
    { intros value le m le' m' RANGE INV VALUE RUN.
      apply (@literal_double_tree_entry_parent controls values le' iterator value FRESH).
      eapply literal_double_tree_entry_preserved; [exact CHILD| |exact RUN].
      eapply literal_double_tree_entry_child; eassumption. }
    assert (HEADER : forall le m value, invariant le -> Int.signed start<=value<=Z.max (Int.signed start) upper ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      expression_test (Ebinop Cop.Olt (Etempvar iterator memory_long_type) bound memory_signed_int_type)
        (Entry ge locals le m) (value <? upper)).
    { intros le m value INV RANGE VALUE; exists (Val.of_bool (value <? upper)); split.
      - eapply literal_double_bound_test_execution; [exact DECODE| |exact UPPER|exact VALUE].
        pose proof (@memory_i32_range_is_i64 (Int.signed start) (Int.signed_range start)) as LOWER.
        destruct (Z_le_dec (Int.signed start) upper); rewrite ?Z.max_r,?Z.max_l in RANGE by lia; lia.
      - destruct (value <? upper); reflexivity. }
    pose proof (@memory_long_from_range_equivalence fe ge locals iterator (double_tree_initial start)
      (Ebinop Cop.Olt (Etempvar iterator memory_long_type) bound memory_signed_int_type)
      (literal_double_source_tree_code tree) (Int.signed start) upper (fun le _ => invariant le) physical
      (fun _ => literal_double_tree_exit tree)
      ltac:(intros; apply double_tree_initial_execution) HEADER
      ltac:(intros le m tr le' m' out RUN; eapply literal_double_source_tree_completed_normal; eassumption)
      ltac:(intros le m tr le' m' RUN; eapply writes_only_frame;
        [exact RUN|eapply literal_double_source_tree_writes_only; exact CHILD|exact ITERATOR_FRAME])
      BRIDGE BODY_ENTRY
      ltac:(intros le m value INV; apply literal_double_tree_entry_set; [exact FRESH|exact INV])
      temps memory after final ENTRY) as CORRECT.
    pose proof (@double_source_tree_range_settled_exit literal_double_parameter_value raw iterator start
      (DoubleTreeBound (literal_double_parameter_name upper) None) (literal_double_tree_skeleton tree) temps ITERATOR_FRAME) as EXIT.
    rewrite literal_double_skeleton_bound in EXIT.
    unfold literal_double_tree_exit in CORRECT; cbn zeta in CORRECT; rewrite EXIT in CORRECT.
    cbn [literal_double_source_tree_code literal_double_tree_memory literal_double_tree_skeleton double_source_tree_memory].
    rewrite literal_double_skeleton_bound.
    destruct raw; [rewrite (long_raw_from_execution iterator (double_tree_initial start) bound
      (literal_double_source_tree_code tree) fe ge locals temps memory E0 after final Out_normal)|]; exact CORRECT.
Qed.
End SOURCE.

Corollary literal_double_source_tree_source_Loop p tree controls values fe ge locals layouts temps memory after final :
  preserving_globals (globalenv p) ge -> literal_double_source_tree_checked p controls tree ->
  double_source_tree_shared_layout (literal_double_tree_skeleton tree) layouts ->
  double_source_tree_scope (literal_double_tree_skeleton tree) locals ->
  literal_double_tree_facts tree controls values ge layouts -> literal_double_tree_entry controls values temps ->
  (exec_stmt fe ge locals temps memory (literal_double_source_tree_code tree) E0 after final Out_normal <->
   SL.loop_semantics
     (double_source_tree_model (double_source_tree_parameters (literal_double_tree_skeleton tree))
       (length controls) (literal_double_tree_skeleton tree))
     (rev (map values controls)++map literal_double_parameter_value
       (double_source_tree_parameters (literal_double_tree_skeleton tree)))
     (RuntimeState (global_double_locations ge layouts) memory)
     (RuntimeState (global_double_locations ge layouts) final) /\ after=literal_double_tree_exit tree temps).
Proof.
  intros GLOBAL CHECK LAYOUT SCOPE FACTS ENTRY.
  pose proof (@double_source_tree_model_memory (literal_double_tree_skeleton tree) (map values controls)
    literal_double_parameter_value (global_double_locations ge layouts) memory final) as MODEL.
  rewrite map_length in MODEL; rewrite MODEL.
  eapply literal_double_source_tree_execution_memory; eassumption.
Qed.

Print Assumptions literal_double_tree_entry_preserved.
Print Assumptions literal_double_tree_entry_child.
Print Assumptions literal_double_tree_entry_parent.
Print Assumptions literal_double_source_tree_execution_memory.
Print Assumptions literal_double_source_tree_source_Loop.
