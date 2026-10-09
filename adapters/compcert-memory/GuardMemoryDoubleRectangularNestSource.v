From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightGlobalScope ClightRegionProgress ClightLoopSyntax ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceLoopModel
  GuardMemoryDoubleInitializedReductionSource
  GuardMemoryDoubleInitializedNestData GuardMemoryDoubleInitializedNestSource GuardMemoryDoubleReductionNestSource
  GuardMemoryDoubleAssignmentFactory GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl
  GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryLongLoopSettle GuardMemoryLongHeaderLicense
  GuardMemoryDoubleRectangularNestData GuardMemoryDoubleRectangularNestModel.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_rectangular_nest_ready instruction ge counts prefix :=
  forall coordinates, Forall2 (fun count value => 0<=value<Z.of_nat count) counts coordinates ->
    double_source_instruction_resolved instruction (prefix++coordinates) ge (double_source_instruction_layouts instruction).
Lemma double_rectangular_nest_ready_child instruction ge count counts prefix value :
  double_rectangular_nest_ready instruction ge (count::counts) prefix -> 0<=value<Z.of_nat count ->
  double_rectangular_nest_ready instruction ge counts (prefix++[value]).
Proof.
  intros READY RANGE coordinates BOUNDS.
  pose proof (@READY (value::coordinates) ltac:(constructor; assumption)) as RECEIPT.
  replace ((prefix++[value])++coordinates) with (prefix++value::coordinates) by (rewrite <- app_assoc; reflexivity).
  exact RECEIPT.
Qed.
Definition double_rectangular_observations := list (ident*(block*nat)).
Definition double_rectangular_observed_axes (axes : double_rectangular_axes) counts (observations : double_rectangular_observations) :=
  Forall2 (fun axis count => exists bound_block, In (snd axis,(bound_block,count)) observations) axes counts.
Definition double_rectangular_observed_loads (observations : double_rectangular_observations) memory :=
  forall header bound_block count, In (header,(bound_block,count)) observations ->
    Mem.load Mint64 memory bound_block 0=Some (Vlong (Int64.repr (Z.of_nat count))).
Definition double_rectangular_nest_entry controls valuation observations temps memory :=
  double_source_prefix_words controls valuation temps /\ double_rectangular_observed_loads observations memory.

Section SOURCE.
Variable p : program.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable observations : double_rectangular_observations.
Hypothesis GLOBAL : preserving_globals (globalenv p) ge.
Hypothesis BINDINGS : forall header bound_block count, In (header,(bound_block,count)) observations ->
  double_global_binding ge locals header bound_block.

Theorem double_rectangular_nest_canonical_source_model axes :
  forall counts slot parameters controls valuation body instruction temps memory after final,
  checked_double_source_instruction p (controls++double_rectangular_iterators axes) body=Some instruction ->
  double_initialized_nest_fresh controls (double_rectangular_iterators axes) ->
  locals_avoid (double_source_instruction_globals instruction) locals ->
  (forall header bound_block count, In (header,(bound_block,count)) observations ->
    fst (value_instruction_write (double_source_instruction_model instruction))<>header) ->
  double_rectangular_observed_axes axes counts observations ->
  Forall (fun count => Z.of_nat count<=Int64.max_signed) counts ->
  skipn slot parameters=map Z.of_nat counts ->
  double_rectangular_nest_ready instruction ge counts (map valuation controls) ->
  double_rectangular_nest_entry controls valuation observations temps memory ->
  (exec_stmt fe ge locals temps memory (double_rectangular_nest_code axes body) E0 after final Out_normal <->
   SL.loop_semantics (double_rectangular_nest_model (double_source_instruction_model instruction) (length axes)
     slot (length (map valuation controls))) (rev (map valuation controls)++parameters)
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts instruction)) memory)
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts instruction)) final) /\
   after=double_rectangular_nest_exit (double_rectangular_iterators axes) counts temps).
Proof.
  induction axes as [|[iterator header] rest IH]; intros counts slot parameters controls valuation body instruction
    temps memory after final LEAF FRESH LOCAL WRITE LINK UPPERS PARAMETERS READY ENTRY.
  - inversion LINK; subst counts; cbn [double_rectangular_iterators] in LEAF; rewrite app_nil_r in LEAF.
    pose proof (@READY [] ltac:(constructor)) as RESOLVED; rewrite app_nil_r in RESOLVED.
    destruct RESOLVED as [write [reads [WR RR]]].
    pose proof (@checked_double_source_instruction_execution_iff p controls body instruction valuation fe ge locals
      temps memory write reads final LEAF GLOBAL LOCAL (proj1 ENTRY) WR RR) as BRIDGE.
    cbn [double_rectangular_nest_code double_rectangular_nest_model length]; rewrite double_source_instruction_Loop.
    rewrite double_rectangular_nest_exit_nil; unfold double_source_model_point; split.
    + intro RUN; pose proof (@checked_double_source_assignment_effects p controls body instruction fe ge locals
        temps memory E0 after final Out_normal LEAF RUN) as [_ [TEMPS NORMAL]].
      subst after; split; [apply BRIDGE; exact RUN|reflexivity].
    + intros [MODEL SAME]; subst after; apply BRIDGE; exact MODEL.
  - inversion LINK as [|axis count axes counts' OBSERVED LINKS]; subst axis axes counts.
    destruct OBSERVED as [bound_block OBSERVED]; cbn [snd] in OBSERVED.
    inversion UPPERS as [|count' counts'' UPPER UPPERS']; subst count' counts''.
    cbn [double_rectangular_iterators map fst] in LEAF,FRESH.
    destruct FRESH as [DISTINCT TAIL].
    assert (LENGTH : length rest=length counts') by (eapply Forall2_length; exact LINKS).
    assert (NEXT_PARAMETERS : skipn (S slot) parameters=map Z.of_nat counts')
      by (eapply double_rectangular_parameter_tail; exact PARAMETERS).
    assert (CHILD_LEAF : checked_double_source_instruction p ((controls++[iterator])++double_rectangular_iterators rest)
      body=Some instruction).
    { replace ((controls++[iterator])++double_rectangular_iterators rest) with
        (controls++iterator::double_rectangular_iterators rest) by (rewrite <- app_assoc; reflexivity); exact LEAF. }
    assert (OUTER_FRESH : ~ In iterator (double_rectangular_iterators rest)).
    { intro MEMBER; apply (@double_initialized_nest_fresh_disjoint (controls++[iterator])
        (double_rectangular_iterators rest) TAIL iterator MEMBER); apply in_or_app; right; cbn; auto. }
    assert (PREFIX_DISJOINT : forall key, In key controls -> ~ In key (double_rectangular_iterators rest)).
    { intros key MEMBER WRITTEN; apply (@double_initialized_nest_fresh_disjoint (controls++[iterator])
        (double_rectangular_iterators rest) TAIL key WRITTEN); apply in_or_app; auto. }
    set (physical := fun value first last => SL.loop_semantics
      (double_rectangular_nest_model (double_source_instruction_model instruction) (length rest)
        (S slot) (length (map valuation controls++[value]))) (rev (map valuation controls++[value])++parameters)
      (RuntimeState (global_double_locations ge (double_source_instruction_layouts instruction)) first)
      (RuntimeState (global_double_locations ge (double_source_instruction_layouts instruction)) last)).
    assert (BRIDGE : forall value le m le' m', 0<=value<Z.of_nat count ->
      double_rectangular_nest_entry controls valuation observations le m ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      (exec_stmt fe ge locals le m (double_rectangular_nest_code rest body) E0 le' m' Out_normal <->
       physical value m m' /\ le'=double_rectangular_nest_exit (double_rectangular_iterators rest) counts' le)).
    { intros value le m le' m' RANGE [WORDS LOADS] VALUE.
      pose proof (@double_source_control_values controls valuation iterator value DISTINCT) as VALUES.
      pose proof (@double_source_control_words controls valuation iterator value le DISTINCT WORDS VALUE) as EXTENDED.
      assert (CHILD_READY : double_rectangular_nest_ready instruction ge counts'
        (map (double_source_control_value valuation iterator value) (controls++[iterator]))).
      { pose proof (@double_rectangular_nest_ready_child instruction ge count counts'
          (map valuation controls) value READY RANGE) as NEXT.
        exact (@eq_ind_r (list Z) (map valuation controls++[value])
          (fun prefix => double_rectangular_nest_ready instruction ge counts' prefix) NEXT
          (map (double_source_control_value valuation iterator value) (controls++[iterator])) VALUES). }
      pose proof (@IH counts' (S slot) parameters (controls++[iterator])
        (double_source_control_value valuation iterator value) body instruction le m le' m'
        CHILD_LEAF TAIL LOCAL WRITE LINKS UPPERS' NEXT_PARAMETERS CHILD_READY
        ltac:(split; assumption)) as CORRECT.
      unfold physical; rewrite <- VALUES; exact CORRECT. }
    assert (HEADER_TEST : forall le m value,
      double_rectangular_nest_entry controls valuation observations le m -> 0<=value<=Z.of_nat count ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      expression_test (memory_global_long_condition iterator header) (Entry ge locals le m) (value <? Z.of_nat count)).
    { intros le m value [WORDS LOADS] RANGE VALUE.
      eapply double_matmul_global_test; [eapply BINDINGS; exact OBSERVED|exact (@LOADS header bound_block count OBSERVED)|exact VALUE|exact RANGE|exact UPPER]. }
    assert (SET_ENTRY : forall le m value, double_rectangular_nest_entry controls valuation observations le m ->
      double_rectangular_nest_entry controls valuation observations (PTree.set iterator (Vlong (Int64.repr value)) le) m).
    { intros le m value [WORDS LOADS]; split; [|exact LOADS].
      intros key MEMBER; rewrite PTree.gso by (intro SAME; subst; contradiction); apply WORDS; exact MEMBER. }
    assert (BODY_ENTRY : forall value le m le' m', 0<=value<Z.of_nat count ->
      double_rectangular_nest_entry controls valuation observations le m ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      exec_stmt fe ge locals le m (double_rectangular_nest_code rest body) E0 le' m' Out_normal ->
      double_rectangular_nest_entry controls valuation observations le' m').
    { intros value le m le' m' RANGE INV VALUE RUN.
      destruct (proj1 (@BRIDGE value le m le' m' RANGE INV VALUE) RUN) as [MODEL EXIT].
      destruct INV as [WORDS LOADS]; subst le'; split.
      - intros key MEMBER; rewrite double_rectangular_nest_exit_frame;
          [apply WORDS; exact MEMBER|apply PREFIX_DISJOINT; exact MEMBER].
      - intros observed_header observed_block observed_count MEMBER.
        unfold physical in MODEL; rewrite LENGTH in MODEL.
        rewrite (@double_rectangular_nest_preserves_global counts' instruction (S slot)
          (map valuation controls++[value]) parameters ge (double_source_instruction_layouts instruction)
          m m' observed_header observed_block Mint64 0 NEXT_PARAMETERS
          (proj2 (@BINDINGS observed_header observed_block observed_count MEMBER))
          (@WRITE observed_header observed_block observed_count MEMBER) MODEL).
        exact (@LOADS observed_header observed_block observed_count MEMBER). }
    cbn [double_rectangular_nest_code length double_rectangular_iterators map fst].
    rewrite LENGTH,double_rectangular_nest_memory by exact PARAMETERS.
    pose proof (@memory_long_initialized_settled_equivalence fe ge locals iterator
      (memory_global_long_condition iterator header) (double_rectangular_nest_code rest body) (Z.of_nat count) 0
      (double_rectangular_nest_entry controls valuation observations) physical
      (fun _ => double_rectangular_nest_exit (double_rectangular_iterators rest) counts') HEADER_TEST
      (@normal_statement_execution fe ge locals _ (@double_rectangular_nest_normal rest body
        (@checked_double_reduction_assignment_shape p ((controls++[iterator])++double_rectangular_iterators rest)
          body instruction CHILD_LEAF)))
      ltac:(intros le m tr le' m' RUN; eapply writes_only_frame;
        [exact RUN|exact (@double_rectangular_nest_writes rest body
          (@checked_double_reduction_assignment_shape p ((controls++[iterator])++double_rectangular_iterators rest)
            body instruction CHILD_LEAF))|exact OUTER_FRESH])
      BRIDGE BODY_ENTRY SET_ENTRY count temps memory after final eq_refl ltac:(lia) ENTRY) as CORRECT.
    unfold physical in CORRECT; rewrite LENGTH in CORRECT.
    rewrite double_rectangular_nest_settled_exit in CORRECT by exact OUTER_FRESH; exact CORRECT.
Qed.
End SOURCE.

Print Assumptions double_rectangular_nest_ready_child.
Print Assumptions double_rectangular_nest_canonical_source_model.
