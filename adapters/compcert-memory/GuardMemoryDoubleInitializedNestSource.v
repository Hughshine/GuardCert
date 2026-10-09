From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightGlobalScope ClightRegionProgress ClightLoopSyntax ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceLoopModel
  GuardMemoryDoubleInitializedReductionData GuardMemoryDoubleInitializedReductionSource
  GuardMemoryDoubleInitializedNestData GuardMemoryDoubleInitializedNestSyntax GuardMemoryDoubleInitializedNestModel
  GuardMemoryDoubleInitializedNestExit GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl
  GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryLongLoopSettle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_initialized_nest_ready description ge count prefix depth :=
  forall coordinates, length coordinates=depth -> Forall (fun value => 0<=value<Z.of_nat count) coordinates ->
    double_source_instruction_resolved (initialized_reduction_initial_instruction description) (prefix++coordinates)
      ge (double_initialized_reduction_layouts description) /\
    forall value, 0<=value<Z.of_nat count ->
      double_source_instruction_resolved (initialized_reduction_body_instruction description) ((prefix++coordinates)++[value])
        ge (double_initialized_reduction_layouts description).
Lemma double_initialized_nest_ready_child description ge count prefix depth value :
  double_initialized_nest_ready description ge count prefix (S depth) -> 0<=value<Z.of_nat count ->
  double_initialized_nest_ready description ge count (prefix++[value]) depth.
Proof.
  intros READY RANGE coordinates LENGTH BOUNDS.
  pose proof (@READY (value::coordinates) ltac:(cbn; congruence) ltac:(constructor; assumption)) as RECEIPTS.
  replace ((prefix++[value])++coordinates) with (prefix++value::coordinates) by (rewrite <- app_assoc; reflexivity).
  exact RECEIPTS.
Qed.
Lemma double_initialized_nest_prefix_disjoint p controls outers description :
  checked_double_initialized_reduction p (controls++outers) (double_initialized_reduction_code description)=Some description ->
  double_initialized_nest_fresh controls outers ->
  forall key, In key controls -> ~ In key (outers++[initialized_reduction_iterator description]).
Proof.
  intros LEAF FRESH key MEMBER WRITTEN.
  apply in_app_iff in WRITTEN as [WRITTEN|SINGLE].
  - apply (@double_initialized_nest_fresh_disjoint controls outers FRESH key WRITTEN); exact MEMBER.
  - cbn in SINGLE; destruct SINGLE as [SAME|IMPOSSIBLE]; [subst key|contradiction].
    destruct (@checked_double_initialized_reduction_sound p (controls++outers)
      (double_initialized_reduction_code description) description LEAF) as [_ [_ [_ STATIC]]].
    destruct (@double_initialized_reduction_static_sound p (controls++outers) description STATIC) as [DISTINCT REST].
    apply DISTINCT; apply in_or_app; auto.
Qed.
Lemma double_initialized_nest_outer_fresh p controls iterator rest description :
  checked_double_initialized_reduction p (controls++iterator::rest) (double_initialized_reduction_code description)=Some description ->
  double_initialized_nest_fresh (controls++[iterator]) rest ->
  ~ In iterator (rest++[initialized_reduction_iterator description]).
Proof.
  intros LEAF FRESH.
  eapply double_initialized_nest_prefix_disjoint with (controls:=controls++[iterator]);
    [replace ((controls++[iterator])++rest) with (controls++iterator::rest) by (rewrite <- app_assoc; reflexivity);
      exact LEAF|exact FRESH|apply in_or_app; right; cbn; auto].
Qed.
Definition double_initialized_nest_entry controls valuation header_block count temps memory :=
  double_source_prefix_words controls valuation temps /\
  Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr (Z.of_nat count))).

Section SOURCE.
Variable p : program.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable header_block : block.
Variable count : nat.
Hypothesis GLOBAL : preserving_globals (globalenv p) ge.
Hypothesis UPPER : Z.of_nat count<=Int64.max_signed.

Theorem double_initialized_nest_canonical_source_model outers : forall controls valuation description temps memory after final,
  checked_double_initialized_reduction p (controls++outers) (double_initialized_reduction_code description)=Some description ->
  double_initialized_nest_fresh controls outers ->
  locals_avoid (double_initialized_reduction_globals description) locals ->
  double_global_binding ge locals (initialized_reduction_header description) header_block ->
  double_initialized_nest_ready description ge count (map valuation controls) (length outers) ->
  double_initialized_nest_entry controls valuation header_block count temps memory ->
  (exec_stmt fe ge locals temps memory (double_initialized_nest_code outers description) E0 after final Out_normal <->
   SL.loop_semantics (double_source_initialized_nest_model
     (double_source_instruction_model (initialized_reduction_initial_instruction description))
     (double_source_instruction_model (initialized_reduction_body_instruction description)) (length outers)
     (length (map valuation controls))) (rev (map valuation controls)++[Z.of_nat count])
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts description)) memory)
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts description)) final) /\
   after=double_initialized_nest_exit outers (initialized_reduction_iterator description) count temps).
Proof.
  induction outers as [|iterator rest IH]; intros controls valuation description temps memory after final
    LEAF FRESH LOCAL HEADER READY ENTRY.
  - rewrite app_nil_r in LEAF.
    destruct (@READY [] eq_refl ltac:(constructor)) as [INITIAL BODY]; rewrite app_nil_r in INITIAL,BODY.
    cbn [double_initialized_nest_code double_source_initialized_nest_model length]; rewrite map_length,double_initialized_nest_exit_leaf.
    eapply double_initialized_reduction_source_model;
      [exact LEAF|exact GLOBAL|exact LOCAL|exact HEADER|exact UPPER|exact INITIAL|exact BODY|exact ENTRY].
  - destruct FRESH as [DISTINCT TAIL].
    assert (CHILD_LEAF : checked_double_initialized_reduction p ((controls++[iterator])++rest)
      (double_initialized_reduction_code description)=Some description).
    { replace ((controls++[iterator])++rest) with (controls++iterator::rest) by (rewrite <- app_assoc; reflexivity); exact LEAF. }
    pose proof (@checked_double_initialized_nest_complete p (controls++[iterator]) rest description TAIL CHILD_LEAF) as CHILD_CHECK.
    pose proof (@double_initialized_nest_outer_fresh p controls iterator rest description LEAF TAIL) as OUTER_FRESH.
    pose proof (@double_initialized_nest_prefix_disjoint p (controls++[iterator]) rest description CHILD_LEAF TAIL)
      as PREFIX_DISJOINT.
    set (physical := fun value first last => SL.loop_semantics (double_source_initialized_nest_model
      (double_source_instruction_model (initialized_reduction_initial_instruction description))
      (double_source_instruction_model (initialized_reduction_body_instruction description)) (length rest)
      (length (map valuation controls++[value]))) (rev (map valuation controls++[value])++[Z.of_nat count])
      (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts description)) first)
      (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts description)) last)).
    assert (BRIDGE : forall value le m le' m', 0<=value<Z.of_nat count ->
      double_initialized_nest_entry controls valuation header_block count le m ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      (exec_stmt fe ge locals le m (double_initialized_nest_code rest description) E0 le' m' Out_normal <->
       physical value m m' /\ le'=double_initialized_nest_exit rest (initialized_reduction_iterator description) count le)).
    { intros value le m le' m' RANGE [WORDS LOAD] VALUE.
      pose proof (@double_source_control_values controls valuation iterator value DISTINCT) as PARAMETERS.
      pose proof (@double_source_control_words controls valuation iterator value le DISTINCT WORDS VALUE) as EXTENDED.
      assert (CHILD_READY : double_initialized_nest_ready description ge count
        (map (double_source_control_value valuation iterator value) (controls++[iterator])) (length rest)).
      { pose proof (@double_initialized_nest_ready_child description ge count (map valuation controls)
          (length rest) value READY RANGE) as NEXT.
        exact (@eq_ind_r (list Z) (map valuation controls++[value])
          (fun prefix => double_initialized_nest_ready description ge count prefix (length rest)) NEXT
          (map (double_source_control_value valuation iterator value) (controls++[iterator])) PARAMETERS). }
      pose proof (@IH (controls++[iterator]) (double_source_control_value valuation iterator value) description
        le m le' m' CHILD_LEAF TAIL LOCAL HEADER CHILD_READY ltac:(split; assumption)) as CORRECT.
      unfold physical; rewrite <- PARAMETERS; exact CORRECT. }
    assert (HEADER_TEST : forall le m value,
      double_initialized_nest_entry controls valuation header_block count le m -> 0<=value<=Z.of_nat count ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      expression_test (double_matmul_long_condition iterator (initialized_reduction_header description))
        (Entry ge locals le m) (value <? Z.of_nat count)).
    { intros le m value [WORDS LOAD] RANGE VALUE; eapply double_matmul_global_test; eassumption. }
    assert (SET_ENTRY : forall le m value, double_initialized_nest_entry controls valuation header_block count le m ->
      double_initialized_nest_entry controls valuation header_block count (PTree.set iterator (Vlong (Int64.repr value)) le) m).
    { intros le m value [WORDS LOAD]; split; [|exact LOAD].
      intros key MEMBER; rewrite PTree.gso by (intro SAME; subst; contradiction); apply WORDS; exact MEMBER. }
    assert (BODY_ENTRY : forall value le m le' m', 0<=value<Z.of_nat count ->
      double_initialized_nest_entry controls valuation header_block count le m ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      exec_stmt fe ge locals le m (double_initialized_nest_code rest description) E0 le' m' Out_normal ->
      double_initialized_nest_entry controls valuation header_block count le' m').
    { intros value le m le' m' RANGE INV VALUE RUN.
      destruct (proj1 (@BRIDGE value le m le' m' RANGE INV VALUE) RUN) as [MODEL EXIT].
      destruct INV as [WORDS LOAD]; subst le'; split.
      - intros key MEMBER; rewrite double_initialized_nest_exit_frame;
          [apply WORDS; exact MEMBER|apply PREFIX_DISJOINT; apply in_or_app; auto].
      - destruct (@checked_double_initialized_reduction_sound p ((controls++[iterator])++rest)
          (double_initialized_reduction_code description) description CHILD_LEAF) as [_ [_ [_ STATIC]]].
        destruct (@double_initialized_reduction_static_sound p ((controls++[iterator])++rest) description STATIC)
          as [_ [_ [IW [RW CERTIFICATES]]]].
        unfold physical in MODEL.
        rewrite (@double_source_initialized_nest_preserves_global (length rest) description
          (map valuation controls++[value]) count ge (double_initialized_reduction_layouts description)
          m m' (initialized_reduction_header description) header_block Mint64 0 (proj2 HEADER) IW RW MODEL).
        exact LOAD. }
    cbn [double_initialized_nest_code length].
    rewrite double_source_initialized_nest_memory.
    pose proof (@memory_long_initialized_settled_equivalence fe ge locals iterator
      (double_matmul_long_condition iterator (initialized_reduction_header description))
      (double_initialized_nest_code rest description) (Z.of_nat count) 0
      (double_initialized_nest_entry controls valuation header_block count) physical
      (fun _ => double_initialized_nest_exit rest (initialized_reduction_iterator description) count)
      HEADER_TEST
      (@normal_statement_execution fe ge locals _
        (@checked_double_initialized_nest_normal p (controls++[iterator])
          (double_initialized_nest_code rest description) rest description CHILD_CHECK))
      ltac:(intros le m tr le' m' RUN; eapply writes_only_frame;
        [exact RUN|exact (@checked_double_initialized_nest_writes p (controls++[iterator])
          (double_initialized_nest_code rest description) rest description CHILD_CHECK)|exact OUTER_FRESH])
      BRIDGE BODY_ENTRY SET_ENTRY count temps memory after final eq_refl ltac:(lia) ENTRY) as CORRECT.
    rewrite double_initialized_nest_settled_exit in CORRECT by exact OUTER_FRESH; exact CORRECT.
Qed.

Theorem checked_double_initialized_nest_source_model controls valuation source outers description temps memory after final :
  checked_double_initialized_nest p controls source=Some (outers,description) ->
  locals_avoid (double_initialized_reduction_globals description) locals ->
  double_global_binding ge locals (initialized_reduction_header description) header_block ->
  double_initialized_nest_ready description ge count (map valuation controls) (length outers) ->
  double_initialized_nest_entry controls valuation header_block count temps memory ->
  (exec_stmt fe ge locals temps memory source E0 after final Out_normal <->
   SL.loop_semantics (double_source_initialized_nest_model
     (double_source_instruction_model (initialized_reduction_initial_instruction description))
     (double_source_instruction_model (initialized_reduction_body_instruction description)) (length outers)
     (length (map valuation controls))) (rev (map valuation controls)++[Z.of_nat count])
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts description)) memory)
     (RuntimeState (global_double_locations ge (double_initialized_reduction_layouts description)) final) /\
   after=double_initialized_nest_exit outers (initialized_reduction_iterator description) count temps).
Proof.
  intros CHECK LOCAL HEADER READY ENTRY.
  destruct (@checked_double_initialized_nest_sound p controls source outers description CHECK) as [CODE [LEAF FRESH]].
  rewrite CODE; eapply double_initialized_nest_canonical_source_model; eassumption.
Qed.
End SOURCE.

Print Assumptions double_initialized_nest_ready_child.
Print Assumptions double_initialized_nest_prefix_disjoint.
Print Assumptions double_initialized_nest_outer_fresh.
Print Assumptions double_initialized_nest_canonical_source_model.
Print Assumptions checked_double_initialized_nest_source_model.
