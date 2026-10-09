From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightGlobalScope ClightRegionProgress ClightLoopSyntax ClightTempFrame.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDoubleLocations
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceLoopModel
  GuardMemoryDoubleHeaderInstruction GuardMemoryDoubleHeaderNestModel GuardMemoryDoubleHeaderFrame
  GuardMemoryDoubleInitializedReductionSource GuardMemoryDoubleInitializedNestData GuardMemoryDoubleInitializedNestSource
  GuardMemoryDoubleReductionNestData GuardMemoryDoubleReductionNestModel GuardMemoryDoubleAssignmentFactory
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryLongLoopSettle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_header_nest_ready instruction ge count prefix depth :=
  forall coordinates, length coordinates=depth -> Forall (fun value => 0<=value<Z.of_nat count) coordinates ->
    double_source_instruction_resolved instruction (Z.of_nat count::prefix++coordinates) ge (double_source_instruction_layouts instruction).
Lemma double_header_nest_ready_child instruction ge count prefix depth value :
  double_header_nest_ready instruction ge count prefix (S depth) -> 0<=value<Z.of_nat count ->
  double_header_nest_ready instruction ge count (prefix++[value]) depth.
Proof.
  intros READY RANGE coordinates LENGTH BOUNDS.
  pose proof (@READY (value::coordinates) ltac:(cbn; congruence) ltac:(constructor; assumption)) as RECEIPT.
  replace ((prefix++[value])++coordinates) with (prefix++value::coordinates) by (rewrite <- app_assoc; reflexivity).
  exact RECEIPT.
Qed.
Lemma checked_double_header_assignment_shape p header controls body instruction :
  checked_double_header_source_instruction p header controls body=Some instruction -> exists target rhs, body=Sassign target rhs.
Proof.
  intro CHECK; destruct (@checked_double_header_source_instruction_sound p header controls body instruction CHECK) as [DECODE REST].
  destruct (@decoded_double_assignment_shape body (double_source_assignment instruction) DECODE) as [rhs [CODE TYPE]].
  eexists; eexists; exact CODE.
Qed.

Section SOURCE.
Variable p : program.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable header : ident.
Variable header_block : block.
Variable count : nat.
Hypothesis GLOBAL : preserving_globals (globalenv p) ge.
Hypothesis UPPER : Z.of_nat count<=Int64.max_signed.

Theorem double_header_nest_canonical_source_model iterators :
  forall controls valuation body instruction temps memory after final,
  checked_double_header_source_instruction p header (header::controls++iterators) body=Some instruction ->
  double_initialized_nest_fresh (header::controls) iterators ->
  valuation header=Z.of_nat count ->
  locals_avoid (double_source_instruction_globals instruction) locals ->
  double_global_binding ge locals header header_block ->
  fst (value_instruction_write (double_source_instruction_model instruction))<>header ->
  double_header_nest_ready instruction ge count (map valuation controls) (length iterators) ->
  double_initialized_nest_entry controls valuation header_block count temps memory ->
  (exec_stmt fe ge locals temps memory (double_reduction_nest_code iterators header body) E0 after final Out_normal <->
   SL.loop_semantics (double_header_nest_model (double_source_instruction_model instruction) (length iterators)
     (length (map valuation controls))) (rev (map valuation controls)++[Z.of_nat count])
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts instruction)) memory)
     (RuntimeState (global_double_locations ge (double_source_instruction_layouts instruction)) final) /\
   after=double_reduction_nest_exit iterators count temps).
Proof.
  induction iterators as [|iterator rest IH]; intros controls valuation body instruction temps memory after final
    LEAF FRESH HEADER_VALUE LOCAL HEADER WRITE READY ENTRY.
  - rewrite app_nil_r in LEAF.
    pose proof (@READY [] eq_refl ltac:(constructor)) as RESOLVED; rewrite app_nil_r in RESOLVED.
    destruct RESOLVED as [write [reads [WR RR]]].
    assert (PARAMETERS : map valuation (header::controls)=Z.of_nat count::map valuation controls).
    { cbn; rewrite HEADER_VALUE; reflexivity. }
    assert (OBSERVED : eval_expr ge locals temps memory (Evar header memory_long_type)
      (Vlong (Int64.repr (valuation header)))).
    { rewrite HEADER_VALUE; eapply memory_global_long_execution; [exact HEADER|exact (proj2 ENTRY)]. }
    assert (VIEW : forall identifier, In identifier (header::controls) -> identifier<>header ->
      temps ! identifier=Some (Vlong (Int64.repr (valuation identifier)))).
    { intros identifier [SAME|MEMBER] DIFFERENT; [congruence|apply (proj1 ENTRY); exact MEMBER]. }
    destruct (@checked_double_header_source_instruction_sound p header (header::controls) body instruction LEAF)
      as [_ [_ [_ REGISTRY]]].
    pose proof (@checked_double_header_source_shared_execution_iff p header (header::controls) body instruction
      valuation fe ge locals temps memory (double_source_instruction_layouts instruction) write reads final
      LEAF (@checked_double_source_layout_certificate instruction _ REGISTRY) GLOBAL LOCAL OBSERVED VIEW
      ltac:(rewrite <- HEADER_VALUE in WR; exact WR)
      ltac:(rewrite <- HEADER_VALUE in RR; exact RR)) as BRIDGE.
    cbn [map] in BRIDGE; rewrite HEADER_VALUE in BRIDGE.
    cbn [double_reduction_nest_code double_header_nest_model length]; rewrite double_header_instruction_Loop.
    rewrite double_reduction_nest_exit_nil; unfold double_source_model_point; split.
    + intro RUN; pose proof (@checked_double_header_source_assignment_effects p header (header::controls) body instruction fe ge locals
        temps memory E0 after final Out_normal LEAF RUN) as [_ [TEMPS NORMAL]].
      subst after; split; [apply BRIDGE; exact RUN|reflexivity].
    + intros [MODEL SAME]; subst after; apply BRIDGE; exact MODEL.
  - destruct FRESH as [DISTINCT TAIL].
    assert (CHILD_LEAF : checked_double_header_source_instruction p header (header::(controls++[iterator])++rest) body=Some instruction).
    { replace (header::(controls++[iterator])++rest) with (header::controls++iterator::rest) by (rewrite <- app_assoc; reflexivity); exact LEAF. }
    assert (OUTER_FRESH : ~ In iterator rest).
    { intro MEMBER; apply (@double_initialized_nest_fresh_disjoint (header::controls++[iterator]) rest TAIL iterator MEMBER).
      right; apply in_or_app; right; cbn; auto. }
    assert (PREFIX_DISJOINT : forall key, In key controls -> ~ In key rest).
    { intros key MEMBER WRITTEN; apply (@double_initialized_nest_fresh_disjoint (header::controls++[iterator]) rest TAIL key WRITTEN).
      right; apply in_or_app; auto. }
    assert (PREFIX_FRESH : ~ In iterator controls) by (intro MEMBER; apply DISTINCT; right; exact MEMBER).
    assert (HEADER_FRESH : header<>iterator) by (intro SAME; subst iterator; apply DISTINCT; left; reflexivity).
    set (physical := fun value first last => SL.loop_semantics
      (double_header_nest_model (double_source_instruction_model instruction) (length rest)
        (length (map valuation controls++[value]))) (rev (map valuation controls++[value])++[Z.of_nat count])
      (RuntimeState (global_double_locations ge (double_source_instruction_layouts instruction)) first)
      (RuntimeState (global_double_locations ge (double_source_instruction_layouts instruction)) last)).
    assert (BRIDGE : forall value le m le' m', 0<=value<Z.of_nat count ->
      double_initialized_nest_entry controls valuation header_block count le m ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      (exec_stmt fe ge locals le m (double_reduction_nest_code rest header body) E0 le' m' Out_normal <->
       physical value m m' /\ le'=double_reduction_nest_exit rest count le)).
    { intros value le m le' m' RANGE [WORDS LOAD] VALUE.
      pose proof (@double_source_control_values controls valuation iterator value PREFIX_FRESH) as PARAMETERS.
      pose proof (@double_source_control_words controls valuation iterator value le PREFIX_FRESH WORDS VALUE) as EXTENDED.
      assert (CHILD_READY : double_header_nest_ready instruction ge count
        (map (double_source_control_value valuation iterator value) (controls++[iterator])) (length rest)).
      { pose proof (@double_header_nest_ready_child instruction ge count (map valuation controls)
          (length rest) value READY RANGE) as NEXT.
        exact (@eq_ind_r (list Z) (map valuation controls++[value])
          (fun prefix => double_header_nest_ready instruction ge count prefix (length rest)) NEXT
          (map (double_source_control_value valuation iterator value) (controls++[iterator])) PARAMETERS). }
      pose proof (@IH (controls++[iterator]) (double_source_control_value valuation iterator value) body instruction
        le m le' m' CHILD_LEAF TAIL ltac:(unfold double_source_control_value; destruct (peq header iterator); congruence) LOCAL HEADER WRITE CHILD_READY ltac:(split; assumption)) as CORRECT.
      unfold physical; rewrite <- PARAMETERS; exact CORRECT. }
    assert (HEADER_TEST : forall le m value,
      double_initialized_nest_entry controls valuation header_block count le m -> 0<=value<=Z.of_nat count ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      expression_test (double_matmul_long_condition iterator header) (Entry ge locals le m) (value <? Z.of_nat count)).
    { intros le m value [WORDS LOAD] RANGE VALUE; eapply double_matmul_global_test; eassumption. }
    assert (SET_ENTRY : forall le m value, double_initialized_nest_entry controls valuation header_block count le m ->
      double_initialized_nest_entry controls valuation header_block count (PTree.set iterator (Vlong (Int64.repr value)) le) m).
    { intros le m value [WORDS LOAD]; split; [|exact LOAD].
      intros key MEMBER; rewrite PTree.gso by (intro SAME; subst; apply DISTINCT; right; exact MEMBER); apply WORDS; exact MEMBER. }
    assert (BODY_ENTRY : forall value le m le' m', 0<=value<Z.of_nat count ->
      double_initialized_nest_entry controls valuation header_block count le m ->
      le ! iterator=Some (Vlong (Int64.repr value)) ->
      exec_stmt fe ge locals le m (double_reduction_nest_code rest header body) E0 le' m' Out_normal ->
      double_initialized_nest_entry controls valuation header_block count le' m').
    { intros value le m le' m' RANGE INV VALUE RUN.
      destruct (proj1 (@BRIDGE value le m le' m' RANGE INV VALUE) RUN) as [MODEL EXIT].
      destruct INV as [WORDS LOAD]; subst le'; split.
      - intros key MEMBER; rewrite double_reduction_nest_exit_frame;
          [apply WORDS; exact MEMBER|apply PREFIX_DISJOINT; exact MEMBER].
      - unfold physical in MODEL.
        rewrite (@double_header_nest_preserves_global (length rest) instruction (map valuation controls++[value]) count
          ge (double_source_instruction_layouts instruction) m m' header header_block Mint64 0 (proj2 HEADER) WRITE MODEL).
        exact LOAD. }
    cbn [double_reduction_nest_code length]; rewrite double_header_nest_memory.
    pose proof (@memory_long_initialized_settled_equivalence fe ge locals iterator
      (double_matmul_long_condition iterator header) (double_reduction_nest_code rest header body) (Z.of_nat count) 0
      (double_initialized_nest_entry controls valuation header_block count) physical
      (fun _ => double_reduction_nest_exit rest count) HEADER_TEST
      (@normal_statement_execution fe ge locals _ (@double_reduction_nest_normal rest header body
        (@checked_double_header_assignment_shape p header (header::(controls++[iterator])++rest) body instruction CHILD_LEAF)))
      ltac:(intros le m tr le' m' RUN; eapply writes_only_frame;
        [exact RUN|exact (@double_reduction_nest_writes rest header body
          (@checked_double_header_assignment_shape p header (header::(controls++[iterator])++rest) body instruction CHILD_LEAF))|exact OUTER_FRESH])
      BRIDGE BODY_ENTRY SET_ENTRY count temps memory after final eq_refl ltac:(lia) ENTRY) as CORRECT.
    rewrite double_reduction_nest_settled_exit in CORRECT by exact OUTER_FRESH; exact CORRECT.
Qed.
End SOURCE.

Print Assumptions double_header_nest_ready_child.
Print Assumptions checked_double_header_assignment_shape.
Print Assumptions double_header_nest_canonical_source_model.
