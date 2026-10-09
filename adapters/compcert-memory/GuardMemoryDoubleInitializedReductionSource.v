From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Clight ClightBigstep.
From polcert.src Require Import PolyBase.
From Guard Require Import CompCertMemoryActions ClightCondition ClightCountedLoop ClightGlobalScope
  ClightRegionProgress ClightLoopSyntax.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryValueInstr GuardMemoryDynamicTensorLayout
  GuardMemoryDoubleValue GuardMemoryDoubleLocations GuardMemoryDoubleAssignment
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleSourceLoopModel
  GuardMemoryDoubleInitializedReductionData GuardMemoryDoubleHeaderFrame GuardMemoryDoubleProgramBindings
  GuardMemoryLongControl GuardMemoryLongLoopControl GuardMemoryLongLoopSettle GuardMemoryDoubleMatmulLoops.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_source_prefix_words controls valuation (temps : temp_env) :=
  forall identifier, In identifier controls -> temps ! identifier=Some (Vlong (Int64.repr (valuation identifier))).
Definition double_source_control_value (valuation : ident -> Z) iterator (value : Z) identifier :=
  if peq identifier iterator then value else valuation identifier.
Lemma double_source_control_values controls valuation iterator value :
  ~ In iterator controls ->
  map (double_source_control_value valuation iterator value) (controls++[iterator])=map valuation controls++[value].
Proof.
  intro DISTINCT; rewrite map_app; f_equal.
  - apply map_ext_in; intros identifier MEMBER; unfold double_source_control_value.
    destruct (peq identifier iterator); [subst; contradiction|reflexivity].
  - cbn [map]; unfold double_source_control_value;
      destruct (peq iterator iterator); [reflexivity|contradiction].
Qed.
Lemma double_source_control_words controls valuation iterator value temps :
  ~ In iterator controls -> double_source_prefix_words controls valuation temps ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  double_source_prefix_words (controls++[iterator]) (double_source_control_value valuation iterator value) temps.
Proof.
  intros DISTINCT PREFIX VALUE identifier MEMBER; apply in_app_iff in MEMBER as [MEMBER|SINGLE];
    unfold double_source_control_value.
  - destruct (peq identifier iterator); [subst; contradiction|apply PREFIX; exact MEMBER].
  - cbn in SINGLE; destruct SINGLE as [SAME|IMPOSSIBLE]; [subst identifier|contradiction].
    destruct (peq iterator iterator); [exact VALUE|contradiction].
Qed.
Definition double_source_instruction_resolved description parameters ge layouts := exists write reads,
  global_double_locations ge layouts (exact_cell (value_instruction_write (double_source_instruction_model description)) parameters)=Some write /\
  resolve_cells (map (fun access => exact_cell access parameters)
    (value_instruction_reads (double_source_instruction_model description))) (global_double_locations ge layouts)=Some reads.
Lemma double_initialized_reduction_scope description locals :
  locals_avoid (double_initialized_reduction_globals description) locals ->
  locals_avoid (double_source_instruction_globals (initialized_reduction_initial_instruction description)) locals /\
  locals_avoid (double_source_instruction_globals (initialized_reduction_body_instruction description)) locals.
Proof.
  intro LOCAL; split; intros identifier MEMBER; apply LOCAL; right;
    unfold double_source_instruction_globals in MEMBER;
    unfold double_initialized_reduction_accesses; rewrite map_app; apply in_or_app; auto.
Qed.
Lemma double_source_identity_loop_exit iterator count temps :
  memory_long_settled_exit iterator (fun _ le => le) count 0 (PTree.set iterator (Vlong Int64.zero) temps)=
  PTree.set iterator (Vlong (Int64.repr (Z.of_nat count))) temps.
Proof.
  destruct count as [|count]; [reflexivity|].
  rewrite (@memory_long_constant_settle_exit iterator (fun le => le)
    ltac:(intro le; reflexivity) ltac:(intros le word; reflexivity) count 0).
  rewrite Z.add_0_l,PTree.set2; reflexivity.
Qed.
Lemma checked_double_initialized_reduction_header_binding p controls source description ge locals :
  checked_double_initialized_reduction p controls source=Some description ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_initialized_reduction_globals description) locals ->
  exists block, double_global_binding ge locals (initialized_reduction_header description) block.
Proof.
  intros CHECK GLOBAL LOCAL.
  destruct (@checked_double_initialized_reduction_sound p controls source description CHECK) as [_ [_ [_ STATIC]]].
  destruct (@double_initialized_reduction_static_sound p controls description STATIC) as [_ [DECL _]].
  eapply (@checked_global_binding p [(initialized_reduction_header description,memory_long_type)] ge locals
    (initialized_reduction_header description) memory_long_type).
  - unfold global_declarations_check; cbn [forallb]; rewrite DECL; reflexivity.
  - cbn; auto.
  - exact GLOBAL.
  - intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|IMPOSSIBLE];
      [subst identifier|contradiction]; apply LOCAL; left; reflexivity.
Qed.

Section INITIALIZED_REDUCTION.
Variable p : program.
Variable controls : list ident.
Variable source : statement.
Variable description : double_initialized_reduction.
Variable valuation : ident -> Z.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable ge : genv.
Variable locals : env.
Variable header_block : block.
Variable count : nat.
Hypothesis CHECK : checked_double_initialized_reduction p controls source=Some description.
Hypothesis GLOBAL : preserving_globals (globalenv p) ge.
Hypothesis LOCAL : locals_avoid (double_initialized_reduction_globals description) locals.
Hypothesis HEADER_BIND : double_global_binding ge locals (initialized_reduction_header description) header_block.
Hypothesis UPPER : Z.of_nat count<=Int64.max_signed.
Hypothesis INITIAL_RESOLVED : double_source_instruction_resolved (initialized_reduction_initial_instruction description)
  (map valuation controls) ge (double_initialized_reduction_layouts description).
Hypothesis BODY_RESOLVED : forall value, 0<=value<Z.of_nat count ->
  double_source_instruction_resolved (initialized_reduction_body_instruction description)
    (map valuation controls++[value]) ge (double_initialized_reduction_layouts description).

Let iterator := initialized_reduction_iterator description.
Let initializer := initialized_reduction_initial_instruction description.
Let reduction := initialized_reduction_body_instruction description.
Let layouts := double_initialized_reduction_layouts description.
Let initial_model := double_source_instruction_model initializer.
Let reduction_model := double_source_instruction_model reduction.
Let prefix := map valuation controls.
Definition double_initialized_reduction_entry temps memory :=
  double_source_prefix_words controls valuation temps /\
  Mem.load Mint64 memory header_block 0=Some (Vlong (Int64.repr (Z.of_nat count))).
Definition double_initialized_reduction_point value before after :=
  double_source_model_point reduction_model (prefix++[value])
    (RuntimeState (global_double_locations ge layouts) before) (RuntimeState (global_double_locations ge layouts) after).

Lemma initialized_reduction_certificates :
  checked_double_source_instruction p controls (initialized_reduction_initializer description)=Some initializer /\
  checked_double_source_instruction p (controls++[iterator]) (initialized_reduction_body description)=Some reduction /\
  ~ In iterator controls /\
  fst (value_instruction_write initial_model)<>initialized_reduction_header description /\
  fst (value_instruction_write reduction_model)<>initialized_reduction_header description /\
  double_source_layout_certificate initializer layouts /\ double_source_layout_certificate reduction layouts.
Proof.
  destruct (@checked_double_initialized_reduction_sound p controls source description CHECK) as [CODE [INITIAL [BODY STATIC]]].
  destruct (@double_initialized_reduction_static_sound p controls description STATIC)
    as [DISTINCT [DECL [IW [RW [IL RL]]]]].
  repeat split; assumption.
Qed.

Lemma double_initialized_reduction_body_bridge value temps memory after final :
  0<=value<Z.of_nat count -> double_initialized_reduction_entry temps memory ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  (exec_stmt fe ge locals temps memory (initialized_reduction_body description) E0 after final Out_normal <->
   double_initialized_reduction_point value memory final /\ after=temps).
Proof.
  intros RANGE [PREFIX LOAD] VALUE.
  destruct initialized_reduction_certificates as [IC [BC [DISTINCT [IW [RW [IL RL]]]]]].
  destruct (double_initialized_reduction_scope LOCAL) as [LI LR].
  pose proof (@double_source_control_words controls valuation iterator value temps DISTINCT PREFIX VALUE) as WORDS.
  destruct (@BODY_RESOLVED value RANGE) as [write [reads [WRITE READS]]].
  pose proof (@double_source_control_values controls valuation iterator value DISTINCT) as PARAMETERS.
  rewrite <- PARAMETERS in WRITE,READS.
  split.
  - intro RUN; destruct (@checked_double_source_shared_execution p (controls++[iterator])
      (initialized_reduction_body description) reduction (double_source_control_value valuation iterator value)
      fe ge locals temps memory layouts write reads E0 after final Out_normal BC RL GLOBAL LR WORDS WRITE READS RUN)
      as [TRACE [TEMPS [OUTCOME MODEL]]].
    split; [|exact TEMPS]; unfold double_initialized_reduction_point,double_source_model_point,prefix;
      rewrite <- PARAMETERS; exact MODEL.
  - intros [MODEL TEMPS]; subst after.
    apply (proj2 (@checked_double_source_shared_execution_iff p (controls++[iterator])
      (initialized_reduction_body description) reduction (double_source_control_value valuation iterator value)
      fe ge locals temps memory layouts write reads final BC RL GLOBAL LR WORDS WRITE READS)).
    unfold double_initialized_reduction_point,double_source_model_point,prefix in MODEL;
      rewrite <- PARAMETERS in MODEL; exact MODEL.
Qed.
Lemma double_initialized_reduction_set_entry temps memory value :
  double_initialized_reduction_entry temps memory ->
  double_initialized_reduction_entry (PTree.set iterator (Vlong (Int64.repr value)) temps) memory.
Proof.
  intros [PREFIX LOAD]; split; [|exact LOAD].
  destruct initialized_reduction_certificates as [_ [_ [DISTINCT _]]].
  intros identifier MEMBER; rewrite PTree.gso; [apply PREFIX; exact MEMBER|intro SAME; subst; contradiction].
Qed.
Lemma double_initialized_reduction_body_entry value temps memory after final :
  0<=value<Z.of_nat count -> double_initialized_reduction_entry temps memory ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  exec_stmt fe ge locals temps memory (initialized_reduction_body description) E0 after final Out_normal ->
  double_initialized_reduction_entry after final.
Proof.
  intros RANGE ENTRY VALUE RUN.
  destruct (proj1 (@double_initialized_reduction_body_bridge value temps memory after final RANGE ENTRY VALUE) RUN) as [MODEL TEMPS].
  destruct ENTRY as [PREFIX LOAD]; subst after; split; [exact PREFIX|].
  destruct initialized_reduction_certificates as [_ [_ [_ [_ [RW _]]]]].
  rewrite (@double_source_model_preserves_global reduction (prefix++[value]) ge layouts memory final
    (initialized_reduction_header description) header_block Mint64 0 (proj2 HEADER_BIND) RW MODEL); exact LOAD.
Qed.
Lemma double_initialized_reduction_header temps memory value :
  double_initialized_reduction_entry temps memory -> 0<=value<=Z.of_nat count ->
  temps ! iterator=Some (Vlong (Int64.repr value)) ->
  expression_test (double_matmul_long_condition iterator (initialized_reduction_header description))
    (Entry ge locals temps memory) (value <? Z.of_nat count).
Proof.
  intros [PREFIX LOAD] RANGE VALUE; exists (Val.of_bool (value <? Z.of_nat count)); split.
  - eapply memory_long_test_execution; try reflexivity.
    + pose proof Int64.min_signed_neg; lia.
    + pose proof Int64.min_signed_neg; pose proof (Nat2Z.is_nonneg count); lia.
    + constructor; exact VALUE.
    + eapply memory_global_long_execution; eassumption.
  - destruct (value <? Z.of_nat count); reflexivity.
Qed.
Theorem double_initialized_reduction_loop_equivalence temps memory after final :
  double_initialized_reduction_entry temps memory ->
  (exec_stmt fe ge locals temps memory
    (memory_long_initialized_loop iterator (double_matmul_long_condition iterator (initialized_reduction_header description))
      (initialized_reduction_body description)) E0 after final Out_normal <->
   counted_iterations double_initialized_reduction_point count 0 memory final /\
   after=PTree.set iterator (Vlong (Int64.repr (Z.of_nat count))) temps).
Proof.
  intro ENTRY.
  destruct initialized_reduction_certificates as [IC [BC REST]].
  pose proof (@memory_long_initialized_settled_equivalence fe ge locals iterator
    (double_matmul_long_condition iterator (initialized_reduction_header description))
    (initialized_reduction_body description) (Z.of_nat count) 0 double_initialized_reduction_entry
    double_initialized_reduction_point (fun _ le => le) double_initialized_reduction_header
    ltac:(intros le m tr le' m' out RUN; exact (proj2 (proj2
      (@checked_double_source_assignment_effects p (controls++[iterator]) (initialized_reduction_body description)
        reduction fe ge locals le m tr le' m' out BC RUN))))
    ltac:(intros le m tr le' m' RUN; pose proof (@checked_double_source_assignment_effects p
      (controls++[iterator]) (initialized_reduction_body description) reduction fe ge locals le m tr le' m'
      Out_normal BC RUN) as [_ [SAME OUT]]; subst le'; reflexivity)
    double_initialized_reduction_body_bridge double_initialized_reduction_body_entry double_initialized_reduction_set_entry
    count temps memory after final eq_refl ltac:(lia) ENTRY) as BRIDGE.
  rewrite double_source_identity_loop_exit in BRIDGE; exact BRIDGE.
Qed.

Theorem double_initialized_reduction_source_model temps memory after final :
  double_initialized_reduction_entry temps memory ->
  (exec_stmt fe ge locals temps memory source E0 after final Out_normal <->
   SL.loop_semantics (double_source_initialized_reduction_model initial_model reduction_model (length controls))
     (rev prefix++[Z.of_nat count])
     (RuntimeState (global_double_locations ge layouts) memory) (RuntimeState (global_double_locations ge layouts) final) /\
   after=PTree.set iterator (Vlong (Int64.repr (Z.of_nat count))) temps).
Proof.
  intro ENTRY.
  destruct (@checked_double_initialized_reduction_sound p controls source description CHECK) as [CODE _].
  rewrite CODE; unfold double_initialized_reduction_code.
  assert (LENGTH : length prefix=length controls) by (unfold prefix; apply map_length).
  rewrite <- LENGTH, double_source_initialized_reduction_model_memory.
  destruct initialized_reduction_certificates as [IC [BC [DISTINCT [IW [RW [IL RL]]]]]].
  destruct (double_initialized_reduction_scope LOCAL) as [LI LR].
  destruct INITIAL_RESOLVED as [write [reads [WRITE READS]]].
  destruct ENTRY as [PREFIX LOAD]; split.
  - intro RUN; destruct (sequence_normal_decode RUN) as [middle_temps [middle [FIRST SECOND]]].
    destruct (@checked_double_source_shared_execution p controls (initialized_reduction_initializer description)
      initializer valuation fe ge locals temps memory layouts write reads E0 middle_temps middle Out_normal
      IC IL GLOBAL LI PREFIX WRITE READS FIRST) as [_ [TEMPS [_ MODEL]]]; subst middle_temps.
    assert (READY : double_initialized_reduction_entry temps middle).
    { split; [exact PREFIX|].
      rewrite (@double_source_model_preserves_global initializer prefix ge layouts memory middle
        (initialized_reduction_header description) header_block Mint64 0 (proj2 HEADER_BIND) IW MODEL); exact LOAD. }
    destruct (proj1 (@double_initialized_reduction_loop_equivalence temps middle after final READY) SECOND) as [ITER EXIT].
    split; [exists middle; split; [exact MODEL|exact ITER]|exact EXIT].
  - intros [[middle [MODEL ITER]] EXIT]; subst after.
    assert (FIRST : exec_stmt fe ge locals temps memory (initialized_reduction_initializer description) E0 temps middle Out_normal).
    { apply (proj2 (@checked_double_source_shared_execution_iff p controls
        (initialized_reduction_initializer description) initializer valuation fe ge locals temps memory layouts write reads
        middle IC IL GLOBAL LI PREFIX WRITE READS)); exact MODEL. }
    assert (READY : double_initialized_reduction_entry temps middle).
    { split; [exact PREFIX|].
      rewrite (@double_source_model_preserves_global initializer prefix ge layouts memory middle
        (initialized_reduction_header description) header_block Mint64 0 (proj2 HEADER_BIND) IW MODEL); exact LOAD. }
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); [exact FIRST|].
    apply (proj2 (@double_initialized_reduction_loop_equivalence temps middle
      (PTree.set iterator (Vlong (Int64.repr (Z.of_nat count))) temps) final READY)); split; [exact ITER|reflexivity].
Qed.
End INITIALIZED_REDUCTION.

Print Assumptions double_source_control_values.
Print Assumptions double_source_control_words.
Print Assumptions double_initialized_reduction_scope.
Print Assumptions double_source_identity_loop_exit.
Print Assumptions checked_double_initialized_reduction_header_binding.
Print Assumptions double_initialized_reduction_body_bridge.
Print Assumptions double_initialized_reduction_loop_equivalence.
Print Assumptions double_initialized_reduction_source_model.
