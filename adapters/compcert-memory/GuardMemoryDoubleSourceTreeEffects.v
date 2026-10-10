From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGlobalScope ClightRegionProgress ClightStructuredMemoryFrame.
From GuardMemory Require Import GuardMemoryValueInstr GuardMemoryDoubleLocations GuardMemoryDoubleAssignmentFactory
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleAffineSourceAccess GuardMemoryDoubleRawEffects
  GuardMemoryLongControl GuardMemoryLongProgressControl GuardMemoryLongLoopControl
  GuardMemoryLongRawLoadedProgress GuardMemoryLongRangeSource GuardMemoryDoubleSourceTreeData.
Import ListNotations.
Set Implicit Arguments.

Definition double_tree_write_global instruction :=
  fst (double_affine_source_function (double_source_write instruction)).
Definition double_tree_write_globals tree := map double_tree_write_global (double_source_tree_instructions tree).
Definition double_tree_header_leaf p instructions header target value := exists controls instruction,
  checked_double_source_instruction p controls (Sassign target value)=Some instruction /\
  In instruction instructions /\ double_tree_write_global instruction<>header.

Lemma double_source_tree_header_frame p controls tree :
  double_source_tree_checked p controls tree ->
  forall instructions header,
    incl (double_source_tree_instructions tree) instructions ->
    (forall instruction, In instruction instructions -> double_tree_write_global instruction<>header) ->
    structured_memory_frame (double_tree_header_leaf p instructions header) (double_source_tree_code tree).
Proof.
  revert controls; induction tree; intros controls CHECK instructions header INCLUDED DIFFERENT;
    cbn [double_source_tree_code].
  - exact I.
  - destruct (@checked_double_source_instruction_sound p controls body instruction CHECK) as [ASSIGN _].
    destruct (@decoded_double_assignment_shape body (double_source_assignment instruction) ASSIGN) as [rhs [SHAPE TYPE]].
    rewrite SHAPE in CHECK |- *; cbn [structured_memory_frame]; exists controls,instruction; split; [exact CHECK|].
    assert (MEMBER : In instruction instructions) by (apply INCLUDED; cbn; auto).
    split; [exact MEMBER|apply DIFFERENT; exact MEMBER].
  - destruct CHECK as [FIRST SECOND]; cbn [structured_memory_frame]; split.
    + eapply IHtree1; [exact FIRST| |exact DIFFERENT].
      intros instruction MEMBER; apply INCLUDED,in_or_app; left; exact MEMBER.
    + eapply IHtree2; [exact SECOND| |exact DIFFERENT].
      intros instruction MEMBER; apply INCLUDED,in_or_app; right; exact MEMBER.
  - destruct CHECK as [FRESH [HEADER CHILD]]; destruct raw;
      cbn [long_raw_from_loop long_raw_loaded_loop long_counter_increment
        memory_long_from_loop memory_long_frontend_loop memory_long_increment structured_memory_frame];
      repeat split; try exact I; eapply IHtree; eassumption.
Qed.

Theorem checked_double_source_raw_permissions p controls source description fe ge locals temps memory trace after final outcome :
  checked_double_source_instruction p controls source=Some description ->
  preserving_globals (globalenv p) ge -> locals_avoid [double_tree_write_global description] locals ->
  exec_stmt fe ge locals temps memory source trace after final outcome ->
  forall block offset kind permission,
    Mem.perm final block offset kind permission <-> Mem.perm memory block offset kind permission.
Proof.
  intros CHECK GLOBAL LOCAL RUN.
  destruct (@checked_double_source_raw_store p controls source description fe ge locals temps memory trace after final outcome
    CHECK GLOBAL LOCAL RUN) as [block [ofs [value [SYMBOL [STORE _]]]]].
  intros actual offset kind permission; split; intro PERM;
    [eapply Mem.perm_store_2|eapply Mem.perm_store_1]; eassumption.
Qed.

(** Whole-tree source effects, including every finite iteration and both sides
    of a sequence. No accepted guard or source/model point resolution is used. *)
Theorem checked_double_source_tree_raw_header_frame p controls tree fe ge locals temps memory trace after final outcome
  header header_block :
  double_source_tree_checked p controls tree -> double_source_tree_header_writes_check tree=true ->
  In header (double_source_tree_parameters tree) -> preserving_globals (globalenv p) ge ->
  locals_avoid (double_tree_write_globals tree) locals -> Genv.find_symbol ge header=Some header_block ->
  exec_stmt fe ge locals temps memory (double_source_tree_code tree) trace after final outcome ->
  (forall chunk offset, Mem.load chunk final header_block offset=Mem.load chunk memory header_block offset) /\
  (forall block offset kind permission,
    Mem.perm final block offset kind permission <-> Mem.perm memory block offset kind permission).
Proof.
  intros CHECK WRITES MEMBER GLOBAL LOCAL HEADER RUN.
  assert (FRAME : structured_memory_frame
    (double_tree_header_leaf p (double_source_tree_instructions tree) header) (double_source_tree_code tree)).
  { eapply double_source_tree_header_frame; [exact CHECK|apply incl_refl|].
    intros instruction POINT; eapply double_source_tree_header_writes_check_sound; eassumption. }
  set (relation := fun actual before final => locals_avoid (double_tree_write_globals tree) actual ->
    (forall chunk offset, Mem.load chunk final header_block offset=Mem.load chunk before header_block offset) /\
    (forall block offset kind permission,
      Mem.perm final block offset kind permission <-> Mem.perm before block offset kind permission)).
  assert (EFFECT : relation locals memory final).
  { eapply (@structured_memory_frame_execution ge
      (double_tree_header_leaf p (double_source_tree_instructions tree) header) relation).
    - intros actual before SCOPE; split; intros; reflexivity.
    - intros actual before middle completed FIRST SECOND SCOPE.
      destruct (FIRST SCOPE) as [LOAD1 PERM1]; destruct (SECOND SCOPE) as [LOAD2 PERM2].
      split; intros; [rewrite LOAD2,LOAD1; reflexivity|rewrite PERM2,PERM1; reflexivity].
    - intros entry actual current before target value events result completed out [layout [instruction [LEAF [POINT DIFFERENT]]]] STEP SCOPE.
      assert (SINGLE : locals_avoid [double_tree_write_global instruction] actual).
      { intros identifier INSIDE; cbn in INSIDE; destruct INSIDE as [SAME|[]]; subst identifier.
        apply SCOPE,in_map; exact POINT. }
      split.
      + intros chunk offset; eapply checked_double_source_raw_preserves_header; eassumption.
      + eapply checked_double_source_raw_permissions; eassumption.
    - exact RUN.
    - exact FRAME. }
  apply EFFECT; exact LOCAL.
Qed.

Print Assumptions double_source_tree_header_frame.
Print Assumptions checked_double_source_raw_permissions.
Print Assumptions checked_double_source_tree_raw_header_frame.
