From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGlobalScope ClightTempFrame ClightCondition ClightStructuredMemoryFrame ClightRegionProgress.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleAffineSourceAccess
  GuardMemoryDoubleHeaderFrame GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceTransport GuardMemoryDoubleInitializedReductionSource
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeEffects GuardMemoryDoubleRawEffects
  GuardMemoryDoubleSourceTreeSyntax GuardMemoryLongControl GuardMemoryLongRangeCaptureSource
  GuardMemoryLongSourceAffine.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Only headers on mathematically active paths require observations. Values for
    other parameter slots may be arbitrary; their child code is not reached. *)
Fixpoint double_source_tree_active_headers valuation tree : list ident := match tree with
  | DoubleTreeSkip | DoubleTreePoint _ _ => []
  | DoubleTreeSequence first second =>
      double_source_tree_active_headers valuation first++double_source_tree_active_headers valuation second
  | DoubleTreeRange _ _ start bound child => tree_bound_header bound::
      (if Int.signed start <? double_tree_bound_value valuation bound
       then double_source_tree_active_headers valuation child else [])
  end.
Lemma double_source_tree_active_headers_subset valuation tree :
  incl (double_source_tree_active_headers valuation tree) (double_source_tree_headers tree).
Proof.
  induction tree; intros key MEMBER; cbn [double_source_tree_active_headers double_source_tree_headers] in *;
    try contradiction.
  - apply in_app_or in MEMBER as [FIRST|SECOND]; apply in_or_app;
      [left; apply IHtree1|right; apply IHtree2]; assumption.
  - destruct MEMBER as [SAME|MEMBER]; [left; exact SAME|right].
    destruct (Int.signed start <? double_tree_bound_value valuation bound); [apply IHtree; exact MEMBER|contradiction].
Qed.
Definition double_source_tree_scope tree locals :=
  forall instruction, In instruction (double_source_tree_instructions tree) ->
    locals_avoid (double_source_instruction_globals instruction) locals.
Definition double_source_tree_shared_layout tree layouts :=
  forall instruction, In instruction (double_source_tree_instructions tree) ->
    double_source_layout_certificate instruction layouts.
Definition double_source_tree_header_exclusions tree headers :=
  forall instruction header, In instruction (double_source_tree_instructions tree) -> In header headers ->
    double_tree_write_global instruction<>header.
Definition double_source_tree_header_words ge locals headers (valuation : ident -> Z) memory :=
  forall header, In header headers -> exists block,
    double_global_binding ge locals header block /\
    Mem.load Mint64 memory block 0=Some (Vlong (Int64.repr (valuation header))).
Definition double_source_tree_entry ge locals headers header_values controls control_values temps memory :=
  double_source_prefix_words controls control_values temps /\
  double_source_tree_header_words ge locals headers header_values memory.

(** Domain facts are data about machine ranges and cell resolution, not callbacks
    asserting correctness of C source execution. A factory must produce them. *)
Fixpoint double_source_tree_model_facts tree controls header_values control_values ge layouts : Prop := match tree with
  | DoubleTreeSkip => True
  | DoubleTreePoint _ instruction => double_source_instruction_resolved instruction (map control_values controls) ge layouts
  | DoubleTreeSequence first second =>
      double_source_tree_model_facts first controls header_values control_values ge layouts /\
      double_source_tree_model_facts second controls header_values control_values ge layouts
  | DoubleTreeRange _ iterator start bound child =>
      Int64.min_signed<=double_tree_bound_value header_values bound<=Int64.max_signed /\
      forall value, Int.signed start<=value<double_tree_bound_value header_values bound ->
        double_source_tree_model_facts child (controls++[iterator]) header_values
          (double_source_control_value control_values iterator value) ge layouts
  end.
Lemma double_source_tree_scope_writes tree locals : double_source_tree_scope tree locals ->
  locals_avoid (double_tree_write_globals tree) locals.
Proof.
  intros SCOPE key MEMBER; unfold double_tree_write_globals in MEMBER.
  apply in_map_iff in MEMBER as [instruction [SAME POINT]]; subst key.
  apply (SCOPE instruction POINT); unfold double_source_instruction_globals,double_source_instruction_accesses,
    double_tree_write_global; cbn [map]; left; reflexivity.
Qed.

(** Generalize the previous whole-tree frame to observers unused by this subtree.
    The caller supplies write exclusions inherited from its enclosing checked
    region. This is the pre-guard transport needed for later sibling headers. *)
Theorem double_source_subtree_raw_header_frame p controls tree fe ge locals temps memory trace after final outcome
  header header_block :
  double_source_tree_checked p controls tree -> preserving_globals (globalenv p) ge ->
  locals_avoid (double_tree_write_globals tree) locals ->
  (forall instruction, In instruction (double_source_tree_instructions tree) -> double_tree_write_global instruction<>header) ->
  Genv.find_symbol ge header=Some header_block ->
  exec_stmt fe ge locals temps memory (double_source_tree_code tree) trace after final outcome ->
  (forall chunk offset, Mem.load chunk final header_block offset=Mem.load chunk memory header_block offset) /\
  (forall block offset kind permission,
    Mem.perm final block offset kind permission <-> Mem.perm memory block offset kind permission).
Proof.
  intros CHECK GLOBAL LOCAL DIFFERENT HEADER RUN.
  set (relation := fun actual before completed => locals_avoid (double_tree_write_globals tree) actual ->
    (forall chunk offset, Mem.load chunk completed header_block offset=Mem.load chunk before header_block offset) /\
    (forall block offset kind permission,
      Mem.perm completed block offset kind permission <-> Mem.perm before block offset kind permission)).
  assert (EFFECT : relation locals memory final).
  { eapply (@structured_memory_frame_execution ge
      (double_tree_header_leaf p (double_source_tree_instructions tree) header) relation).
    - intros actual before SCOPE; split; intros; reflexivity.
    - intros actual before middle completed FIRST SECOND SCOPE.
      destruct (FIRST SCOPE) as [LOAD1 PERM1]; destruct (SECOND SCOPE) as [LOAD2 PERM2].
      split; intros; [rewrite LOAD2,LOAD1; reflexivity|rewrite PERM2,PERM1; reflexivity].
    - intros entry actual current before target value events result completed out
        [layout [instruction [LEAF [POINT WRITE]]]] STEP SCOPE.
      assert (SINGLE : locals_avoid [double_tree_write_global instruction] actual).
      { intros identifier INSIDE; cbn in INSIDE; destruct INSIDE as [SAME|[]]; subst identifier.
        apply SCOPE,in_map; exact POINT. }
      split.
      + intros chunk offset; eapply checked_double_source_raw_preserves_header; eassumption.
      + eapply checked_double_source_raw_permissions; eassumption.
    - exact RUN.
    - eapply double_source_tree_header_frame; [exact CHECK|apply incl_refl|exact DIFFERENT]. }
  apply EFFECT; exact LOCAL.
Qed.
Theorem double_source_tree_entry_preserved p controls tree fe ge locals headers header_values control_values
  temps memory trace after final outcome :
  double_source_tree_checked p controls tree -> preserving_globals (globalenv p) ge ->
  double_source_tree_scope tree locals -> double_source_tree_header_exclusions tree headers ->
  double_source_tree_entry ge locals headers header_values controls control_values temps memory ->
  exec_stmt fe ge locals temps memory (double_source_tree_code tree) trace after final outcome ->
  double_source_tree_entry ge locals headers header_values controls control_values after final.
Proof.
  intros CHECK GLOBAL SCOPE EXCLUSIONS [WORDS HEADERS] RUN; split.
  - intros key MEMBER; rewrite (writes_only_frame RUN (@double_source_tree_writes_only p controls tree CHECK)
      key (@double_source_tree_writes_avoid p controls tree CHECK key MEMBER)); apply WORDS; exact MEMBER.
  - intros header MEMBER; destruct (HEADERS header MEMBER) as [block [BIND LOAD]].
    exists block; split; [exact BIND|].
    destruct (@double_source_subtree_raw_header_frame p controls tree fe ge locals temps memory trace after final outcome
      header block CHECK GLOBAL (double_source_tree_scope_writes SCOPE)
      ltac:(intros instruction POINT; apply EXCLUSIONS; assumption) (proj2 BIND) RUN) as [FRAME PERMISSIONS].
    rewrite FRAME; exact LOAD.
Qed.
Theorem double_tree_bound_observed_execution ge locals temps memory headers valuation bound :
  In (tree_bound_header bound) headers -> double_source_tree_header_words ge locals headers valuation memory ->
  eval_expr ge locals temps memory (double_tree_bound_code bound) (Vlong (Int64.repr (double_tree_bound_value valuation bound))).
Proof.
  intros MEMBER HEADERS; destruct (HEADERS _ MEMBER) as [block [BIND LOAD]].
  destruct bound as [header [offset|]]; cbn [double_tree_bound_code double_tree_bound_value] in *.
  - pose proof (@memory_long_offset_bound_execution ge locals temps memory header block
      (Int64.repr (valuation header)) offset BIND LOAD) as RUN.
    rewrite long_source_repr_sub in RUN; exact RUN.
  - change (eval_expr ge locals temps memory (Evar header memory_long_type) (Vlong (Int64.repr (valuation header-0)))).
    replace (valuation header-0) with (valuation header) by lia.
    exact (@memory_global_long_execution ge locals temps memory header block (Int64.repr (valuation header)) BIND LOAD).
Qed.

Print Assumptions double_source_tree_active_headers_subset.
Print Assumptions double_source_tree_scope_writes.
Print Assumptions double_source_subtree_raw_header_frame.
Print Assumptions double_source_tree_entry_preserved.
Print Assumptions double_tree_bound_observed_execution.
