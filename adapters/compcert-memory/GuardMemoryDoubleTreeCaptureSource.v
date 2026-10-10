From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightLoopSyntax ClightGlobalScope ClightRegionProgress ClightTempFrame.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleProgramBindings
  GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeState GuardMemoryDoubleTreeCaptureLicense
  GuardMemoryDoubleTreeCaptureData GuardMemoryDoubleTreeCaptureControl GuardMemoryDoubleTreeCaptureReceipt
  GuardMemoryLongControl GuardMemoryLongExpressionCapture GuardMemoryRectangularCapture.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Semantic source executions are used exclusively inside this safety proof.
    The generated code performs header checks, not source preexecution. Raw
    effects transport later-sibling loads to the unchanged guard memory. *)
Theorem double_tree_capture_source_licensed tree :
  forall p controls fe ge locals headers source_temps source_memory source_after source_final
    temps guard_memory cache flag lower upper accepted_before,
  double_source_tree_checked p controls tree -> preserving_globals (globalenv p) ge ->
  double_source_tree_scope tree locals -> double_source_tree_header_exclusions tree headers ->
  incl (double_source_tree_headers tree) headers -> locals_avoid headers locals ->
  (forall header, In header headers -> Int.min_signed<=lower header<=Int.max_signed /\
    Int.min_signed<=upper header<=Int.max_signed) ->
  double_tree_header_loads_equal ge headers source_memory guard_memory ->
  double_tree_flag_value temps flag accepted_before ->
  exec_stmt fe ge locals source_temps source_memory (double_source_tree_code tree) E0 source_after source_final Out_normal ->
  exists after accepted, double_tree_capture_receipt ge locals guard_memory cache flag lower upper tree temps after accepted.
Proof.
  induction tree; intros p controls fe ge locals headers source_temps source_memory source_after source_final
    temps guard_memory cache flag lower upper accepted_before CHECK GLOBAL SCOPE EXCLUSIONS HEADERS LOCAL LIMITS EQUAL FLAG RUN.
  all: destruct accepted_before; [|exists temps,false; apply double_tree_receipt_disabled; exact FLAG].
  - exists temps,true; apply double_tree_receipt_skip; exact FLAG.
  - exists temps,true; apply double_tree_receipt_point; exact FLAG.
  - destruct CHECK as [FIRST SECOND].
    destruct (sequence_normal_decode RUN) as [middle [middle_memory [RUN1 RUN2]]].
    assert (SCOPE1 : double_source_tree_scope tree1 locals).
    { intros instruction MEMBER; apply SCOPE; cbn; apply in_or_app; left; exact MEMBER. }
    assert (EXCLUSIONS1 : double_source_tree_header_exclusions tree1 headers).
    { intros instruction header POINT MEMBER; apply EXCLUSIONS; [cbn; apply in_or_app; left|]; assumption. }
    destruct (@IHtree1 p controls fe ge locals headers source_temps source_memory middle middle_memory
      temps guard_memory cache flag lower upper true FIRST GLOBAL SCOPE1 EXCLUSIONS1
      ltac:(intros header MEMBER; apply HEADERS; cbn; apply in_or_app; left; exact MEMBER)
      LOCAL LIMITS EQUAL FLAG RUN1) as [prepared [first_accepted RECEIPT1]].
    pose proof (@double_tree_header_loads_after_source p controls tree1 fe ge locals headers source_temps source_memory
      guard_memory middle middle_memory FIRST GLOBAL SCOPE1 EXCLUSIONS1 EQUAL RUN1) as MIDDLE.
    destruct (@IHtree2 p controls fe ge locals headers middle middle_memory source_after source_final
      prepared guard_memory cache flag lower upper first_accepted SECOND GLOBAL
      ltac:(intros instruction MEMBER; apply SCOPE; cbn; apply in_or_app; right; exact MEMBER)
      ltac:(intros instruction header POINT MEMBER; apply EXCLUSIONS; [cbn; apply in_or_app; right|]; assumption)
      ltac:(intros header MEMBER; apply HEADERS; cbn; apply in_or_app; right; exact MEMBER)
      LOCAL LIMITS MIDDLE (double_tree_capture_receipt_flag RECEIPT1) RUN2) as [after [accepted RECEIPT2]].
    exists after,accepted; eapply double_tree_receipt_sequence; eassumption.
  - destruct CHECK as [FRESH [DECL CHILD]].
    assert (MEMBER : In (tree_bound_header bound) headers) by (apply HEADERS; cbn; left; reflexivity).
    assert (DECLS : global_declarations_check p [(tree_bound_header bound,memory_long_type)]=true).
    { unfold global_declarations_check; cbn [forallb]; rewrite DECL; reflexivity. }
    destruct (@checked_global_binding p [(tree_bound_header bound,memory_long_type)] ge locals
      (tree_bound_header bound) memory_long_type DECLS (or_introl eq_refl) GLOBAL
      ltac:(intros key [SAME|[]]; subst key; apply LOCAL; exact MEMBER)) as [block BIND].
    destruct (@double_tree_range_first_load p controls raw iterator start bound tree fe ge locals source_temps
      source_memory source_after source_final block CHILD BIND RUN) as [input [LOAD CHILD_RUN]].
    assert (GUARD_LOAD : Mem.load Mint64 guard_memory block 0=Some (Vlong input)).
    { rewrite <- (EQUAL _ _ MEMBER (proj2 BIND)); exact LOAD. }
    destruct (LIMITS _ MEMBER) as [LOW HIGH].
    destruct (double_tree_capture_accept bound input lower upper) eqn:ACCEPT.
    + destruct (double_tree_word_active start bound input) eqn:ACTIVE.
      * apply Z.ltb_lt in ACTIVE.
        destruct (CHILD_RUN ACTIVE) as [child_after [child_final CHILD_SOURCE]].
        assert (CHILD_FLAG : double_tree_flag_value (double_tree_captured temps bound cache flag input lower upper) flag true).
        { unfold double_tree_flag_value; rewrite double_tree_captured_flag,ACCEPT; reflexivity. }
        destruct (@IHtree p (controls++[iterator]) fe ge locals headers
          (PTree.set iterator (Vlong (Int64.repr (Int.signed start))) source_temps) source_memory child_after child_final
          (double_tree_captured temps bound cache flag input lower upper) guard_memory cache flag lower upper true
          CHILD GLOBAL SCOPE EXCLUSIONS
          ltac:(intros header INSIDE; apply HEADERS; cbn; right; exact INSIDE)
          LOCAL LIMITS EQUAL CHILD_FLAG CHILD_SOURCE) as [after [accepted RECEIPT]].
        exists after,accepted; eapply double_tree_receipt_child; try eassumption; apply Z.ltb_lt; exact ACTIVE.
      * exists (double_tree_captured temps bound cache flag input lower upper),true.
        eapply double_tree_receipt_empty; eassumption.
    + exists (double_tree_captured temps bound cache flag input lower upper),false.
      eapply double_tree_receipt_refused; eassumption.
Qed.

Theorem double_tree_capture_source_execution p controls tree fe ge locals source_temps memory source_after source_final
  temps cache flag lower upper :
  double_source_tree_checked p controls tree -> preserving_globals (globalenv p) ge ->
  double_source_tree_scope tree locals ->
  double_source_tree_header_exclusions tree (double_source_tree_headers tree) ->
  locals_avoid (double_source_tree_headers tree) locals ->
  (forall header, In header (double_source_tree_headers tree) ->
    Int.min_signed<=lower header<=Int.max_signed /\ Int.min_signed<=upper header<=Int.max_signed) ->
  (forall header, In header (double_source_tree_headers tree) -> flag<>cache header) ->
  double_tree_flag_value temps flag true ->
  exec_stmt fe ge locals source_temps memory (double_source_tree_code tree) E0 source_after source_final Out_normal ->
  exists after accepted,
    exec_stmt fe ge locals temps memory (double_tree_capture_code tree cache flag lower upper) E0 after memory Out_normal /\
    double_tree_flag_value after flag accepted /\
    (forall key, ~ In key (double_tree_capture_private tree cache flag) -> after ! key=temps ! key).
Proof.
  intros CHECK GLOBAL SCOPE EXCLUSIONS LOCAL LIMITS FRESH FLAG RUN.
  destruct (@double_tree_capture_source_licensed tree p controls fe ge locals (double_source_tree_headers tree)
    source_temps memory source_after source_final temps memory cache flag lower upper true CHECK GLOBAL SCOPE EXCLUSIONS
    (incl_refl _) LOCAL LIMITS (double_tree_header_loads_refl ge _ memory) FLAG RUN) as [after [accepted RECEIPT]].
  exists after,accepted; split.
  - exact (@double_tree_capture_receipt_execution ge locals memory cache flag lower upper tree temps after accepted RECEIPT FRESH fe).
  - split; [exact (double_tree_capture_receipt_flag RECEIPT)|].
    exact (@double_tree_capture_receipt_frame ge locals memory cache flag lower upper tree temps after accepted RECEIPT FRESH).
Qed.

Print Assumptions double_tree_capture_source_licensed.
Print Assumptions double_tree_capture_source_execution.
