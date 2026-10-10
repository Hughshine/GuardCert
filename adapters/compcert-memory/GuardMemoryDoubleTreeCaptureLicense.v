From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightLoopSyntax ClightGlobalScope ClightRegionProgress ClightSkipPrefix.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleHeaderFrame
  GuardMemoryDoubleProgramBindings GuardMemoryDoubleSourceTreeData GuardMemoryDoubleSourceTreeSyntax
  GuardMemoryDoubleSourceTreeState GuardMemoryLongControl GuardMemoryLongRangeSource
  GuardMemoryLongRangeHeader GuardMemoryLongRangeCaptureSource GuardMemoryDoubleSignedRangeSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_tree_bound_word bound input := match tree_bound_offset bound with
  | None=>input | Some offset=>Int64.sub input (Int64.repr (Int.signed offset)) end.
Lemma double_tree_bound_load_decode ge locals temps memory bound block result :
  double_global_binding ge locals (tree_bound_header bound) block ->
  eval_expr ge locals temps memory (double_tree_bound_code bound) (Vlong result) ->
  exists input, Mem.load Mint64 memory block 0=Some (Vlong input) /\
    result=double_tree_bound_word bound input.
Proof.
  destruct bound as [header [offset|]]; cbn [double_tree_bound_code double_tree_bound_word]; intros BIND RUN.
  - eapply memory_long_offset_bound_decode; eassumption.
  - exists result; split; [eapply memory_global_long_decode; eassumption|reflexivity].
Qed.

(** This receipt uses only the first comparison of a defined source range. No
    accepted affine-cell or no-wrap premise is needed to license the raw load.
    The child receipt is conditional on the actual machine comparison. *)
Theorem double_tree_range_first_load p controls raw iterator start bound child fe ge locals temps memory after final block :
  double_source_tree_checked p (controls++[iterator]) child ->
  double_global_binding ge locals (tree_bound_header bound) block ->
  exec_stmt fe ge locals temps memory
    (double_source_tree_code (DoubleTreeRange raw iterator start bound child)) E0 after final Out_normal ->
  exists input, Mem.load Mint64 memory block 0=Some (Vlong input) /\
    (Int64.signed (Int64.repr (Int.signed start))<Int64.signed (double_tree_bound_word bound input) ->
      exists child_after child_final,
        exec_stmt fe ge locals (PTree.set iterator (Vlong (Int64.repr (Int.signed start))) temps) memory
          (double_source_tree_code child) E0 child_after child_final Out_normal).
Proof.
  intros CHECK BIND RUN.
  assert (CANONICAL : exec_stmt fe ge locals temps memory
    (memory_long_from_loop iterator (double_tree_initial start)
      (Ebinop Olt (Etempvar iterator memory_long_type) (double_tree_bound_code bound) memory_signed_int_type)
      (double_source_tree_code child)) E0 after final Out_normal).
  { cbn [double_source_tree_code] in RUN; destruct raw; [|exact RUN].
    apply (proj1 (@long_raw_from_execution iterator (double_tree_initial start) (double_tree_bound_code bound)
      (double_source_tree_code child) fe ge locals temps memory E0 after final Out_normal)); exact RUN. }
  assert (INITIAL : eval_expr ge locals temps memory (double_tree_initial start) (Vlong (Int64.repr (Int.signed start)))).
  { unfold double_tree_initial; eapply eval_Ecast; [constructor|reflexivity]. }
  destruct (@memory_long_from_bound_license fe ge locals temps memory iterator (double_tree_initial start)
    (double_tree_bound_code bound) (double_source_tree_code child) (Int.signed start) after final
    (double_tree_bound_type bound) INITIAL (@double_source_tree_normal p (controls++[iterator]) child CHECK)
    CANONICAL) as [result [BOUND CHILD]].
  destruct (@double_tree_bound_load_decode ge locals _ memory bound block result BIND BOUND)
    as [input [LOAD RESULT]].
  exists input; split; [exact LOAD|rewrite <- RESULT; exact CHILD].
Qed.

(** Source and guard states may have different public temporaries and memory
    contents. Only observer loads are transported; no load is assumed defined. *)
Definition double_tree_header_loads_equal (ge : genv) headers source_memory guard_memory :=
  forall header block, In header headers -> Genv.find_symbol ge header=Some block ->
    Mem.load Mint64 source_memory block 0=Mem.load Mint64 guard_memory block 0.
Lemma double_tree_header_loads_refl ge headers memory : double_tree_header_loads_equal ge headers memory memory.
Proof. intros header block MEMBER SYMBOL; reflexivity. Qed.
Theorem double_tree_header_loads_after_source p controls tree fe ge locals headers temps source_memory
  guard_memory after final :
  double_source_tree_checked p controls tree -> preserving_globals (globalenv p) ge ->
  double_source_tree_scope tree locals -> double_source_tree_header_exclusions tree headers ->
  double_tree_header_loads_equal ge headers source_memory guard_memory ->
  exec_stmt fe ge locals temps source_memory (double_source_tree_code tree) E0 after final Out_normal ->
  double_tree_header_loads_equal ge headers final guard_memory.
Proof.
  intros CHECK GLOBAL SCOPE EXCLUSIONS EQUAL RUN header block MEMBER SYMBOL.
  destruct (@double_source_subtree_raw_header_frame p controls tree fe ge locals temps source_memory E0 after final
    Out_normal header block CHECK GLOBAL (double_source_tree_scope_writes SCOPE)
    ltac:(intros instruction POINT; apply EXCLUSIONS; assumption) SYMBOL RUN) as [FRAME PERMISSIONS].
  rewrite FRAME; exact (EQUAL header block MEMBER SYMBOL).
Qed.

Print Assumptions double_tree_bound_load_decode.
Print Assumptions double_tree_range_first_load.
Print Assumptions double_tree_header_loads_refl.
Print Assumptions double_tree_header_loads_after_source.
