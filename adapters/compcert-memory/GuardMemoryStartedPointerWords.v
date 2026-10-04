From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCountedLoop ClightTempFrame ClightFiniteRegion ClightStraightLine ClightNoWrap.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryNaryRanges GuardMemoryNaryLoops
  GuardMemoryNaryLift GuardMemoryRecursiveSource GuardMemoryRecursiveSyntax GuardMemoryRecursiveBody GuardMemoryRecursiveFramedExecution GuardMemoryRecursiveFirstLeaf
  GuardMemoryPointerSequence GuardMemoryPointerSyntax GuardMemoryPointerCompute GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryBufferOffsets.
From GuardMemory Require Import GuardMemoryMultiPointerSyntax GuardMemoryMultiPointerSequence GuardMemoryMultiPointerCompute GuardMemoryMultiPointerIdentifiers GuardMemoryMultiPointerCells GuardMemoryScalarPointerBody GuardMemoryRecursiveDomain GuardMemoryScalarLoops GuardMemoryScalarLift GuardMemorySourceParameters.
From GuardMemory Require Import GuardMemoryInstructionPadding.
From GuardMemory Require Import GuardMemoryParamPointerSyntax GuardMemoryPointerSourceWords.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

From GuardMemory Require Import GuardMemoryStartedFirstLeaf.
Theorem memory_started_pointer_source_first_capability source (package : memory_param_pointer_region_package source)
  iterator bound body child fe ge locals temps memory after final :
  param_pointer_region_nest package = MemorySourceAxis iterator bound body child ->
  Forall (fun bound => 0 < Int.signed (temp_word bound temps)) (memory_nest_bounds child) ->
  Int.signed (temp_word iterator temps) < Int.signed (temp_word bound temps) ->
  exec_stmt fe ge locals temps memory source E0 after final Out_normal ->
  forall identifier, In identifier (param_pointer_region_parameters package++param_pointer_region_scalars package) -> exists word, temps ! identifier = Some (Vint word).
Proof.
  intros NEST POSITIVE ACTIVE SOURCE.
  destruct package as [nest caps parameters parameter_caps pointers extent scalars operations CERT]; cbn in *.
  destruct CERT as [EQUAL NONEMPTY SHAPES FRESH CAPS_LENGTH CAPS PARAM_LENGTH PARAM_CAPS PARAM_STABLE PARAM_USED WINDOW PROTECTED UNIQUE STABLE USED OPS VALID COVERED BODY]; subst source; subst nest.
  assert (DISJOINT : forall identifier, In identifier (memory_nest_iterators (MemorySourceAxis iterator bound body child)) -> ~ In identifier (pointers++parameters++scalars)).
  { intros identifier MEMBER BAD; repeat rewrite in_app_iff in BAD.
    destruct BAD as [BAD|[BAD|BAD]];
      [exact (PROTECTED identifier BAD MEMBER)|exact (PARAM_STABLE identifier BAD MEMBER)|exact (STABLE identifier BAD MEMBER)]. }
  destruct (@memory_started_first_leaf fe ge locals iterator bound body child SHAPES FRESH
    (@memory_pointer_sequence_normal operations (memory_nest_leaf (MemorySourceAxis iterator bound body child)) BODY)
    (@memory_pointer_sequence_quiet operations (memory_nest_leaf (MemorySourceAxis iterator bound body child)) BODY)
    (@memory_pointer_sequence_writes operations (memory_nest_leaf (MemorySourceAxis iterator bound body child)) BODY) (pointers++parameters++scalars) temps memory after final
    DISJOINT POSITIVE ACTIVE SOURCE) as [leaf_temps [leaf_after [leaf_final [FRAME LEAF]]]].
  cbn [memory_nest_leaf] in BODY; apply flatten_region_execution in LEAF; rewrite BODY in LEAF.
  assert (TYPED : forall identifier, In identifier scalars -> exists word, temps ! identifier = Some (Vint word)).
  { intros identifier MEMBER; destruct (USED identifier MEMBER) as [operation [index [IN [LOOKUP USE]]]].
    destruct (@memory_multi_pointer_sequence_used_register (caps++parameter_caps) operations (memory_nest_iterators (MemorySourceAxis iterator bound body child)++parameters)
      scalars extent fe ge locals identifier index VALID LOOKUP leaf_temps memory leaf_after leaf_final LEAF operation IN USE)
      as [word WORD].
    exists word; rewrite (FRAME identifier ltac:(apply in_or_app; right; apply in_or_app; right; assumption)) in WORD; exact WORD. }
  assert (PARAM_TYPED : forall identifier, In identifier parameters -> exists word, temps ! identifier = Some (Vint word)).
  { intros identifier MEMBER; destruct (PARAM_USED identifier MEMBER) as [operation [IN USE]].
    destruct (@memory_pointer_sequence_address_words (caps++parameter_caps) operations
      (memory_nest_iterators (MemorySourceAxis iterator bound body child)++parameters) scalars extent fe ge locals identifier VALID
      leaf_temps memory leaf_after leaf_final LEAF operation IN USE) as [word WORD].
    exists word; rewrite (FRAME identifier ltac:(apply in_or_app; right; apply in_or_app; left; assumption)) in WORD; exact WORD. }
  intros identifier MEMBER; apply in_app_iff in MEMBER as [PARAM|SCALAR];
    [apply PARAM_TYPED; exact PARAM|apply TYPED; exact SCALAR].
Qed.
Print Assumptions memory_started_pointer_source_first_capability.
