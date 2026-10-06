From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightCountedLoop
  ClightFrontendLoopProtocol ClightPureExpr ClightLoopSyntax ClightRegionProgress ClightStraightLine
  ClightRectangularLoops CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryNaryCompute
  GuardMemoryNaryRanges GuardMemoryRecursiveSource GuardMemoryPointerCompute GuardMemoryPointerSequence
  GuardMemoryMultiPointerCompute GuardMemoryMultiPointerSequence GuardMemoryMultiPointerIdentifiers
  GuardMemoryMultiPointerCells GuardMemoryPointerSourceWords GuardMemorySourceParameters GuardMemoryParametricSourceClight
  GuardMemoryParametricFirstBody GuardMemoryAffinePointerBody GuardMemoryObservationStability.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictLoopProgress ClightStrictIteration
  ClightAffineLoadedBoundTransport.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The reached actual header provides the first row; its future reads need
    not be stable. Address and scalar words come from the true leaf body. *)
Theorem memory_affine_header_first_words fe ge locals temps memory row header column inner_bound expression
  upper body outer_body after final geometry scalars limits layout extent operations :
  column <> inner_bound -> pure_scalar expression ->
  expression_test header (Entry ge locals temps memory) true ->
  eval_expr ge locals temps memory expression (Vint (Int.repr upper)) ->
  0 < upper -> signed_range upper ->
  (forall identifier, In identifier (geometry++scalars) -> identifier <> column /\ identifier <> inner_bound) ->
  flatten_region outer_body = [memory_parametric_setup inner_bound expression;
    rectangle_reset column;frontend_counted_loop column inner_bound body] ->
  flatten_region body = map memory_pointer_compute_statement operations ->
  Forall (memory_multi_pointer_compute_valid limits layout scalars extent) operations ->
  (forall identifier, In identifier geometry -> exists operation,
    In operation operations /\ In identifier (memory_pointer_operation_address_reads operation)) ->
  (forall identifier, In identifier scalars -> exists operation index,
    In operation operations /\ nth_error (layout++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation))) ->
  exec_stmt fe ge locals temps memory (strict_frontend_loop row header outer_body) E0 after final Out_normal ->
  forall identifier, In identifier (geometry++scalars) -> exists word, temps ! identifier = Some (Vint word).
Proof.
  intros CK PURE ACTIVE VALUE POSITIVE SAFE PROTECTED OUTER BODY VALID ADDRESS_USED SCALAR_USED SOURCE.
  assert (OUTER_NORMAL : normal_statement outer_body = true)
    by (exact (@memory_parametric_outer_normal column inner_bound expression body outer_body
      (@memory_pointer_sequence_quiet operations body BODY) OUTER)).
  assert (OUTER_QUIET : quiet_statement outer_body = true).
  { apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|].
    constructor; [reflexivity|constructor; [|constructor]].
    cbn [quiet_statement frontend_counted_loop counter_increment]; rewrite (@memory_pointer_sequence_quiet operations body BODY); reflexivity. }
  destruct (@strict_active_iteration fe ge locals row header outer_body temps memory after final
    OUTER_NORMAL OUTER_QUIET ACTIVE SOURCE) as [next [last [incremented [rest [ROW _]]]]].
  destruct (@memory_parametric_first_inner_body fe ge locals temps memory column inner_bound expression upper body outer_body
    next last (geometry++scalars) CK (@memory_pointer_sequence_normal operations body BODY)
    (@memory_pointer_sequence_writes operations body BODY) PURE VALUE POSITIVE SAFE PROTECTED OUTER ROW)
    as [leaf [body_after [body_final [FRAME RUN]]]].
  apply flatten_region_execution in RUN; rewrite BODY in RUN.
  intros identifier MEMBER; apply in_app_iff in MEMBER as [ADDRESS|SCALAR].
  - destruct (ADDRESS_USED identifier ADDRESS) as [operation [MEMBER USED]].
    destruct (@memory_pointer_sequence_address_words limits operations layout scalars extent fe ge locals identifier
      VALID leaf memory body_after body_final RUN operation MEMBER USED) as [word WORD].
    exists word; rewrite FRAME in WORD by (apply in_or_app; left; exact ADDRESS); exact WORD.
  - destruct (SCALAR_USED identifier SCALAR) as [operation [index [MEMBER [LOOKUP USED]]]].
    destruct (@memory_multi_pointer_sequence_used_register limits operations layout scalars extent fe ge locals
      identifier index VALID LOOKUP leaf memory body_after body_final RUN operation MEMBER USED) as [word WORD].
    exists word; rewrite FRAME in WORD by (apply in_or_app; right; exact SCALAR); exact WORD.
Qed.

Print Assumptions memory_affine_header_first_words.
