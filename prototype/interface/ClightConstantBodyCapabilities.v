From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightLoopSyntax ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryWindowCells
  GuardMemoryNaryCompute GuardMemoryFootprintCapabilities GuardMemoryRectangularFootprint
  GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestWords AffineNestValuation
  AffineNestMathDomain AffineNestSourceDecode AffineNestLeafModel AffineNestLeafDecode
  AffineNestLoopEncoding AffineNestLeafLoop AffineNestScanModel AffineNestScanPoints.
From GuardInterface Require Import ClightConstantBoundModel ClightAffineChildBodyDecode
  ClightAffineBodyCapabilities ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Decode only the reached constant-bound subbody. The enclosing prefix can
    contain both loaded-loop coordinates. No execution or stability premise
    for either cached enclosing loop is needed. *)
Theorem constant_affine_prefix_body_decode iterator helper upper body child coordinates prefix parameters bounds
  lower upper_window pointers operations
  (certificate : affine_leaf_certificate(affine_nest_leaf child) bounds lower upper_window
    (coordinates++parameters) [] pointers operations)
  fe ge locals initial valuation code temps memory after final tail written :
  let nest:=AffineSourceAxis iterator helper(MemorySourceConstant upper) body child in
  coordinates=prefix++affine_nest_iterators nest ->
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  affine_nest_bound_dependencies prefix parameters nest ->
  (forall identifier, In identifier((prefix++parameters)++pointers) -> ~In identifier(affine_nest_mutated nest)) ->
  affine_math_domain bounds(coordinates++parameters) nest valuation 0 ->
  affine_word_view(prefix++parameters) valuation temps -> temp_agree pointers initial temps ->
  writes_only written body -> ~In helper written -> temps!helper=Some(Vint(Int.repr upper)) ->
  affine_lower_nest nest prefix parameters(L.Constant 0)
    (affine_checked_leaf_code coordinates parameters [] operations)=Some code ->
  exec_stmt fe ge locals temps memory(constant_body_source iterator(Int.repr upper) body) E0 after final Out_normal ->
  L.loop_semantics code(map valuation(rev prefix++parameters)++tail)
    (RuntimeState(window_multi_pointer_locations initial lower upper_window) memory)
    (RuntimeState(window_multi_pointer_locations initial lower upper_window) final).
Proof.
  cbn zeta; intros COORDINATES SHAPES FRESH DEPENDENCIES PROTECTED DOMAIN WORDS POINTERS WRITES PRIVATE HELPER LOWER SOURCE.
  assert (DISTINCT : iterator<>helper).
  { cbn [affine_nest_controls] in FRESH; apply NoDup_cons_iff in FRESH as [FIRST REST].
    intro SAME; apply FIRST; cbn; auto. }
  destruct(sequence_normal_decode SOURCE) as [reset [reset_memory [RESET LOOP]]].
  destruct(rectangle_reset_decode RESET) as [_ [TEMPS [MEMORY _]]]; subst reset reset_memory.
  assert (BOUND : (PTree.set iterator(Vint Int.zero)temps)!helper=Some(Vint(Int.repr upper))).
  { rewrite PTree.gso by congruence; exact HELPER. }
  destruct(@constant_loop_preinitialized_model fe ge locals iterator helper(Int.repr upper) body written
    _ memory E0 after final Out_normal DISTINCT WRITES PRIVATE BOUND LOOP) as [MODEL EXIT].
  eapply affine_checked_prefix_source_decode with
    (nest:=AffineSourceAxis iterator helper(MemorySourceConstant upper) body child)
    (certificate:=certificate)(prefix:=prefix)(start:=0)
    (temps:=PTree.set iterator(Vint Int.zero)temps); try eassumption.
  - eapply affine_word_view_frame; [exact WORDS|apply temp_agree_set].
    intro MEMBER; apply(PROTECTED iterator(in_or_app _ _ _ (or_introl MEMBER))); cbn; auto.
  - eapply temp_agree_trans; [exact POINTERS|apply temp_agree_set].
    intro MEMBER; apply(PROTECTED iterator(in_or_app _ _ _ (or_intror MEMBER))); cbn; auto.
  - split; [apply PTree.gss|exact BOUND].
Qed.

(** Transport permission facts, not the reached source's memory values, to
    the actual guard entry. All leaf reads and writes in this subdomain are
    covered by the existing recursive affine footprint theorem. *)
Theorem constant_affine_prefix_body_capabilities iterator helper upper body child coordinates prefix parameters bounds
  lower upper_window pointers operations
  (certificate : affine_leaf_certificate(affine_nest_leaf child) bounds lower upper_window
    (coordinates++parameters) [] pointers operations)
  fe ge locals initial valuation code temps guard_memory memory after final written :
  let nest:=AffineSourceAxis iterator helper(MemorySourceConstant upper) body child in
  coordinates=prefix++affine_nest_iterators nest ->
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) ->
  affine_nest_bound_dependencies prefix parameters nest ->
  (forall identifier, In identifier((prefix++parameters)++pointers) -> ~In identifier(affine_nest_mutated nest)) ->
  affine_math_domain bounds(coordinates++parameters) nest valuation 0 ->
  affine_word_view(prefix++parameters) valuation temps -> temp_agree pointers initial temps ->
  writes_only written body -> ~In helper written -> temps!helper=Some(Vint(Int.repr upper)) ->
  affine_lower_nest nest prefix parameters(L.Constant 0)
    (affine_checked_leaf_code coordinates parameters [] operations)=Some code ->
  memory_accesses_back guard_memory memory ->
  exec_stmt fe ge locals temps memory(constant_body_source iterator(Int.repr upper) body) E0 after final Out_normal ->
  forall point, affine_scan_point nest valuation 0 point ->
    Forall(memory_cell_capable(window_multi_pointer_locations initial lower upper_window) guard_memory)
      (memory_point_footprint(map memory_nary_compute_instruction operations)(map point(coordinates++parameters))).
Proof.
  cbn zeta; intros COORDINATES SHAPES FRESH DEPENDENCIES PROTECTED DOMAIN WORDS POINTERS WRITES PRIVATE HELPER LOWER BACK SOURCE point POINT.
  pose proof(@constant_affine_prefix_body_decode iterator helper upper body child coordinates prefix parameters bounds
    lower upper_window pointers operations certificate fe ge locals initial valuation code temps memory after final [] written
    COORDINATES SHAPES FRESH DEPENDENCIES PROTECTED DOMAIN WORDS POINTERS WRITES PRIVATE HELPER LOWER SOURCE) as MODEL.
  unfold affine_checked_leaf_code in LOWER; rewrite app_nil_r in LOWER.
  pose proof(affine_leaf_unique certificate) as UNIQUE; rewrite app_nil_r in UNIQUE.
  eapply affine_prefix_capabilities_at_guard_entry with(prefix:=prefix)(lower:=0)(lower_code:=L.Constant 0)
    (code:=code)(tail:=[])(memory:=memory)(final:=final);
    try eassumption; try reflexivity.
  exact(window_multi_pointer_locations_int32 _ _ _).
Qed.

Print Assumptions constant_affine_prefix_body_decode.
Print Assumptions constant_affine_prefix_body_capabilities.
