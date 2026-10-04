From Stdlib Require Import List Bool ZArith Arith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightStraightLine ClightStructuredProgress.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryNaryCompute GuardMemoryNaryAffineAccess GuardMemoryPointerComputeSyntax
  GuardMemoryPointerSourceWords GuardMemoryMultiPointerIdentifiers GuardMemoryAffineSourceExpressions GuardMemoryIntervalBox.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode AffineNestLoopEncoding
  AffineNestProfile AffineNestBoundWords AffineNestGuardPackage AffineNestCheckedCompiler AffineNestPropose.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Range policy is untrusted configuration, independently checked with the
    actual source. Child caps are inferred from the actual affine upper bounds;
    address windows are inferred from all actual load/store access functions. *)
Record affine_range_policy := AffineRangePolicy {
  affine_policy_root_floor : Z;
  affine_policy_root_cap : Z;
  affine_policy_bound_lower : Z;
  affine_policy_bound_upper : Z;
  affine_policy_address_lower : Z;
  affine_policy_address_upper : Z
}.
Definition affine_policy_parameter_ranges policy bound nest operations parameters :=
  map(fun identifier=>if Pos.eqb identifier bound then (1,affine_policy_root_cap policy+1) else
    if existsb(Pos.eqb identifier)(affine_tail_bound_reads nest) then
      (affine_policy_bound_lower policy,affine_policy_bound_upper policy) else
    if existsb(Pos.eqb identifier)(flat_map memory_pointer_operation_address_reads operations) then
      (affine_policy_address_lower policy,affine_policy_address_upper policy) else
    (Int.min_signed,Int.max_signed+1)) parameters.

Fixpoint affine_infer_axis_ranges nest prefix parameters prefix_ranges parameter_ranges floor :=
  match nest with
  | AffineSourceLeaf _=>Some []
  | AffineSourceAxis iterator _ expression _ child=>
    match affine_loop_expression(rev prefix++parameters) expression with
    | Some encoded=>match MemoryNested.A.analyze
        (map affine_profile_interval(rev prefix_ranges++parameter_ranges)) encoded with
      | Some interval=>let cap:=Z.max (floor+1)(MemoryNested.A.upper interval) in
        match affine_infer_axis_ranges child(prefix++[iterator]) parameters
          (prefix_ranges++[(floor,cap)]) parameter_ranges 0 with
        | Some remaining=>Some((floor,cap)::remaining)|None=>None end
      | None=>None end
    | None=>None end end.

Definition affine_access_proposed_range bounds access :=
  let term:=memory_nary_access_index access in
  (interval_dot_lower(fst term) bounds+snd term,
   interval_dot_upper(fst term) bounds+snd term+1).
Definition affine_infer_address_window bounds operations :=
  let accesses:=flat_map(fun operation=>memory_nary_compute_write operation::memory_nary_compute_reads operation) operations in
  match accesses with
  | []=>None
  | first::rest=>Some(fold_left(fun previous access=>
      let range:=affine_access_proposed_range bounds access in
      (Z.min(fst previous)(fst range),Z.max(snd previous)(snd range))) rest(affine_access_proposed_range bounds first)) end.

Definition affine_source_range_proposal policy : affine_source_proposer := fun live pool source=>
  let nest:=propose_affine_source_nest(progress_syntax_size source) source in
  match nest with
  | AffineSourceAxis iterator bound _ body child=>
    let coordinates:=affine_nest_iterators nest in
    let parameters:=affine_propose_parameters nest in
    match coordinates with
    | _::_::_=>match propose_memory_pointer_computes 1(coordinates++parameters)(flatten_region(affine_nest_leaf nest)) with
      | Some operations=>let ranges:=affine_policy_parameter_ranges policy bound nest operations parameters in
        match affine_infer_axis_ranges nest [] parameters [] ranges(affine_policy_root_floor policy) with
        | Some((floor,cap)::remaining)=>let axes:=(floor,cap)::remaining in
          match affine_infer_address_window(axes++ranges) operations,
            nth_error(var_names pool)(2*length coordinates)%nat with
          | Some(lower,upper),Some result=>Some(parameters,
              AffineGuardProposal iterator bound body child(axes++ranges) lower upper
                (memory_multi_pointer_operation_identifiers operations) operations ranges floor cap remaining
                (firstn(2*length coordinates)%nat(var_names pool)) result)
          | _,_=>None end
        | _=>None end
      | None=>None end
    | _=>None end
  | _=>None end.
Print Assumptions affine_infer_axis_ranges.
Print Assumptions affine_infer_address_window.
Print Assumptions affine_source_range_proposal.
