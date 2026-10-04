From Stdlib Require Import List Bool ZArith Arith.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightStraightLine ClightStructuredProgress.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryPointerComputeSyntax GuardMemoryPointerSourceWords
  GuardMemoryMultiPointerIdentifiers GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode AffineNestBoundWords
  AffineNestGuardPackage AffineNestCheckedCompiler.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** An untrusted initial policy, checked by check_affine_region. It proposes
    finite boxes and declarations from actual syntax; acceptance never relies
    on the correctness of these heuristics. *)
Fixpoint affine_integer_expression_reads expression := match expression with
  | Etempvar identifier ty=>if type_eq ty type_int32s then [identifier] else []
  | Ederef first _ | Eaddrof first _ | Eunop _ first _ | Ecast first _ | Efield first _ _=>affine_integer_expression_reads first
  | Ebinop _ first second _=>affine_integer_expression_reads first++affine_integer_expression_reads second
  | _=>[] end.
Definition affine_integer_leaf_reads source := flat_map(fun statement=>match statement with
  | Sassign first second=>affine_integer_expression_reads first++affine_integer_expression_reads second
  | _=>[] end)(flatten_region source).
Definition affine_propose_parameters nest := match nest with
  | AffineSourceLeaf _=>[]
  | AffineSourceAxis _ bound _ _ _=>nodup peq(filter(fun identifier=>negb(existsb(Pos.eqb identifier)(affine_nest_mutated nest)))
      (bound::affine_tail_bound_reads nest++affine_integer_leaf_reads(affine_nest_leaf nest))) end.
Definition affine_default_axis_ranges depth := match depth with
  | O=>[]
  | S remaining=>(-4,8)::map(fun index=>(0,Z.of_nat(Nat.pow 2(index+4)%nat)))(seq 0 remaining) end.
Definition affine_default_parameter_ranges bound nest operations parameters :=
  map(fun identifier=>if Pos.eqb identifier bound then (1,9) else
    if existsb(Pos.eqb identifier)(affine_tail_bound_reads nest) then (-8,9) else
    if existsb(Pos.eqb identifier)(flat_map memory_pointer_operation_address_reads operations) then (-32,33) else
    (Int.min_signed,Int.max_signed+1)) parameters.

Definition affine_default_source_proposal : affine_source_proposer := fun live pool source=>
  let nest:=propose_affine_source_nest(progress_syntax_size source) source in
  match nest with
  | AffineSourceAxis iterator bound _ body child=>
    let coordinates:=affine_nest_iterators nest in
    let parameters:=affine_propose_parameters nest in
    match coordinates with
    | _::_::_=>match propose_memory_pointer_computes 1(coordinates++parameters)(flatten_region(affine_nest_leaf nest)) with
      | Some operations=>
        let ranges:=affine_default_parameter_ranges bound nest operations parameters in
        let axes:=affine_default_axis_ranges(length coordinates) in
        let private:=firstn(2*length coordinates)%nat(var_names pool) in
        match axes,nth_error(var_names pool)(2*length coordinates)%nat with
        | (floor,cap)::remaining,Some result=>
          Some(parameters,AffineGuardProposal iterator bound body child(axes++ranges)(-65536) 65536
            (memory_multi_pointer_operation_identifiers operations) operations ranges floor cap remaining private result)
        | _,_=>None end
      | None=>None end
    | _=>None end
  | _=>None end.
Print Assumptions affine_default_source_proposal.
