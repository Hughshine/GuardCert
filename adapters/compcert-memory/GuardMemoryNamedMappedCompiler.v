From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight Csyntax Csem Cstrategy SimplExpr SimplExprproof
  SimplLocals SimplLocalsproof.
From compcert.driver Require Import Compiler.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightGuard ClightCondition ClightPureExpr ClightPrivateRule ClightPrivateRegion
  ClightPrivateRegionProof ClightPrivatePool ClightTempFootprint ClightTempScope
  ClightStructuredProgress ClightRectangularSelector ClightRectangularStore
  ClightRectangularGuard ClightRectangularRegion ClightRectangularLoops GuardCompiler
  ClightFrontendLoopProtocol ClightFrontendRegion ClightStraightLine ClightSharedRegion ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryClightRectangles GuardMemoryCompiler GuardMemoryTiledClight GuardMemoryTiledCompiler
  GuardMemoryArrayFamilyBackend GuardMemoryOperationsClight GuardMemoryOperationsTiledClight GuardMemoryRegistryBackend GuardMemoryRegistryGuard
  GuardMemoryInstr GuardMemoryLoops GuardMemorySequenceLoops
  GuardMemoryNamedOperations GuardMemoryNamedRegistrySource GuardMemoryNamedGuard GuardMemoryNamedCandidate GuardMemoryNamedChecker GuardMemoryAffineReindex GuardMemoryNamedMappedChecker GuardMemoryNamedCompiler.
Import CoreAlarmed ListNotations PrivateRegion.
Import Clight.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition check_memory_named_mapped_region live pool (propose : (list memory_instruction -> option (L.stmt * list memory_affine_reindex))) source : CoreAlarmed.Base.imp (option statement) :=
  match private_counter_pairs pool,describe_memory_named source with
  | Some pairs,Some package =>
    let d := named_description package in
    match propose (map named_operation_instruction (named_operations package)) with
    | Some (candidate,steps) => match compile_named_array_candidate (described_shape d) (named_operations package)
        (rectangle_bound d) (rectangle_inner_bound d) live pairs candidate with
      | Some code => BIND valid <- checked_named_mapped_candidate (described_shape d) (named_operations package) (rectangle_bound d) (rectangle_inner_bound d) candidate steps -;
        pure (if valid then Some (memory_named_target package code) else None)
      | None => pure None end
    | None => pure None end
  | _,_ => pure None end.
Theorem check_memory_named_mapped_region_sound live pool propose source target :
  mayReturn (check_memory_named_mapped_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_named_mapped_region.
  destruct (private_counter_pairs pool) as [pairs|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (describe_memory_named source) as [package|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (propose (map named_operation_instruction (named_operations package))) as [[candidate steps]|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (compile_named_array_candidate (described_shape (named_description package)) (named_operations package)
    (rectangle_bound (named_description package))
    (rectangle_inner_bound (named_description package)) live pairs candidate) as [code|] eqn:COMPILE;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  intro CHECK; bind_imp_destruct CHECK valid VALID; apply mayReturn_pure in CHECK.
  destruct valid; [inversion CHECK; subst target|discriminate].
  apply memory_named_target_sound with (pairs := pairs) (candidate := candidate); [exact COMPILE|].
  eapply checked_named_mapped_candidate_correct; exact VALID.
Qed.

Print Assumptions check_memory_named_mapped_region_sound.
