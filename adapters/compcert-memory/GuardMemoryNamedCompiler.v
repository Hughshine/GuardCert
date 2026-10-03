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
  GuardMemoryNamedOperations GuardMemoryNamedRegistrySource GuardMemoryNamedGuard GuardMemoryNamedCandidate GuardMemoryNamedChecker.
Import CoreAlarmed ListNotations PrivateRegion.
Import Clight.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition propose_named_array_operation row bound column inner_bound store : option named_array_operation :=
  match describe_memory_rectangle (frontend_counted_loop row bound
    (rectangle_outer_body column inner_bound store)) with
  | Some package => Some (NamedArrayOperation (package_mode package)
      (described_shape (package_description package)) (described_array (package_description package)))
  | None => match store with
    | Sassign lhs (Ebinop Oadd (Ederef (Ebinop Oadd (Evar read_array _) _ _) _) payload _) =>
      match describe_memory_rectangle (frontend_counted_loop row bound
        (rectangle_outer_body column inner_bound (Sassign lhs payload))) with
      | Some package => Some (NamedCrossArrayOperation
          (described_shape (package_description package)) (described_array (package_description package)) read_array)
      | None => None end
    | _ => None end
  end.
Fixpoint propose_named_array_operations row bound column inner_bound stores : option (list named_array_operation) :=
  match stores with
  | [] => Some []
  | store::rest =>
    match propose_named_array_operation row bound column inner_bound store,
      propose_named_array_operations row bound column inner_bound rest with
    | Some operation,Some operations => Some (operation::operations)
    | _,_ => None end
  end.
Definition propose_named_array_operations_region source : option (rectangle_description * list named_array_operation) :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset column _;inner_loop] => match propose_frontend_shape inner_loop with
      | Some (_,inner_bound,inner_body) =>
        match propose_named_array_operations row bound column inner_bound (flatten_region inner_body) with
        | Some (operation::operations) => Some
            (RectangleDescription (named_operation_shape operation) (named_operation_array operation)
              row bound column inner_bound inner_body outer_body,operation::operations)
        | _ => None end
      | None => None end
    | _ => None end
  | None => None end.
Record named_array_operations_certificate source d shapes := NamedArrayOperationsCertificate {
  named_family_source : source = rectangle_described_source d;
  named_family_body : flatten_region (rectangle_inner_body d) =
    map (named_operation_statement (rectangle_row d) (rectangle_column d)) shapes;
  named_family_outer : flatten_region (rectangle_described_outer_body d) =
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  named_family_rn : rectangle_row d <> rectangle_bound d;
  named_family_rc : rectangle_row d <> rectangle_column d;
  named_family_nc : rectangle_bound d <> rectangle_column d;
  named_family_rm : rectangle_row d <> rectangle_inner_bound d;
  named_family_cm : rectangle_column d <> rectangle_inner_bound d;
  named_family_layout : rectangle_layout_valid (described_shape d);
  named_family_layouts : Forall (named_operation_layout (described_shape d)) shapes;
  named_family_nonempty : shapes <> []
}.
Definition check_named_array_operations source d shapes : option (named_array_operations_certificate source d shapes).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    (map (named_operation_statement (rectangle_row d) (rectangle_column d)) shapes))
    as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_described_outer_body d))
    [rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)])
    as [OUTER|]; [|exact None].
  destruct (peq (rectangle_row d) (rectangle_bound d)) as [|RN]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_column d)) as [|RC]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_column d)) as [|NC]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_inner_bound d)) as [|RM]; [exact None|].
  destruct (peq (rectangle_column d) (rectangle_inner_bound d)) as [|CM]; [exact None|].
  destruct (rectangle_layout_check (described_shape d)) eqn:LAYOUT; [|exact None].
  destruct (forallb (fun operation => same_array_layout_check (described_shape d) (named_operation_shape operation)) shapes) eqn:LAYOUTS; [|exact None].
  assert (ALL : Forall (named_operation_layout (described_shape d)) shapes).
  { apply Forall_forall; intros shape MEMBER; unfold named_operation_layout; apply same_array_layout_check_sound.
    exact (proj1 (forallb_forall _ _) LAYOUTS shape MEMBER). }
  destruct shapes as [|shape shapes]; [exact None|].
  exact (Some (@NamedArrayOperationsCertificate source d (shape::shapes) SOURCE BODY OUTER RN RC NC RM CM
    (@rectangle_layout_check_sound (described_shape d) LAYOUT) ALL ltac:(discriminate))).
Defined.
Record memory_named_package source := MemoryNamedPackage {
  named_description : rectangle_description;
  named_operations : list named_array_operation;
  named_syntax : named_array_operations_certificate source named_description named_operations
}.
Definition describe_memory_named source : option (memory_named_package source) :=
  match propose_named_array_operations_region source with
  | Some (d,shapes) => match check_named_array_operations source d shapes with
    | Some CERT => Some (@MemoryNamedPackage source d shapes CERT) | None => None end
  | None => None end.
Definition memory_named_target source (package : memory_named_package source) code :=
  let d := named_description package in
  shared_guarded_statement
    (decision_bind (memory_named_guard_tree (described_shape d)
      (named_array_descriptors (described_shape d) (named_operations package))
      (rectangle_row d) (rectangle_bound d) (rectangle_inner_bound d)) (Decision true) (Decision false))
    (rectangle_tiled_candidate code (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d)) source.
Theorem memory_named_target_sound source (package : memory_named_package source) live pairs candidate code :
  compile_named_array_candidate (described_shape (named_description package)) (named_operations package)
    (rectangle_bound (named_description package)) (rectangle_inner_bound (named_description package))
    live pairs candidate = Some code ->
  memory_named_candidate_certificate (described_shape (named_description package)) (named_operations package) candidate ->
  projected_region_contract live source (memory_named_target package code).
Proof.
  destruct package as [d operations CERT]; cbn; intros COMPILE CHECK.
  destruct CERT as [SOURCE BODY OUTER RN RC NC RM CM VALID LAYOUTS NONEMPTY]; subst source.
  unfold memory_named_target,rectangle_described_source; cbn.
  change (projected_region_contract live
    (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (generated_private_region (@memory_named_array_candidate_rule (described_shape d) VALID operations LAYOUTS
      (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d)
      (rectangle_inner_body d) (rectangle_described_outer_body d) RN RC NC RM CM BODY OUTER
      live pairs candidate code COMPILE CHECK))).
  apply encoded_private_rule_sound.
Qed.
Definition check_memory_named_affine_region live pool (propose : (list memory_instruction -> option (L.stmt * list nat))) source : CoreAlarmed.Base.imp (option statement) :=
  match private_counter_pairs pool,describe_memory_named source with
  | Some pairs,Some package =>
    let d := named_description package in
    match propose (map named_operation_instruction (named_operations package)) with
    | Some (candidate,swaps) => match compile_named_array_candidate (described_shape d) (named_operations package)
        (rectangle_bound d) (rectangle_inner_bound d) live pairs candidate with
      | Some code => BIND valid <- checked_named_affine_candidate (described_shape d) (named_operations package) (rectangle_bound d) (rectangle_inner_bound d) candidate swaps -;
        pure (if valid then Some (memory_named_target package code) else None)
      | None => pure None end
    | None => pure None end
  | _,_ => pure None end.
Theorem check_memory_named_affine_region_sound live pool propose source target :
  mayReturn (check_memory_named_affine_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_named_affine_region.
  destruct (private_counter_pairs pool) as [pairs|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (describe_memory_named source) as [package|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (propose (map named_operation_instruction (named_operations package))) as [[candidate swaps]|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (compile_named_array_candidate (described_shape (named_description package)) (named_operations package)
    (rectangle_bound (named_description package))
    (rectangle_inner_bound (named_description package)) live pairs candidate) as [code|] eqn:COMPILE;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  intro CHECK; bind_imp_destruct CHECK valid VALID; apply mayReturn_pure in CHECK.
  destruct valid; [inversion CHECK; subst target|discriminate].
  apply memory_named_target_sound with (pairs := pairs) (candidate := candidate); [exact COMPILE|].
  eapply checked_named_affine_candidate_correct; exact VALID.
Qed.

Print Assumptions check_memory_named_affine_region_sound.

Definition check_memory_named_tiled_region live pool rows columns source : CoreAlarmed.Base.imp (option statement) :=
  match Z_lt_dec 0 rows,Z_lt_dec 0 columns,private_counter_pairs pool,describe_memory_named source with
  | left _,left _,Some pairs,Some package =>
    let d := named_description package in
    let candidate := memory_tiled_sequence (map named_operation_instruction (named_operations package)) rows columns in
    match compile_named_array_candidate (described_shape d) (named_operations package)
      (rectangle_bound d) (rectangle_inner_bound d) live pairs candidate with
    | Some code => BIND valid <- checked_named_tiled_candidate (described_shape d) (named_operations package) rows columns -;
        pure (if valid then Some (memory_named_target package code) else None)
    | None => pure None end
  | _,_,_,_ => pure None end.
Theorem check_memory_named_tiled_region_sound live pool rows columns source target :
  mayReturn (check_memory_named_tiled_region live pool rows columns source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_named_tiled_region.
  destruct (Z_lt_dec 0 rows); [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (Z_lt_dec 0 columns); [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (private_counter_pairs pool) as [pairs|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (describe_memory_named source) as [package|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (compile_named_array_candidate (described_shape (named_description package)) (named_operations package)
    (rectangle_bound (named_description package)) (rectangle_inner_bound (named_description package)) live pairs
    (memory_tiled_sequence (map named_operation_instruction (named_operations package)) rows columns))
    as [code|] eqn:COMPILE; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  intro CHECK; bind_imp_destruct CHECK valid VALID; apply mayReturn_pure in CHECK.
  destruct valid; [inversion CHECK; subst target|discriminate].
  apply memory_named_target_sound with (pairs := pairs)
    (candidate := memory_tiled_sequence (map named_operation_instruction (named_operations package)) rows columns);
    [exact COMPILE|].
  apply checked_named_tiled_candidate_correct; assumption.
Qed.
Print Assumptions check_memory_named_tiled_region_sound.
