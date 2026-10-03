From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From Guard Require Import ClightCondition ClightPureExpr ClightPrivateRule ClightPrivateRegion ClightPrivateRegionProof
  ClightPrivatePool ClightTempFootprint ClightRectangularSelector ClightRectangularStore
  ClightRectangularGuard ClightRectangularRegion ClightRectangularLoops ClightFrontendLoopProtocol
  ClightFrontendRegion ClightStraightLine ClightSharedRegion ClightSyntaxEquality.
From GuardMemory Require Import GuardMemoryInstr GuardMemoryLoops GuardMemoryNamedOperations GuardMemoryNamedRegistrySource
  GuardMemoryArrayFamilyBackend GuardMemoryTiledCompiler GuardMemoryNamedCompiler GuardMemoryNamedCandidate GuardMemoryAffineReindex GuardMemoryRaggedClight
  GuardMemoryRaggedGuard GuardMemoryNamedRaggedSource GuardMemoryNamedRaggedCandidate GuardMemoryNamedRaggedChecker.
Import CoreAlarmed ListNotations PrivateRegion.
Import Clight.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition propose_named_ragged_region source : option (rectangle_description * ident * list named_array_operation) :=
  match propose_frontend_shape source with
  | Some (row,bound,outer_body) => match flatten_region outer_body with
    | [Sset inner_bound (Ebinop Oadd _ (Etempvar parameter _) _);Sset column _;inner_loop] =>
      match propose_frontend_shape inner_loop with
      | Some (_,_,inner_body) =>
        match propose_named_array_operations row bound column inner_bound (flatten_region inner_body) with
        | Some (operation::operations) => Some
            (RectangleDescription (named_operation_shape operation) (named_operation_array operation)
              row bound column inner_bound inner_body outer_body,parameter,operation::operations)
        | _ => None end
      | None => None end
    | _ => None end
  | None => None end.
Record named_ragged_certificate source d parameter operations := NamedRaggedCertificate {
  ragged_source : source = rectangle_described_source d;
  ragged_body : flatten_region (rectangle_inner_body d) =
    map (named_operation_statement (rectangle_row d) (rectangle_column d)) operations;
  ragged_outer : flatten_region (rectangle_described_outer_body d) =
    [memory_ragged_setup (rectangle_row d) parameter (rectangle_inner_bound d);
      rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)];
  ragged_rn : rectangle_row d <> rectangle_bound d;
  ragged_rc : rectangle_row d <> rectangle_column d;
  ragged_nc : rectangle_bound d <> rectangle_column d;
  ragged_rk : rectangle_row d <> rectangle_inner_bound d;
  ragged_nk : rectangle_bound d <> rectangle_inner_bound d;
  ragged_ck : rectangle_column d <> rectangle_inner_bound d;
  ragged_mc : parameter <> rectangle_column d;
  ragged_mk : parameter <> rectangle_inner_bound d;
  ragged_mr : parameter <> rectangle_row d;
  ragged_layout : rectangle_layout_valid (described_shape d);
  ragged_layouts : Forall (named_operation_layout (described_shape d)) operations;
  ragged_nonempty : operations <> []
}.
Definition check_named_ragged source d parameter operations : option (named_ragged_certificate source d parameter operations).
Proof.
  destruct (statement_eq source (rectangle_described_source d)) as [SOURCE|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_inner_body d))
    (map (named_operation_statement (rectangle_row d) (rectangle_column d)) operations)) as [BODY|]; [|exact None].
  destruct (list_eq_dec statement_eq (flatten_region (rectangle_described_outer_body d))
    [memory_ragged_setup (rectangle_row d) parameter (rectangle_inner_bound d); rectangle_reset (rectangle_column d);
      frontend_counted_loop (rectangle_column d) (rectangle_inner_bound d) (rectangle_inner_body d)]) as [OUTER|]; [|exact None].
  destruct (peq (rectangle_row d) (rectangle_bound d)) as [|RN]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_column d)) as [|RC]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_column d)) as [|NC]; [exact None|].
  destruct (peq (rectangle_row d) (rectangle_inner_bound d)) as [|RK]; [exact None|].
  destruct (peq (rectangle_bound d) (rectangle_inner_bound d)) as [|NK]; [exact None|].
  destruct (peq (rectangle_column d) (rectangle_inner_bound d)) as [|CK]; [exact None|].
  destruct (peq parameter (rectangle_column d)) as [|MC]; [exact None|].
  destruct (peq parameter (rectangle_inner_bound d)) as [|MK]; [exact None|].
  destruct (peq parameter (rectangle_row d)) as [|MR]; [exact None|].
  destruct (rectangle_layout_check (described_shape d)) eqn:LAYOUT; [|exact None].
  destruct (forallb (fun operation => same_array_layout_check (described_shape d) (named_operation_shape operation)) operations) eqn:LAYOUTS; [|exact None].
  assert (ALL : Forall (named_operation_layout (described_shape d)) operations).
  { apply Forall_forall; intros operation MEMBER; unfold named_operation_layout; apply same_array_layout_check_sound.
    exact (proj1 (forallb_forall _ _) LAYOUTS operation MEMBER). }
  destruct operations as [|operation operations]; [exact None|].
  exact (Some (@NamedRaggedCertificate source d parameter (operation::operations) SOURCE BODY OUTER RN RC NC RK NK CK MC MK MR
    (@rectangle_layout_check_sound (described_shape d) LAYOUT) ALL ltac:(discriminate))).
Defined.
Record memory_ragged_package source := MemoryRaggedPackage {
  ragged_description : rectangle_description;
  ragged_parameter : ident;
  ragged_operations : list named_array_operation;
  ragged_syntax : named_ragged_certificate source ragged_description ragged_parameter ragged_operations
}.
Definition describe_memory_ragged source : option (memory_ragged_package source) :=
  match propose_named_ragged_region source with
  | Some (d,parameter,operations) => match check_named_ragged source d parameter operations with
    | Some CERT => Some (@MemoryRaggedPackage source d parameter operations CERT) | None => None end
  | None => None end.
Definition memory_ragged_target source (package : memory_ragged_package source) width_tree code :=
  let d := ragged_description package in
  shared_guarded_statement
    (decision_bind (memory_ragged_guard_tree (described_shape d)
      (named_array_descriptors (described_shape d) (ragged_operations package))
      (rectangle_row d) (rectangle_bound d) (ragged_parameter package) width_tree) (Decision true) (Decision false))
    (memory_ragged_candidate code (rectangle_row d) (rectangle_bound d)
      (rectangle_column d) (rectangle_inner_bound d) (ragged_parameter package)) source.
Theorem memory_ragged_target_sound source (package : memory_ragged_package source) live pairs candidate width_tree code :
  compile_named_array_candidate (described_shape (ragged_description package)) (ragged_operations package)
    (rectangle_bound (ragged_description package)) (ragged_parameter package) live pairs candidate = Some code ->
  compile_memory_ragged_width (described_shape (ragged_description package))
    (rectangle_bound (ragged_description package)) (ragged_parameter package) = Some width_tree ->
  memory_ragged_candidate_certificate (described_shape (ragged_description package)) (ragged_operations package) candidate ->
  projected_region_contract live source (memory_ragged_target package width_tree code).
Proof.
  destruct package as [d parameter operations CERT]; cbn; intros COMPILE LOWER CHECK.
  destruct CERT as [SOURCE BODY OUTER RN RC NC RK NK CK MC MK MR VALID LAYOUTS NONEMPTY]; subst source.
  unfold memory_ragged_target,rectangle_described_source; cbn.
  change (projected_region_contract live
    (frontend_counted_loop (rectangle_row d) (rectangle_bound d) (rectangle_described_outer_body d))
    (generated_private_region (@memory_ragged_array_candidate_rule (described_shape d) VALID operations LAYOUTS
      (rectangle_row d) (rectangle_bound d) (rectangle_column d) (rectangle_inner_bound d) parameter
      (rectangle_inner_body d) (rectangle_described_outer_body d) RN RC NC RK NK CK MC MK MR BODY OUTER
      live pairs candidate code COMPILE CHECK width_tree LOWER))).
  apply encoded_private_rule_sound.
Qed.
Definition check_memory_ragged_mapped_region live pool
  (propose : list memory_instruction -> option (L.stmt * list memory_affine_reindex)) source : CoreAlarmed.Base.imp (option statement) :=
  match private_counter_pairs pool,describe_memory_ragged source with
  | Some pairs,Some package =>
    let d := ragged_description package in
    match propose (map named_operation_instruction (ragged_operations package)),
      compile_memory_ragged_width (described_shape d) (rectangle_bound d) (ragged_parameter package) with
    | Some (candidate,steps),Some width_tree =>
      match compile_named_array_candidate (described_shape d) (ragged_operations package)
          (rectangle_bound d) (ragged_parameter package) live pairs candidate with
      | Some code => BIND valid <- checked_named_ragged_candidate (described_shape d) (ragged_operations package)
          (rectangle_bound d) (ragged_parameter package) candidate steps -;
        pure (if valid then Some (memory_ragged_target package width_tree code) else None)
      | None => pure None end
    | _,_ => pure None end
  | _,_ => pure None end.
Theorem check_memory_ragged_mapped_region_sound live pool propose source target :
  mayReturn (check_memory_ragged_mapped_region live pool propose source) (Some target) ->
  projected_region_contract live source target.
Proof.
  unfold check_memory_ragged_mapped_region.
  destruct (private_counter_pairs pool) as [pairs|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (describe_memory_ragged source) as [package|]; [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (propose (map named_operation_instruction (ragged_operations package))) as [[candidate steps]|];
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (compile_memory_ragged_width (described_shape (ragged_description package))
    (rectangle_bound (ragged_description package)) (ragged_parameter package)) as [width_tree|] eqn:LOWER;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  destruct (compile_named_array_candidate (described_shape (ragged_description package)) (ragged_operations package)
    (rectangle_bound (ragged_description package)) (ragged_parameter package) live pairs candidate) as [code|] eqn:COMPILE;
    [|intro CHECK; apply mayReturn_pure in CHECK; discriminate].
  intro CHECK; bind_imp_destruct CHECK valid VALID; apply mayReturn_pure in CHECK.
  destruct valid; [inversion CHECK; subst target|discriminate].
  apply memory_ragged_target_sound with (pairs := pairs) (candidate := candidate); [exact COMPILE|exact LOWER|].
  eapply checked_named_ragged_candidate_correct; exact VALID.
Qed.
Print Assumptions check_memory_ragged_mapped_region_sound.
