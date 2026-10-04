From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCountedLoop ClightTempFootprint.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryWindowCheck GuardMemoryAffineAxisRenaming.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode AffineNestGuardPackage
  AffineNestPackageDecode AffineNestShadowExit AffineNestShadowTransport AffineNestStaticPackage AffineNestScanNamespace.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_multi_right_controls proposal allocated := memory_affine_axis_rename
  (affine_nest_controls(affine_proposal_nest proposal))
  (firstn(length(affine_nest_controls(affine_proposal_nest proposal)))
    (skipn(length(affine_nest_controls(affine_proposal_nest proposal))) allocated)).
Definition affine_multi_left_live proposal live := map(affine_proposal_rename proposal)
  (affine_nest_controls(affine_proposal_nest proposal))++live.

Record affine_multi_static_package source parameters live allocated proposal := AffineMultiStaticPackage {
  affine_multi_guard : affine_guard_package source parameters live proposal;
  affine_multi_pointer_private : forall pointer, In pointer(affine_proposed_pointers proposal) ->
    ~In pointer(affine_nest_mutated(affine_proposal_nest proposal));
  affine_multi_pointer_public : incl(affine_proposed_pointers proposal) live;
  affine_multi_parameters_public : incl parameters live;
  affine_multi_root_public : In(affine_proposed_iterator proposal) live;
  affine_multi_window_low : signed_range(affine_proposed_window_lower proposal);
  affine_multi_window_high : signed_range(affine_proposed_window_upper proposal-1);
  affine_multi_window_span : 4*(affine_proposed_window_upper proposal-affine_proposed_window_lower proposal)<=Ptrofs.modulus;
  affine_multi_source_loop : L.stmt;
  affine_multi_source_lower : affine_package_source_loop parameters proposal=Some affine_multi_source_loop;
  affine_multi_shadow_scope : statement_scope live(affine_shadow_source(affine_proposal_nest proposal));
  affine_multi_left_namespace : affine_scan_namespace(affine_proposal_nest proposal) parameters live
    (affine_proposal_rename proposal)(affine_proposed_result proposal);
  affine_multi_right_namespace : affine_scan_namespace(affine_proposal_nest proposal) parameters(affine_multi_left_live proposal live)
    (affine_multi_right_controls proposal allocated)(affine_proposed_result proposal);
  affine_multi_allocated : incl(affine_proposed_result proposal::
    map(affine_proposal_rename proposal)(affine_nest_controls(affine_proposal_nest proposal))++
    map(affine_multi_right_controls proposal allocated)(affine_nest_controls(affine_proposal_nest proposal))) allocated
}.

Definition check_affine_multi_static_package source parameters live allocated proposal :
  option(affine_multi_static_package source parameters live allocated proposal).
Proof.
  destruct(check_affine_guard_package source parameters live proposal) as [guard|]; [|exact None].
  destruct(forallb(fun pointer=>negb(affine_ident_member_check pointer(affine_nest_mutated(affine_proposal_nest proposal))))
    (affine_proposed_pointers proposal)) eqn:PRIVATE; [|exact None].
  destruct(affine_names_allocated_check(affine_proposed_pointers proposal++parameters++[affine_proposed_iterator proposal]) live) eqn:PUBLIC;
    [|exact None].
  destruct(window_signed_check(affine_proposed_window_lower proposal)) eqn:LOW; [|exact None].
  destruct(window_signed_check(affine_proposed_window_upper proposal-1)) eqn:HIGH; [|exact None].
  destruct(4*(affine_proposed_window_upper proposal-affine_proposed_window_lower proposal)<=?Ptrofs.modulus) eqn:SPAN; [|exact None].
  destruct(affine_package_source_loop parameters proposal) as [source_loop|] eqn:LOWER; [|exact None].
  destruct(affine_statement_scope_check live(affine_shadow_source(affine_proposal_nest proposal))) eqn:SCOPE; [|exact None].
  destruct(check_affine_scan_namespace(affine_proposal_nest proposal) parameters live(affine_proposal_rename proposal)
    (affine_proposed_result proposal)) as [left_names|]; [|exact None].
  destruct(check_affine_scan_namespace(affine_proposal_nest proposal) parameters(affine_multi_left_live proposal live)
    (affine_multi_right_controls proposal allocated)(affine_proposed_result proposal)) as [right_names|]; [|exact None].
  destruct(affine_names_allocated_check(affine_proposed_result proposal::
    map(affine_proposal_rename proposal)(affine_nest_controls(affine_proposal_nest proposal))++
    map(affine_multi_right_controls proposal allocated)(affine_nest_controls(affine_proposal_nest proposal))) allocated) eqn:ALLOCATED;
    [|exact None].
  pose proof(@affine_names_allocated_check_sound _ _ PUBLIC) as LIVE.
  assert(POINTER_PRIVATE:forall pointer, In pointer(affine_proposed_pointers proposal) ->
    ~In pointer(affine_nest_mutated(affine_proposal_nest proposal))).
  { intros pointer MEMBER; apply affine_ident_private_check_sound.
    apply forallb_forall with(x:=pointer) in PRIVATE; [apply negb_true_iff; exact PRIVATE|exact MEMBER]. }
  refine(Some(@AffineMultiStaticPackage source parameters live allocated proposal guard POINTER_PRIVATE _ _ _
    (@window_signed_check_sound _ LOW)(@window_signed_check_sound _ HIGH)(proj1(Z.leb_le _ _) SPAN)
    source_loop LOWER(@affine_statement_scope_check_sound _ _ SCOPE) left_names right_names
    (@affine_names_allocated_check_sound _ _ ALLOCATED))).
  - intros identifier MEMBER; apply LIVE,in_or_app; auto.
  - intros identifier MEMBER; apply LIVE,in_or_app; right; apply in_or_app; auto.
  - apply LIVE,in_or_app; right; apply in_or_app; right; cbn; auto.
Defined.
Print Assumptions check_affine_multi_static_package.
