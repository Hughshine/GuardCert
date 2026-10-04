From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCountedLoop ClightTempFootprint.
From GuardMemory Require Import GuardMemoryLoops GuardMemoryWindowCheck.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode AffineNestGuardPackage
  AffineNestPackageDecode AffineNestShadowExit AffineNestShadowTransport.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_ident_member_check identifier registers := existsb(Pos.eqb identifier) registers.
Lemma affine_ident_member_check_sound identifier registers : affine_ident_member_check identifier registers=true -> In identifier registers.
Proof. intro CHECK; apply existsb_exists in CHECK as [found [MEMBER SAME]]; apply Pos.eqb_eq in SAME; subst; exact MEMBER. Qed.
Lemma affine_ident_private_check_sound identifier registers : affine_ident_member_check identifier registers=false -> ~In identifier registers.
Proof.
  intros CHECK MEMBER; assert (FOUND:affine_ident_member_check identifier registers=true).
  { unfold affine_ident_member_check; apply existsb_exists; exists identifier; split; [exact MEMBER|apply Pos.eqb_refl]. }
  congruence.
Qed.
Definition affine_names_allocated_check registers allocated := forallb(fun identifier=>affine_ident_member_check identifier allocated) registers.
Lemma affine_names_allocated_check_sound registers allocated : affine_names_allocated_check registers allocated=true -> incl registers allocated.
Proof.
  intros CHECK identifier MEMBER; apply forallb_forall with(x:=identifier) in CHECK; [|exact MEMBER].
  apply affine_ident_member_check_sound; exact CHECK.
Qed.

Record affine_static_package source parameters live allocated proposal := AffineStaticPackage {
  affine_static_guard : affine_guard_package source parameters live proposal;
  affine_static_pointer : ident;
  affine_static_single : affine_proposed_pointers proposal=[affine_static_pointer];
  affine_static_pointer_private : ~In affine_static_pointer(affine_nest_mutated(affine_proposal_nest proposal));
  affine_static_pointer_public : In affine_static_pointer live;
  affine_static_window_low : signed_range(affine_proposed_window_lower proposal);
  affine_static_window_high : signed_range(affine_proposed_window_upper proposal-1);
  affine_static_window_span : 4*(affine_proposed_window_upper proposal-affine_proposed_window_lower proposal)<=Ptrofs.modulus;
  affine_static_source_loop : L.stmt;
  affine_static_source_lower : affine_package_source_loop parameters proposal=Some affine_static_source_loop;
  affine_static_shadow_scope : statement_scope live(affine_shadow_source(affine_proposal_nest proposal));
  affine_static_allocated : incl(affine_proposed_result proposal::affine_proposed_private_controls proposal) allocated
}.

Definition check_affine_static_package source parameters live allocated proposal : option(affine_static_package source parameters live allocated proposal).
Proof.
  destruct(check_affine_guard_package source parameters live proposal) as [guard|]; [|exact None].
  destruct(affine_proposed_pointers proposal) as [|pointer rest] eqn:SINGLE; [exact None|].
  destruct rest as [|other rest]; [|exact None].
  destruct(affine_ident_member_check pointer(affine_nest_mutated(affine_proposal_nest proposal))) eqn:PRIVATE; [exact None|].
  destruct(affine_ident_member_check pointer live) eqn:PUBLIC; [|exact None].
  destruct(window_signed_check(affine_proposed_window_lower proposal)) eqn:LOW; [|exact None].
  destruct(window_signed_check(affine_proposed_window_upper proposal-1)) eqn:HIGH; [|exact None].
  destruct(4*(affine_proposed_window_upper proposal-affine_proposed_window_lower proposal)<=?Ptrofs.modulus) eqn:SPAN; [|exact None].
  destruct(affine_package_source_loop parameters proposal) as [source_loop|] eqn:LOWER; [|exact None].
  destruct(affine_statement_scope_check live(affine_shadow_source(affine_proposal_nest proposal))) eqn:SCOPE; [|exact None].
  destruct(affine_names_allocated_check(affine_proposed_result proposal::affine_proposed_private_controls proposal) allocated) eqn:ALLOCATED;
    [|exact None].
  exact(Some(@AffineStaticPackage source parameters live allocated proposal guard pointer SINGLE
    (@affine_ident_private_check_sound _ _ PRIVATE)(@affine_ident_member_check_sound _ _ PUBLIC)
    (@window_signed_check_sound _ LOW)(@window_signed_check_sound _ HIGH)(proj1(Z.leb_le _ _) SPAN)
    source_loop LOWER(@affine_statement_scope_check_sound _ _ SCOPE)(@affine_names_allocated_check_sound _ _ ALLOCATED))).
Defined.
Print Assumptions check_affine_static_package.
