From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet ClightTempFrame.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstLeaf AffineNestLeafModel
  AffineNestGuardWords AffineNestGuardParameterCheck AffineNestValuation.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_source_guard_parameter_domains nest bounds lower upper layout scalars pointers operations
  (certificate:affine_leaf_certificate(affine_nest_leaf nest) bounds lower upper layout scalars pointers operations)
  parameters fe ge locals temps memory after final :
  check_affine_guard_parameters nest layout scalars operations parameters=true ->
  affine_nest_shapes nest -> NoDup(affine_nest_controls nest) -> affine_first_path_active nest temps ->
  exec_stmt fe ge locals temps memory(affine_nest_source nest) E0 after final Out_normal ->
  Forall(fun identifier => register_domain identifier(Entry ge locals temps memory)) parameters.
Proof.
  intros CHECK SHAPES FRESH ACTIVE SOURCE; apply Forall_forall; intros identifier MEMBER.
  destruct(@check_affine_guard_parameters_sound nest layout scalars operations parameters CHECK identifier MEMBER)
    as [USED PRIVATE].
  exact(@affine_source_guard_register_defined nest bounds lower upper layout scalars pointers operations certificate
    fe ge locals temps memory after final identifier SHAPES FRESH PRIVATE ACTIVE USED SOURCE).
Qed.

Lemma affine_register_domains_word_view parameters ge locals temps memory :
  Forall(fun identifier => register_domain identifier(Entry ge locals temps memory)) parameters ->
  affine_word_view parameters(affine_word_valuation temps) temps.
Proof.
  intros DOMAINS identifier MEMBER; apply Forall_forall with(x:=identifier) in DOMAINS; [|exact MEMBER].
  destruct DOMAINS as [word WORD]; cbn [entry_temps] in WORD.
  unfold affine_word_valuation,temp_word; rewrite WORD,Int.repr_signed; reflexivity.
Qed.

Lemma affine_register_domains_transport parameters ge locals before after memory :
  Forall(fun identifier => register_domain identifier(Entry ge locals before memory)) parameters ->
  temp_agree parameters before after ->
  Forall(fun identifier => register_domain identifier(Entry ge locals after memory)) parameters.
Proof.
  intros DOMAINS FRAME; apply Forall_forall; intros identifier MEMBER.
  apply Forall_forall with(x:=identifier) in DOMAINS; [|exact MEMBER].
  destruct DOMAINS as [word WORD]; exists word; cbn [entry_temps] in *; rewrite FRAME by exact MEMBER; exact WORD.
Qed.
Print Assumptions affine_source_guard_parameter_domains.
Print Assumptions affine_register_domains_word_view.
Print Assumptions affine_register_domains_transport.
