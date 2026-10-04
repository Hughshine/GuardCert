From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From GuardMemory Require Import GuardMemoryRecursiveSyntax.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestStaticPackage.
Import ListNotations.
Set Implicit Arguments.

Definition affine_scan_values nest controls identifier :=
  if affine_ident_member_check identifier(affine_nest_iterators nest) then controls identifier else identifier.
Lemma affine_scan_values_iterator nest controls identifier :
  In identifier(affine_nest_iterators nest) -> affine_scan_values nest controls identifier=controls identifier.
Proof.
  intro MEMBER; unfold affine_scan_values,affine_ident_member_check.
  assert(FOUND:existsb(Pos.eqb identifier)(affine_nest_iterators nest)=true).
  { apply existsb_exists; exists identifier; split; [exact MEMBER|apply Pos.eqb_refl]. }
  rewrite FOUND; reflexivity.
Qed.

Record affine_scan_namespace nest parameters live controls flag := AffineScanNamespace {
  affine_scan_names_unique : NoDup(map controls(affine_nest_controls nest));
  affine_scan_names_private : forall identifier, In identifier(affine_nest_controls nest) ->
    ~In(controls identifier)(parameters++live) /\ controls identifier<>flag;
  affine_scan_names_flag_private : ~In flag(parameters++live);
  affine_scan_names_parameters : forall identifier, In identifier parameters ->
    affine_scan_values nest controls identifier=identifier
}.

Definition affine_scan_names_check nest parameters live controls flag :=
  memory_identifiers_unique_check(map controls(affine_nest_controls nest)) &&
  forallb(fun identifier=>negb(affine_ident_member_check(controls identifier)(parameters++live))&&
    negb(Pos.eqb(controls identifier) flag))(affine_nest_controls nest) &&
  negb(affine_ident_member_check flag(parameters++live)) &&
  forallb(fun identifier=>Pos.eqb(affine_scan_values nest controls identifier) identifier) parameters.

Print Assumptions affine_scan_values_iterator.

Definition check_affine_scan_namespace nest parameters live controls flag : option(affine_scan_namespace nest parameters live controls flag).
Proof.
  destruct(memory_identifiers_unique_check(map controls(affine_nest_controls nest))) eqn:UNIQUE; [|exact None].
  destruct(forallb(fun identifier=>negb(affine_ident_member_check(controls identifier)(parameters++live))&&
    negb(Pos.eqb(controls identifier) flag))(affine_nest_controls nest)) eqn:PRIVATE; [|exact None].
  destruct(affine_ident_member_check flag(parameters++live)) eqn:FLAG; [exact None|].
  destruct(forallb(fun identifier=>Pos.eqb(affine_scan_values nest controls identifier) identifier) parameters) eqn:PARAMETERS;
    [|exact None].
  assert(FRESH:forall identifier, In identifier(affine_nest_controls nest) ->
    ~In(controls identifier)(parameters++live) /\ controls identifier<>flag).
  { intros identifier MEMBER; apply forallb_forall with(x:=identifier) in PRIVATE; [|exact MEMBER].
    apply andb_true_iff in PRIVATE as [PUBLIC NOT_FLAG]; apply negb_true_iff in PUBLIC,NOT_FLAG.
    split; [apply affine_ident_private_check_sound; exact PUBLIC|apply Pos.eqb_neq; exact NOT_FLAG]. }
  assert(PARAMETER_VALUES:forall identifier, In identifier parameters -> affine_scan_values nest controls identifier=identifier).
  { intros identifier MEMBER; apply forallb_forall with(x:=identifier) in PARAMETERS; [|exact MEMBER].
    apply Pos.eqb_eq; exact PARAMETERS. }
  exact(Some(@AffineScanNamespace nest parameters live controls flag
    (@memory_identifiers_unique_check_sound _ UNIQUE) FRESH(@affine_ident_private_check_sound _ _ FLAG) PARAMETER_VALUES)).
Defined.
Print Assumptions check_affine_scan_namespace.
