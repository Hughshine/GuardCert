From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From GuardMemory Require Import GuardMemoryNaryCompute GuardMemoryPointerSourceWords GuardMemorySourceParameters.
From GuardAffineNest Require Import AffineNestSyntax AffineNestSourceDecode AffineNestBoundWords
  AffineNestUsedWords AffineNestGuardWords.
Import ListNotations.
Set Implicit Arguments.

Definition affine_position_registers (layout : list ident) positions := flat_map(fun position =>
  match nth_error layout position with Some identifier=>[identifier]|None=>[] end) positions.
Definition affine_leaf_used_registers layout scalars operations := flat_map(fun operation =>
  memory_pointer_operation_address_reads operation++
  affine_position_registers (layout++scalars)
    (memory_source_parameter_positions(memory_nary_compute_value operation))) operations.

Lemma affine_position_registers_sound layout positions identifier :
  In identifier(affine_position_registers layout positions) ->
  exists index, In index positions /\ nth_error layout index=Some identifier.
Proof.
  intro MEMBER; apply in_flat_map in MEMBER as [index [INDEX MEMBER]].
  destruct(nth_error layout index) as [value|] eqn:LOOKUP; [|contradiction].
  cbn in MEMBER; destruct MEMBER as [SAME|BAD]; [subst; exists index; auto|contradiction].
Qed.
Lemma affine_leaf_used_registers_sound layout scalars operations identifier :
  In identifier(affine_leaf_used_registers layout scalars operations) ->
  affine_leaf_register_used layout scalars operations identifier.
Proof.
  intro MEMBER; apply in_flat_map in MEMBER as [operation [OPERATION MEMBER]].
  exists operation; split; [exact OPERATION|].
  apply in_app_or in MEMBER; destruct MEMBER as [ADDRESS|VALUE]; [left; exact ADDRESS|right].
  destruct(@affine_position_registers_sound (layout++scalars)
    (memory_source_parameter_positions(memory_nary_compute_value operation)) identifier VALUE)
    as [index [USED LOOKUP]]; exists index; auto.
Qed.

Definition affine_guard_used_registers nest layout scalars operations := match nest with
  | AffineSourceLeaf _ => affine_leaf_used_registers layout scalars operations
  | AffineSourceAxis _ bound _ _ _ => bound::affine_tail_bound_reads nest++affine_leaf_used_registers layout scalars operations end.
Lemma affine_guard_used_registers_sound nest layout scalars operations identifier :
  In identifier(affine_guard_used_registers nest layout scalars operations) ->
  affine_guard_register_used nest layout scalars operations identifier.
Proof.
  destruct nest; cbn [affine_guard_used_registers affine_guard_register_used].
  - apply affine_leaf_used_registers_sound.
  - intros [ROOT|MEMBER]; [left; symmetry; exact ROOT|right].
    apply in_app_or in MEMBER; destruct MEMBER as [BOUND|LEAF]; [left; exact BOUND|right; apply affine_leaf_used_registers_sound; exact LEAF].
Qed.

(** Extra, unused parameters are refused, rather than eagerly read by the
    guard. The three supported definitions are root headers, conditionally
    reached child bounds, and actually executed leaf expressions. *)
Definition check_affine_guard_parameters nest layout scalars operations parameters :=
  forallb(fun identifier =>
    existsb(Pos.eqb identifier)(affine_guard_used_registers nest layout scalars operations) &&
    negb(existsb(Pos.eqb identifier)(affine_nest_mutated nest))) parameters.

Theorem check_affine_guard_parameters_sound nest layout scalars operations parameters :
  check_affine_guard_parameters nest layout scalars operations parameters=true ->
  forall identifier, In identifier parameters ->
    affine_guard_register_used nest layout scalars operations identifier /\ ~In identifier(affine_nest_mutated nest).
Proof.
  intros CHECK identifier MEMBER; apply forallb_forall with(x:=identifier) in CHECK; [|exact MEMBER].
  apply andb_true_iff in CHECK as [USED FRESH]; apply existsb_exists in USED as [registered [USED SAME]].
  apply Pos.eqb_eq in SAME; subst registered; split; [apply affine_guard_used_registers_sound; exact USED|].
  apply negb_true_iff in FRESH; intro BAD.
  assert (FOUND:existsb(Pos.eqb identifier)(affine_nest_mutated nest)=true).
  { apply existsb_exists; exists identifier; split; [exact BAD|apply Pos.eqb_refl]. }
  congruence.
Qed.
Print Assumptions check_affine_guard_parameters_sound.
