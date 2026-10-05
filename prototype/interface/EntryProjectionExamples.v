From Stdlib Require Import Bool List ZArith Lia.
From GuardInterface Require Import AssumptionDerivation.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record rectangle_parameters := RectangleParameters {
  outer_count : Z;
  inner_count : Z;
  row_stride : Z;
  address_limit : Z
}.

Definition rectangle_occurs p (point : Z * Z) :=
  0 <= fst point < outer_count p /\ 0 <= snd point < inner_count p.

Definition address_requirement : assumption_site rectangle_parameters (Z * Z) :=
  {| site_occurs := rectangle_occurs;
     site_holds := fun p point =>
       (0 <=? row_stride p * fst point + snd point) &&
       (row_stride p * fst point + snd point <=? address_limit p) |}.

(** This conservative endpoint condition has no iteration variables. The
    proof validates its implication, without trusting a polyhedral solver. *)
Definition rectangle_entry_condition p :=
  0 <= outer_count p /\ 0 <= inner_count p /\ 0 <= row_stride p /\
  row_stride p * (outer_count p - 1) + (inner_count p - 1) <= address_limit p.

Theorem rectangular_address_derivation :
  entry_derivation (fun _ => True) [address_requirement] rectangle_entry_condition.
Proof.
  constructor; intros p _ [OUTER [INNER [STRIDE LIMIT]]] site MEMBER [i j] OCCURS.
  destruct MEMBER as [SAME|EMPTY]; [subst site|contradiction].
  cbn [rectangle_occurs address_requirement] in OCCURS |- *; destruct OCCURS as [I J].
  cbn in I, J |- *.
  apply andb_true_iff; split; apply Z.leb_le.
  - nia.
  - assert (BOUND : row_stride p * i <= row_stride p * (outer_count p - 1)).
    { apply Z.mul_le_mono_nonneg_l; lia. }
    nia.
Qed.

(** Textual bound evaluation must not disappear when the modeled body is
    empty. This site occurs at initialization even when there are no points. *)
Definition initial_add_requirement : assumption_site Z unit :=
  {| site_occurs := fun _ _ => True;
     site_holds := fun p _ => (0 <=? p + 1) && (p + 1 <? 256) |}.

Theorem initial_add_derivation :
  entry_derivation (fun _ => True) [initial_add_requirement] (fun p => 0 <= p < 255).
Proof.
  constructor; intros p _ RANGE site MEMBER point _.
  destruct MEMBER as [SAME|EMPTY]; [subst site|contradiction].
  cbn; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Example empty_body_still_requires_bound_check :
  ~ collected_obligations [initial_add_requirement] 255.
Proof.
  intro ALL; specialize (ALL initial_add_requirement (or_introl eq_refl) tt I).
  cbn in ALL; discriminate.
Qed.

(** A wrapped guard cannot certify a mathematical comparison. *)
Example unchecked_guard_false_acceptance :
  ((255 + 1) mod 256 <=? 50) = true /\ (255 + 1 <=? 50) = false.
Proof. vm_compute; auto. Qed.

(** The minor-dimension bound makes row-major delinearization injective;
    it does not assert allocation permissions for either address. *)
Theorem bounded_delinearization_injective stride i j other_i other_j :
  0 < stride -> 0 <= j < stride -> 0 <= other_j < stride ->
  stride * i + j = stride * other_i + other_j ->
  i = other_i /\ j = other_j.
Proof.
  intros STRIDE J OTHER ADDRESS.
  assert (ROW : i = other_i) by (destruct (Z.lt_trichotomy i other_i) as [LESS|[SAME|MORE]]; nia).
  subst other_i; split; [reflexivity|lia].
Qed.

Example out_of_dimension_collision :
  4 * 0 + 4 = 4 * 1 + 0 /\ (0, 4) <> (1, 0).
Proof. split; [reflexivity|congruence]. Qed.

Print Assumptions rectangular_address_derivation.
Print Assumptions initial_add_derivation.
Print Assumptions empty_body_still_requires_bound_check.
Print Assumptions unchecked_guard_false_acceptance.
Print Assumptions bounded_delinearization_injective.
Print Assumptions out_of_dimension_collision.
