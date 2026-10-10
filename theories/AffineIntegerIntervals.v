From Stdlib Require Import List ZArith Lia.
From polcert.lib Require Import Linalg.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Sufficient ranges for mathematical affine obligations. Hosts supply the
    facts that actual inputs inhabit these intervals; unknown dimensions refuse. *)
Definition integer_interval := (Z * Z)%type.
Definition integer_interval_contains (interval : integer_interval) value :=
  fst interval <= value <= snd interval.
Definition integer_interval_scale coefficient (interval : integer_interval) :=
  if 0 <=? coefficient then (coefficient * fst interval, coefficient * snd interval)
  else (coefficient * snd interval, coefficient * fst interval).
Definition integer_interval_sum (first second : integer_interval) :=
  (fst first + fst second, snd first + snd second).

Lemma integer_interval_scale_sound coefficient interval value :
  integer_interval_contains interval value ->
  integer_interval_contains (integer_interval_scale coefficient interval) (coefficient * value).
Proof.
  destruct interval as [lower upper]; unfold integer_interval_contains,integer_interval_scale; cbn.
  destruct (0 <=? coefficient) eqn:SIGN; [apply Z.leb_le in SIGN|apply Z.leb_gt in SIGN]; cbn; nia.
Qed.
Lemma integer_interval_sum_sound first second a b :
  integer_interval_contains first a -> integer_interval_contains second b ->
  integer_interval_contains (integer_interval_sum first second) (a+b).
Proof. destruct first,second; unfold integer_interval_contains,integer_interval_sum; cbn; lia. Qed.

Fixpoint affine_dot_interval (coefficients : list Z) (intervals : list integer_interval) :=
  match coefficients,intervals with
  | [],_ => Some (0,0)
  | coefficient::rest,interval::tail =>
      option_map (integer_interval_sum (integer_interval_scale coefficient interval))
        (affine_dot_interval rest tail)
  | _,_ => None end.
Theorem affine_dot_interval_sound coefficients intervals values result :
  Forall2 integer_interval_contains intervals values ->
  affine_dot_interval coefficients intervals = Some result ->
  integer_interval_contains result (dot_product coefficients values).
Proof.
  revert intervals values result; induction coefficients as [|coefficient rest IH];
    intros intervals values result FACTS ENCODE.
  - cbn [affine_dot_interval] in ENCODE; inversion ENCODE; subst result.
    rewrite dot_product_nil_left; change (0 <= 0 <= 0); lia.
  - destruct intervals as [|interval tail]; [discriminate|].
    inversion FACTS as [|interval' value intervals' remaining CELL TAIL]; subst.
    cbn [affine_dot_interval] in ENCODE.
    destruct (affine_dot_interval rest tail) as [next|] eqn:NEXT; [|discriminate].
    inversion ENCODE; subst result; cbn [dot_product].
    apply integer_interval_sum_sound.
    + apply integer_interval_scale_sound; exact CELL.
    + eapply IH; eauto.
Qed.

Definition affine_integer_interval coefficients constant intervals :=
  option_map (fun interval => (fst interval+constant,snd interval+constant))
    (affine_dot_interval coefficients intervals).
Theorem affine_integer_interval_sound coefficients constant intervals values result :
  Forall2 integer_interval_contains intervals values ->
  affine_integer_interval coefficients constant intervals = Some result ->
  integer_interval_contains result (dot_product coefficients values+constant).
Proof.
  intros FACTS ENCODE; unfold affine_integer_interval in ENCODE.
  destruct (affine_dot_interval coefficients intervals) as [[lower upper]|] eqn:DOT; [|discriminate].
  inversion ENCODE; subst result.
  pose proof (@affine_dot_interval_sound coefficients intervals values (lower,upper) FACTS DOT) as BOUNDS.
  unfold integer_interval_contains in *; cbn in *; lia.
Qed.

Print Assumptions integer_interval_scale_sound.
Print Assumptions affine_dot_interval_sound.
Print Assumptions affine_integer_interval_sound.
