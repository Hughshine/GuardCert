From Stdlib Require Import List ZArith.
From GuardInterface Require Import AffineBoxEnvelope.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A covering box may have a static second count. Substitution removes that
    count from the runtime header; no language register is invented for it. *)
Definition affine_fix_second (constant : Z) (form : affine_form) : affine_form :=
  match fst form with
  | first::second::rest => (first::rest,snd form+second*constant)
  | coefficients => (coefficients,snd form)
  end.

Theorem affine_fix_second_value constant form first parameters :
  affine_value (affine_fix_second constant form) (first::parameters) =
    affine_value form (first::constant::parameters).
Proof.
  destruct form as [[|a [|b rest]] bias]; cbn [affine_fix_second fst snd];
    unfold affine_value; cbn [affine_dot fst snd]; ring.
Qed.

Print Assumptions affine_fix_second_value.
