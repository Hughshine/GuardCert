From Stdlib Require Import List Bool ZArith Lia.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This derivation library has no language or memory semantics. Runtime
    counts bound integer coordinates; remaining variables are entry parameters.
    Its output is an affine formula over counts and those same parameters. *)
Definition affine_form := (list Z * Z)%type.
Fixpoint affine_dot coefficients values :=
  match coefficients,values with
  | coefficient::rest,value::tail => coefficient*value + affine_dot rest tail
  | _,_ => 0
  end.
Definition affine_value (form : affine_form) values := affine_dot (fst form) values + snd form.
Definition affine_sum values := fold_right Z.add 0 values.
Definition endpoint_coefficient (upper : bool) coefficient :=
  if upper then Z.max coefficient 0 else Z.min coefficient 0.
Fixpoint box_endpoint upper coefficients counts :=
  match coefficients,counts with
  | coefficient::rest,count::tail => endpoint_coefficient upper coefficient*(count-1) + box_endpoint upper rest tail
  | _,_ => 0
  end.
Definition affine_endpoint upper dimensions (form : affine_form) : affine_form :=
  let coefficients := map (endpoint_coefficient upper) (firstn dimensions (fst form)) in
  (coefficients ++ skipn dimensions (fst form),snd form-affine_sum coefficients).
Definition synthesize_affine_envelope dimensions (form : affine_form) : option (affine_form * affine_form) :=
  if (dimensions <=? length (fst form))%nat
  then Some (affine_endpoint false dimensions form,affine_endpoint true dimensions form)
  else None.

Lemma affine_dot_app first second left right : length first = length left ->
  affine_dot (first++second) (left++right) = affine_dot first left + affine_dot second right.
Proof.
  revert left; induction first; intros [|value left] LENGTH; cbn in *; try discriminate; [reflexivity|].
  rewrite IHfirst by lia; ring.
Qed.

Lemma box_endpoint_affine upper coefficients counts : length coefficients = length counts ->
  box_endpoint upper coefficients counts =
    affine_dot (map (endpoint_coefficient upper) coefficients) counts -
    affine_sum (map (endpoint_coefficient upper) coefficients).
Proof.
  revert counts; induction coefficients; intros [|count counts] LENGTH; cbn in *; try discriminate; [reflexivity|].
  rewrite IHcoefficients by lia; unfold affine_sum; cbn; ring.
Qed.

Theorem box_endpoint_bounds coefficients coordinates counts :
  length coefficients = length counts -> Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
  box_endpoint false coefficients counts <= affine_dot coefficients coordinates <= box_endpoint true coefficients counts.
Proof.
  intros LENGTH BOX; revert coefficients LENGTH; induction BOX; intros [|coefficient coefficients] LENGTH;
    cbn in LENGTH; try discriminate.
  - cbn; lia.
  - specialize (IHBOX coefficients ltac:(lia)); cbn [box_endpoint affine_dot endpoint_coefficient].
    destruct (Z_le_dec 0 coefficient).
    + rewrite Z.min_r,Z.max_l by lia; nia.
    + rewrite Z.min_l,Z.max_r by lia; nia.
Qed.

Theorem synthesized_affine_envelope_covers dimensions form lower upper coordinates counts parameters :
  synthesize_affine_envelope dimensions form = Some (lower,upper) ->
  length counts = dimensions -> Forall2 (fun coordinate count => 0 <= coordinate < count) coordinates counts ->
  affine_value lower (counts++parameters) <= affine_value form (coordinates++parameters) <=
    affine_value upper (counts++parameters).
Proof.
  unfold synthesize_affine_envelope; destruct (dimensions <=? length (fst form))%nat eqn:SIZE; [|discriminate].
  intro SYNTHESIZED; injection SYNTHESIZED as <- <-; intros COUNTS BOX.
  apply Nat.leb_le in SIZE.
  assert (LENGTH : length (firstn dimensions (fst form)) = length counts)
    by (rewrite length_firstn,Nat.min_l by exact SIZE; exact (eq_sym COUNTS)).
  pose proof (@box_endpoint_bounds (firstn dimensions (fst form)) coordinates counts LENGTH BOX) as BOUNDS.
  pose proof (Forall2_length BOX) as COORDINATES.
  assert (DOT : affine_dot (fst form) (coordinates++parameters) =
    affine_dot (firstn dimensions (fst form)) coordinates + affine_dot (skipn dimensions (fst form)) parameters).
  { rewrite <- (firstn_skipn dimensions (fst form)) at 1.
    apply affine_dot_app; rewrite LENGTH; lia. }
  rewrite !box_endpoint_affine in BOUNDS by exact LENGTH.
  unfold affine_value,affine_endpoint; cbn [fst snd].
  rewrite !affine_dot_app by (rewrite length_map; exact LENGTH).
  rewrite DOT.
  cbn [fst snd] in *; lia.
Qed.

(** The generated Boolean is sufficient for all pairs of source instances.
    Refusal has no claim of overlap: affine interval envelopes can be coarse. *)
Definition affine_envelopes_disjoint first second header :=
  (affine_value (snd first) header <? affine_value (fst second) header) ||
  (affine_value (snd second) header <? affine_value (fst first) header).
Theorem synthesized_affine_envelopes_disjoint dimensions first second first_bounds second_bounds
  counts parameters left right :
  synthesize_affine_envelope dimensions first = Some first_bounds ->
  synthesize_affine_envelope dimensions second = Some second_bounds ->
  length counts = dimensions ->
  Forall2 (fun coordinate count => 0 <= coordinate < count) left counts ->
  Forall2 (fun coordinate count => 0 <= coordinate < count) right counts ->
  affine_envelopes_disjoint first_bounds second_bounds (counts++parameters) = true ->
  affine_value first (left++parameters) <> affine_value second (right++parameters).
Proof.
  destruct first_bounds as [first_lower first_upper],second_bounds as [second_lower second_upper].
  intros FIRST SECOND COUNTS LEFT RIGHT DISJOINT.
  pose proof (@synthesized_affine_envelope_covers dimensions first first_lower first_upper left counts parameters
    FIRST COUNTS LEFT) as FIRST_RANGE.
  pose proof (@synthesized_affine_envelope_covers dimensions second second_lower second_upper right counts parameters
    SECOND COUNTS RIGHT) as SECOND_RANGE.
  unfold affine_envelopes_disjoint in DISJOINT; cbn [fst snd] in DISJOINT.
  rewrite orb_true_iff,!Z.ltb_lt in DISJOINT; destruct DISJOINT; lia.
Qed.

(** A language chooses the machine interval. This conservative range checker
    proves that the generated affine values, for all permitted entry values,
    fit that interval. It does not inspect or enumerate source coordinates. *)
Definition affine_form_range_check minimum maximum limits (form : affine_form) :=
  Nat.eqb (length (fst form)) (length limits) &&
  (minimum <=? box_endpoint false (fst form) limits + snd form) &&
  (box_endpoint true (fst form) limits + snd form <=? maximum).
Theorem checked_affine_form_range minimum maximum limits form values :
  affine_form_range_check minimum maximum limits form = true ->
  Forall2 (fun value limit => 0 <= value < limit) values limits ->
  minimum <= affine_value form values <= maximum.
Proof.
  unfold affine_form_range_check; rewrite !andb_true_iff,Nat.eqb_eq,!Z.leb_le.
  intros [[LENGTH MINIMUM] MAXIMUM] VALUES.
  pose proof (@box_endpoint_bounds (fst form) values limits LENGTH VALUES) as BOUNDS.
  unfold affine_value; lia.
Qed.

(** Entry parameters may be negative. Inclusive intervals are independent of
    the nonnegative, half-open coordinate boxes used by envelope derivation. *)
Fixpoint affine_interval_endpoint (upper : bool) (coefficients : list Z) (ranges : list (Z * Z)) : Z :=
  match coefficients,ranges with
  | coefficient::rest,(low,high)::tail =>
      coefficient*(if upper then if 0 <=? coefficient then high else low
                    else if 0 <=? coefficient then low else high) +
      affine_interval_endpoint upper rest tail
  | _,_ => 0 end.
Definition affine_interval_range_check minimum maximum ranges (form : affine_form) :=
  Nat.eqb (length (fst form)) (length ranges) &&
  (minimum <=? affine_interval_endpoint false (fst form) ranges + snd form) &&
  (affine_interval_endpoint true (fst form) ranges + snd form <=? maximum).
Theorem affine_interval_bounds coefficients values ranges :
  length coefficients = length ranges ->
  Forall2 (fun value range => fst range <= value <= snd range) values ranges ->
  affine_interval_endpoint false coefficients ranges <= affine_dot coefficients values <=
    affine_interval_endpoint true coefficients ranges.
Proof.
  intros LENGTH VALUES; revert coefficients LENGTH; induction VALUES;
    intros [|coefficient coefficients] LENGTH; cbn in LENGTH; try discriminate.
  - cbn; lia.
  - specialize (IHVALUES coefficients ltac:(lia)); destruct y as [low high].
    cbn [affine_interval_endpoint affine_dot fst snd] in *.
    destruct (0 <=? coefficient) eqn:SIGN;
      [apply Z.leb_le in SIGN|apply Z.leb_gt in SIGN]; nia.
Qed.
Theorem checked_affine_interval_range minimum maximum ranges form values :
  affine_interval_range_check minimum maximum ranges form = true ->
  Forall2 (fun value range => fst range <= value <= snd range) values ranges ->
  minimum <= affine_value form values <= maximum.
Proof.
  unfold affine_interval_range_check; rewrite !andb_true_iff,Nat.eqb_eq,!Z.leb_le.
  intros [[LENGTH MINIMUM] MAXIMUM] VALUES.
  pose proof (@affine_interval_bounds (fst form) values ranges LENGTH VALUES) as BOUNDS.
  unfold affine_value; lia.
Qed.

Example affine_envelope_signed_two_axes :
  synthesize_affine_envelope 2 ([16;-1;1],32) =
    Some (([0;-1;1],33),([16;0;1],16)).
Proof. reflexivity. Qed.

Example affine_envelope_disjoint_runtime_counts :
  affine_envelopes_disjoint
    (affine_endpoint false 2 ([16;1;1;0],32),affine_endpoint true 2 ([16;1;1;0],32))
    (affine_endpoint false 2 ([16;1;0;1],33),affine_endpoint true 2 ([16;1;0;1],33))
    [2;2;0;63] = true.
Proof. reflexivity. Qed.

Print Assumptions box_endpoint_bounds.
Print Assumptions synthesized_affine_envelope_covers.
Print Assumptions synthesized_affine_envelopes_disjoint.
Print Assumptions checked_affine_form_range.
Print Assumptions checked_affine_interval_range.
