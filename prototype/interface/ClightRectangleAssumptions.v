From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Integers.
From compcert.common Require Import Events.
From Guard Require Import ClightCondition ClightNoWrap ClightCountedLoop ClightRectangularStore ClightRectangularGuard
  ClightRectangularSelector.
From GuardInterface Require Import GuardInterface GuardedRewrite AssumptionDerivation
  ClightReadonlyRewrite ClightReadonlyRectangle.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Requirements for the canonical rectangular model. These textual positions
    include heads, resets and increments, not only memory-access instances.
    Binding actual source syntax/execution is the rectangle certificate and
    execution decoder's job. Data payload arithmetic retains machine semantics. *)
Inductive rectangle_site_kind :=
| OuterHead | OuterStep | InnerReset | InnerHead | InnerStep
| IndexMultiply | IndexAdd | ByteOffset.

Definition rectangle_model_rows d entry :=
  Int.signed (temp_word (rectangle_bound d) (entry_temps entry)).
Definition rectangle_model_columns d entry :=
  Int.signed (temp_word (rectangle_inner_bound d) (entry_temps entry)).
Definition rectangle_body_occurs d entry (point : Z * Z) :=
  0 <= fst point < rectangle_model_rows d entry /\
  0 <= snd point < rectangle_model_columns d entry.
Definition signed_fits z := (Int.min_signed <=? z) && (z <=? Int.max_signed).
Definition pointer_fits z := (0 <=? z) && (z <=? Ptrofs.max_unsigned).

Definition rectangle_text_site d kind : assumption_site clight_entry (Z * Z) :=
  {| site_occurs := fun entry point =>
       match kind with
       | OuterHead => 0 <= fst point <= rectangle_model_rows d entry
       | OuterStep => 0 <= fst point < rectangle_model_rows d entry
       | InnerReset => 0 <= fst point < rectangle_model_rows d entry /\ snd point = 0
       | InnerHead => 0 <= fst point < rectangle_model_rows d entry /\
                      0 <= snd point <= rectangle_model_columns d entry
       | _ => rectangle_body_occurs d entry point
       end;
     site_holds := fun entry point =>
       match kind with
       | OuterHead => signed_fits (fst point)
       | OuterStep => signed_fits (fst point + 1)
       | InnerReset => signed_fits 0
       | InnerHead => signed_fits (snd point)
       | InnerStep => signed_fits (snd point + 1)
       | IndexMultiply => signed_fits (fst point * rectangle_stride (described_shape d))
       | IndexAdd => signed_fits (fst point * rectangle_stride (described_shape d) + snd point)
       | ByteOffset => pointer_fits (4 * (fst point * rectangle_stride (described_shape d) + snd point))
       end |}.

Definition rectangle_text_sites d := map (rectangle_text_site d)
  [OuterHead; OuterStep; InnerReset; InnerHead; InnerStep; IndexMultiply; IndexAdd; ByteOffset].

Theorem rectangle_text_derivation d (VALID : rectangle_layout_valid (described_shape d)) :
  entry_derivation (fun _ : clight_entry => True) (rectangle_text_sites d) (readonly_rectangle_premise d).
Proof.
  constructor; intros entry _ [ZERO [[ND NR] [MD MR]]] site MEMBER [i j] OCCURS.
  unfold rectangle_text_sites in MEMBER; apply in_map_iff in MEMBER.
  destruct MEMBER as [kind [SAME MEMBER]]; subst site.
  pose proof (rectangle_limits VALID) as [NL [ML [POS SIZE]]].
  unfold rectangle_layout_valid in VALID; destruct VALID as [EXTENT [EXTENT_MAX [STRIDE [STRIDE_MAX PTR]]]].
  change (0 < rectangle_model_rows d entry <= rectangle_outer_limit (described_shape d)) in NR.
  change (0 < rectangle_model_columns d entry <= rectangle_stride (described_shape d)) in MR.
  unfold signed_range in NL, ML.
  destruct kind; cbn [rectangle_text_site site_occurs site_holds rectangle_body_occurs fst snd] in OCCURS |- *;
    unfold signed_fits, pointer_fits; apply andb_true_iff; split; apply Z.leb_le;
    change Int.min_signed with (-2147483648) in *; try lia.
  all: destruct OCCURS as [I J]; cbn in I, J; nia.
Qed.

Theorem accepted_rectangle_text_requirements source d (CERT : rectangle_certificate source d) entry :
  readonly_rectangle_domain d entry -> decision_run entry (readonly_rectangle_tree CERT) true ->
  collected_obligations (rectangle_text_sites d) entry.
Proof.
  intros DOMAIN RUN.
  destruct (readonly_sound (readonly_rectangle_condition (fun _ _ _ _ _ _ _ => False) CERT) entry true entry
    DOMAIN (conj RUN eq_refl)) as [_ ACCEPT].
  exact (entry_derivation_sound (rectangle_text_derivation d (rectangle_layout_bound CERT)) entry I (ACCEPT eq_refl)).
Qed.

Theorem accepted_rectangle_address_injective d entry first second :
  readonly_rectangle_premise d entry -> rectangle_body_occurs d entry first ->
  rectangle_body_occurs d entry second ->
  fst first * rectangle_stride (described_shape d) + snd first =
    fst second * rectangle_stride (described_shape d) + snd second -> first = second.
Proof.
  destruct first as [i j], second as [other_i other_j].
  intros [_ [_ [_ RANGE]]] [I J] [OTHER_I OTHER_J] ADDRESS.
  cbn [rectangle_body_occurs fst snd] in I, J, OTHER_I, OTHER_J, ADDRESS |- *.
  change (0 < rectangle_model_columns d entry <= rectangle_stride (described_shape d)) in RANGE.
  assert (ROW : i = other_i) by (destruct (Z.lt_trichotomy i other_i) as [LESS|[SAME|MORE]]; nia).
  subst other_i; assert (COLUMN : j = other_j) by nia; subst other_j; reflexivity.
Qed.

(** Reification into the concrete machine operations used by rect_index and
    rect_lvalue. This concerns control/address arithmetic, not payload values. *)
Theorem collected_rectangle_machine_index d entry i j :
  collected_obligations (rectangle_text_sites d) entry ->
  rectangle_body_occurs d entry (i,j) ->
  Int.signed (Int.mul (Int.repr i) (Int.repr (rectangle_stride (described_shape d)))) =
    i * rectangle_stride (described_shape d) /\
  Int.signed (Int.add (Int.mul (Int.repr i) (Int.repr (rectangle_stride (described_shape d))))
    (Int.repr j)) = i * rectangle_stride (described_shape d) + j /\
  Ptrofs.unsigned (Ptrofs.repr (4 * (i * rectangle_stride (described_shape d) + j))) =
    4 * (i * rectangle_stride (described_shape d) + j).
Proof.
  intros ALL OCCURS.
  assert (MEMBER : forall kind, In kind [IndexMultiply; IndexAdd; ByteOffset] ->
    In (rectangle_text_site d kind) (rectangle_text_sites d)).
  { intros kind IN; unfold rectangle_text_sites; apply in_map; cbn in *; tauto. }
  pose proof (ALL (rectangle_text_site d IndexMultiply) (MEMBER _ (or_introl eq_refl)) (i,j) OCCURS) as MUL.
  pose proof (ALL (rectangle_text_site d IndexAdd) (MEMBER _ (or_intror (or_introl eq_refl))) (i,j) OCCURS) as ADD.
  pose proof (ALL (rectangle_text_site d ByteOffset) (MEMBER _ (or_intror (or_intror (or_introl eq_refl)))) (i,j) OCCURS) as PTR.
  cbn [rectangle_text_site site_holds fst snd] in MUL, ADD, PTR.
  unfold signed_fits in MUL, ADD; unfold pointer_fits in PTR.
  apply andb_true_iff in MUL as [ML MU], ADD as [AL AU], PTR as [PL PU].
  apply Z.leb_le in ML, MU, AL, AU, PL, PU.
  rewrite rect_integer_multiply, rect_integer_add; split; [apply Int.signed_repr; auto|].
  split; [apply Int.signed_repr; auto|apply Ptrofs.unsigned_repr; auto].
Qed.

Print Assumptions rectangle_text_derivation.
Print Assumptions accepted_rectangle_text_requirements.
Print Assumptions accepted_rectangle_address_injective.
Print Assumptions collected_rectangle_machine_index.
