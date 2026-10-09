From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
From GuardMemory Require Import GuardMemoryNaryAffineExpressions GuardMemoryDoubleAffineSourceAccess
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceResolvedPoints.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Independent axis caps. These receipts describe mathematical footprints;
    they provide neither allocation/permission nor a license for header reads. *)
Fixpoint double_rectangular_dot_bounds coefficients caps : option (Z*Z) :=
  match coefficients,caps with
  | [],_ => Some (0,0)
  | coefficient::coefficients,cap::caps =>
      if 0<?cap then match double_rectangular_dot_bounds coefficients caps with
      | Some (low,high) => if 0<=?coefficient then Some (low,high+coefficient*(cap-1))
          else Some (low+coefficient*(cap-1),high)
      | None=>None end else None
  | _,_=>None end.
Theorem double_rectangular_dot_bounds_sound coefficients : forall caps coordinates low high,
  double_rectangular_dot_bounds coefficients caps=Some (low,high) ->
  Forall2 (fun cap coordinate => 0<=coordinate<cap) caps coordinates ->
  low<=dot_product coefficients coordinates<=high.
Proof.
  induction coefficients as [|coefficient coefficients IH]; intros caps coordinates low high CHECK BOX.
  - cbn [double_rectangular_dot_bounds] in CHECK; inversion CHECK; subst low high.
    rewrite dot_product_nil_left; lia.
  - destruct caps as [|cap caps]; cbn [double_rectangular_dot_bounds] in CHECK; [discriminate|].
    destruct (0<?cap) eqn:POSITIVE; [apply Z.ltb_lt in POSITIVE|discriminate].
    destruct (double_rectangular_dot_bounds coefficients caps) as [[tail_low tail_high]|] eqn:TAIL; [|discriminate].
    inversion BOX as [|cap' coordinate caps' coordinates' RANGE REST]; subst cap' caps' coordinates.
    pose proof (@IH caps coordinates' tail_low tail_high TAIL REST) as BOUNDS.
    destruct (0<=?coefficient) eqn:SIGN; inversion CHECK; subst low high;
      cbn [dot_product]; [apply Z.leb_le in SIGN|apply Z.leb_gt in SIGN]; nia.
Qed.
Definition double_rectangular_row_bounds caps row :=
  match double_rectangular_dot_bounds (fst row) caps with
  | Some (low,high) => Some (low+snd row,high+snd row)
  | None=>None end.
Theorem double_rectangular_row_bounds_sound caps row coordinates low high :
  double_rectangular_row_bounds caps row=Some (low,high) ->
  Forall2 (fun cap coordinate => 0<=coordinate<cap) caps coordinates ->
  low<=memory_nary_index_value row coordinates<=high.
Proof.
  unfold double_rectangular_row_bounds; destruct (double_rectangular_dot_bounds (fst row) caps)
    as [[tail_low tail_high]|] eqn:TAIL; [|discriminate].
  intros CHECK BOX; inversion CHECK; subst low high.
  pose proof (@double_rectangular_dot_bounds_sound (fst row) caps coordinates tail_low tail_high TAIL BOX) as BOUNDS.
  unfold memory_nary_index_value; lia.
Qed.
Fixpoint double_rectangular_footprint_check caps dimensions rows :=
  match dimensions,rows with
  | [],[]=>true
  | dimension::dimensions,row::rows => match double_rectangular_row_bounds caps row with
    | Some (low,high) => (0<=?low) && (high<?dimension) && double_rectangular_footprint_check caps dimensions rows
    | None=>false end
  | _,_=>false end.
Theorem double_rectangular_footprint_check_sound dimensions : forall caps rows coordinates,
  double_rectangular_footprint_check caps dimensions rows=true ->
  Forall2 (fun cap coordinate => 0<=coordinate<cap) caps coordinates ->
  Forall2 (fun dimension coordinate => 0<=coordinate<dimension) dimensions (affine_product rows coordinates).
Proof.
  induction dimensions as [|dimension dimensions IH]; intros caps [|row rows] coordinates CHECK BOX;
    cbn [double_rectangular_footprint_check] in CHECK; try discriminate; [constructor|].
  destruct (double_rectangular_row_bounds caps row) as [[low high]|] eqn:ROW; [|discriminate].
  apply andb_true_iff in CHECK as [HEAD TAIL]; apply andb_true_iff in HEAD as [LOW HIGH].
  apply Z.leb_le in LOW; apply Z.ltb_lt in HIGH.
  pose proof (@double_rectangular_row_bounds_sound caps row coordinates low high ROW BOX) as VALUE.
  cbn [affine_product map]; constructor; [exact ltac:(unfold memory_nary_index_value in VALUE; lia)|].
  eapply IH; eassumption.
Qed.
Definition double_rectangular_instruction_bounds_check caps description := forallb
  (fun access => double_rectangular_footprint_check caps (double_affine_source_dimensions access)
    (snd (double_affine_source_function access))) (double_source_instruction_accesses description).
Theorem double_rectangular_instruction_bounds_check_sound caps description coordinates :
  double_rectangular_instruction_bounds_check caps description=true ->
  Forall2 (fun cap coordinate => 0<=coordinate<cap) caps coordinates ->
  double_source_instruction_bounded description coordinates.
Proof.
  intros CHECK BOX access MEMBER; unfold double_rectangular_instruction_bounds_check in CHECK.
  apply forallb_forall with (x:=access) in CHECK; [|exact MEMBER].
  unfold double_source_access_bounded; eapply double_rectangular_footprint_check_sound; eassumption.
Qed.
Theorem double_rectangular_counts_within_caps caps counts coordinates :
  Forall2 (fun cap count => Z.of_nat count<=cap) caps counts ->
  Forall2 (fun count coordinate => 0<=coordinate<Z.of_nat count) counts coordinates ->
  Forall2 (fun cap coordinate => 0<=coordinate<cap) caps coordinates.
Proof.
  intro LIMITS; revert coordinates; induction LIMITS; intros coordinates RANGES.
  - inversion RANGES; constructor.
  - inversion RANGES; subst; constructor; [lia|apply IHLIMITS; assumption].
Qed.

Print Assumptions double_rectangular_dot_bounds_sound.
Print Assumptions double_rectangular_row_bounds_sound.
Print Assumptions double_rectangular_footprint_check_sound.
Print Assumptions double_rectangular_instruction_bounds_check_sound.
Print Assumptions double_rectangular_counts_within_caps.
