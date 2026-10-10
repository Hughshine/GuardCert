From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg.
From GuardMemory Require Import GuardMemoryNaryAffineExpressions GuardMemoryDoubleAffineSourceAccess
  GuardMemoryDoubleSourceInstruction GuardMemoryDoubleSourceResolvedPoints.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Signed half-open boxes describe source coordinates, including nonzero
    starts and stencil offsets. They are footprint facts, not Mem permissions. *)
Definition double_affine_box_contains box coordinates :=
  Forall2 (fun interval coordinate => fst interval<=coordinate<snd interval) box coordinates.
Fixpoint double_affine_box_dot_bounds coefficients box : option (Z*Z) := match coefficients,box with
  | [],_=>Some (0,0)
  | coefficient::coefficients,(lower,upper)::box=>
      if lower<?upper then match double_affine_box_dot_bounds coefficients box with
      | Some (low,high)=>if 0<=?coefficient then Some (coefficient*lower+low,coefficient*(upper-1)+high)
          else Some (coefficient*(upper-1)+low,coefficient*lower+high)
      | None=>None end else None
  | _,_=>None end.
Theorem double_affine_box_dot_bounds_sound coefficients : forall box coordinates low high,
  double_affine_box_dot_bounds coefficients box=Some (low,high) -> double_affine_box_contains box coordinates ->
  low<=dot_product coefficients coordinates<=high.
Proof.
  induction coefficients as [|coefficient coefficients IH]; intros box coordinates low high CHECK BOX.
  - inversion CHECK; subst low high; rewrite dot_product_nil_left; lia.
  - destruct box as [|[lower upper] box]; cbn [double_affine_box_dot_bounds] in CHECK; [discriminate|].
    destruct (lower<?upper) eqn:NONEMPTY; [apply Z.ltb_lt in NONEMPTY|discriminate].
    destruct (double_affine_box_dot_bounds coefficients box) as [[tail_low tail_high]|] eqn:TAIL; [|discriminate].
    inversion BOX as [|interval coordinate rest coordinates' RANGE REMAINING]; subst interval rest coordinates.
    cbn [fst snd] in RANGE; pose proof (@IH box coordinates' tail_low tail_high TAIL REMAINING) as BOUNDS.
    destruct (0<=?coefficient) eqn:SIGN; inversion CHECK; subst low high; cbn [dot_product];
      [apply Z.leb_le in SIGN|apply Z.leb_gt in SIGN]; nia.
Qed.
Definition double_affine_box_row_bounds box row := match double_affine_box_dot_bounds (fst row) box with
  | Some (low,high)=>Some (low+snd row,high+snd row) | None=>None end.
Theorem double_affine_box_row_bounds_sound box row coordinates low high :
  double_affine_box_row_bounds box row=Some (low,high) -> double_affine_box_contains box coordinates ->
  low<=memory_nary_index_value row coordinates<=high.
Proof.
  unfold double_affine_box_row_bounds; destruct (double_affine_box_dot_bounds (fst row) box)
    as [[tail_low tail_high]|] eqn:TAIL; [|discriminate].
  intros CHECK BOX; inversion CHECK; subst low high.
  pose proof (@double_affine_box_dot_bounds_sound (fst row) box coordinates tail_low tail_high TAIL BOX) as BOUNDS.
  unfold memory_nary_index_value; lia.
Qed.
Fixpoint double_affine_box_footprint_check box dimensions rows := match dimensions,rows with
  | [],[]=>true
  | dimension::dimensions,row::rows=>match double_affine_box_row_bounds box row with
      | Some (low,high)=>(0<=?low)&&(high<?dimension)&&double_affine_box_footprint_check box dimensions rows
      | None=>false end
  | _,_=>false end.
Theorem double_affine_box_footprint_check_sound dimensions : forall box rows coordinates,
  double_affine_box_footprint_check box dimensions rows=true -> double_affine_box_contains box coordinates ->
  Forall2 (fun dimension coordinate => 0<=coordinate<dimension) dimensions (affine_product rows coordinates).
Proof.
  induction dimensions as [|dimension dimensions IH]; intros box [|row rows] coordinates CHECK BOX;
    cbn [double_affine_box_footprint_check] in CHECK; try discriminate; [constructor|].
  destruct (double_affine_box_row_bounds box row) as [[low high]|] eqn:ROW; [|discriminate].
  apply andb_true_iff in CHECK as [HEAD TAIL]; apply andb_true_iff in HEAD as [LOW HIGH].
  apply Z.leb_le in LOW; apply Z.ltb_lt in HIGH.
  pose proof (@double_affine_box_row_bounds_sound box row coordinates low high ROW BOX) as VALUE.
  cbn [affine_product map]; constructor; [unfold memory_nary_index_value in VALUE; lia|eapply IH; eassumption].
Qed.
Definition double_affine_box_instruction_check box description := forallb
  (fun access=>double_affine_box_footprint_check box (double_affine_source_dimensions access)
    (snd (double_affine_source_function access))) (double_source_instruction_accesses description).
Theorem double_affine_box_instruction_check_sound box description coordinates :
  double_affine_box_instruction_check box description=true -> double_affine_box_contains box coordinates ->
  double_source_instruction_bounded description coordinates.
Proof.
  intros CHECK BOX access MEMBER; unfold double_affine_box_instruction_check in CHECK.
  apply forallb_forall with (x:=access) in CHECK; [|exact MEMBER].
  unfold double_source_access_bounded; eapply double_affine_box_footprint_check_sound; eassumption.
Qed.

Print Assumptions double_affine_box_dot_bounds_sound.
Print Assumptions double_affine_box_row_bounds_sound.
Print Assumptions double_affine_box_footprint_check_sound.
Print Assumptions double_affine_box_instruction_check_sound.
