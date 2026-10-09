From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers.
From polcert.lib Require Import Linalg.
From GuardMemory Require Import GuardMemoryNaryAffineExpressions
  GuardMemoryDoubleAffineSourceAccess GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleSourceResolvedPoints GuardMemoryDoubleInitializedBounds.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Rows consume [n] followed by actual iterator coordinates, each in [0,n).
    Keeping the same n in both places preserves parameter/domain correlation.
    The profiles and checker establish mathematical bounds, not permissions. *)
Definition double_header_linear_value (line : Z*Z) count := fst line*count+snd line.
Definition double_header_row_profile (row : constraint) : (Z*Z)*(Z*Z) :=
  match fst row with
  | [] => ((0,snd row),(0,snd row))
  | parameter::iterators =>
      let '(low,high) := double_initialized_dot_bounds 1 iterators in
      ((parameter+low,snd row-low),(parameter+high,snd row-high))
  end.
Lemma double_header_dot_bounds_scaling cap coefficients :
  double_initialized_dot_bounds cap coefficients =
    let '(low,high) := double_initialized_dot_bounds 1 coefficients in
    (low*cap,high*cap).
Proof.
  induction coefficients as [|coefficient rest IH]; cbn [double_initialized_dot_bounds].
  - f_equal; ring.
  - destruct (double_initialized_dot_bounds 1 rest) as [low high] eqn:UNIT.
    rewrite IH; destruct (0<=?coefficient); cbn; f_equal; ring.
Qed.
Theorem double_header_row_profile_sound row count coordinates :
  1<=count -> Forall (fun value => 0<=value<count) coordinates ->
  double_header_linear_value (fst (double_header_row_profile row)) count <=
    memory_nary_index_value row (count::coordinates) <=
  double_header_linear_value (snd (double_header_row_profile row)) count.
Proof.
  destruct row as [coefficients bias]; destruct coefficients as [|parameter iterators];
    intros COUNT WITHIN.
  - unfold double_header_row_profile, double_header_linear_value, memory_nary_index_value;
      cbn; lia.
  - assert (RANGE : Forall (fun value => 0<=value<=count-1) coordinates).
    { apply Forall_forall; intros value MEMBER.
      apply Forall_forall with (x:=value) in WITHIN; [lia|exact MEMBER]. }
    pose proof (@double_initialized_dot_bounds_sound iterators (count-1) coordinates ltac:(lia) RANGE) as BOUNDS.
    rewrite double_header_dot_bounds_scaling in BOUNDS.
    destruct (double_initialized_dot_bounds 1 iterators) as [low high] eqn:UNIT.
    unfold double_header_row_profile, double_header_linear_value, memory_nary_index_value;
      cbn [fst snd dot_product]; rewrite UNIT; cbn [fst snd] in *; nia.
Qed.
Lemma double_header_linear_interval line count limit lower upper :
  1<=count<=limit ->
  lower<=double_header_linear_value line 1<=upper ->
  lower<=double_header_linear_value line limit<=upper ->
  lower<=double_header_linear_value line count<=upper.
Proof.
  destruct line as [slope bias]; unfold double_header_linear_value; cbn [fst snd].
  intros COUNT FIRST LAST; destruct (Z_le_dec 0 slope); nia.
Qed.
Definition double_header_row_bounds_check limit dimension row :=
  let '(low,high) := double_header_row_profile row in
  (0<=?double_header_linear_value low 1) &&
  (0<=?double_header_linear_value low limit) &&
  (double_header_linear_value high 1<?dimension) &&
  (double_header_linear_value high limit<?dimension).
Theorem double_header_row_bounds_check_sound limit dimension row count coordinates :
  double_header_row_bounds_check limit dimension row=true ->
  1<=count<=limit -> Forall (fun value => 0<=value<count) coordinates ->
  0<=memory_nary_index_value row (count::coordinates)<dimension.
Proof.
  unfold double_header_row_bounds_check.
  destruct (double_header_row_profile row) as [low high] eqn:PROFILE.
  intros CHECK COUNT WITHIN.
  apply andb_true_iff in CHECK as [CHECK HIGH_LAST].
  apply andb_true_iff in CHECK as [CHECK HIGH_FIRST].
  apply andb_true_iff in CHECK as [LOW_FIRST LOW_LAST].
  apply Z.leb_le in LOW_FIRST; apply Z.leb_le in LOW_LAST.
  apply Z.ltb_lt in HIGH_FIRST; apply Z.ltb_lt in HIGH_LAST.
  pose proof (@double_header_row_profile_sound row count coordinates ltac:(lia) WITHIN) as BOUNDS.
  rewrite PROFILE in BOUNDS; cbn [fst snd] in BOUNDS.
  destruct low as [la lb]; destruct high as [ha hb];
    unfold double_header_linear_value in *; cbn [fst snd] in *.
  destruct (Z_le_dec 0 la); destruct (Z_le_dec 0 ha); nia.
Qed.
Fixpoint double_header_footprint_check limit dimensions rows :=
  match dimensions,rows with
  | [],[] => true
  | dimension::dimensions,row::rows =>
      double_header_row_bounds_check limit dimension row && double_header_footprint_check limit dimensions rows
  | _,_ => false end.
Theorem double_header_footprint_check_sound limit dimensions rows count coordinates :
  double_header_footprint_check limit dimensions rows=true ->
  1<=count<=limit -> Forall (fun value => 0<=value<count) coordinates ->
  Forall2 (fun dimension coordinate => 0<=coordinate<dimension)
    dimensions (affine_product rows (count::coordinates)).
Proof.
  revert rows; induction dimensions as [|dimension rest IH]; intros [|row rows] CHECK COUNT WITHIN;
    cbn [double_header_footprint_check] in CHECK; try discriminate.
  - constructor.
  - apply andb_true_iff in CHECK as [ROW REST]; cbn [affine_product map]; constructor.
    + exact (@double_header_row_bounds_check_sound limit dimension row count coordinates ROW COUNT WITHIN).
    + eapply IH; eassumption.
Qed.
Definition double_header_instruction_bounds_check limit description := forallb
  (fun access => double_header_footprint_check limit (double_affine_source_dimensions access)
    (snd (double_affine_source_function access))) (double_source_instruction_accesses description).
Theorem double_header_instruction_bounds_check_sound limit description count coordinates :
  double_header_instruction_bounds_check limit description=true ->
  1<=count<=limit -> Forall (fun value => 0<=value<count) coordinates ->
  double_source_instruction_bounded description (count::coordinates).
Proof.
  intros CHECK COUNT WITHIN access MEMBER.
  unfold double_header_instruction_bounds_check in CHECK.
  apply forallb_forall with (x:=access) in CHECK; [|exact MEMBER].
  unfold double_source_access_bounded; eapply double_header_footprint_check_sound; eassumption.
Qed.

(** A proposal algorithm. The endpoint checker remains the authority, including
    when these divisions return a negative or insufficient proposed cap. *)
Definition double_header_lower_limit line :=
  if fst line<?0 then snd line/(-fst line) else Int.max_signed.
Definition double_header_upper_limit dimension line :=
  if 0<?fst line then (dimension-1-snd line)/fst line else Int.max_signed.
Definition double_header_row_limit dimension row :=
  let '(low,high) := double_header_row_profile row in
  Z.min Int.max_signed (Z.min (double_header_lower_limit low) (double_header_upper_limit dimension high)).
Fixpoint double_header_footprint_limit dimensions rows :=
  match dimensions,rows with
  | dimension::dimensions,row::rows =>
      Z.min (double_header_row_limit dimension row) (double_header_footprint_limit dimensions rows)
  | _,_ => Int.max_signed end.
Definition double_header_instruction_limit description := fold_right Z.min Int.max_signed
  (map (fun access => double_header_footprint_limit (double_affine_source_dimensions access)
    (snd (double_affine_source_function access))) (double_source_instruction_accesses description)).
Definition double_header_entry_bounds_check limit description :=
  (0<?limit) && (limit<=?Int.max_signed) && double_header_instruction_bounds_check limit description.

Example double_header_reverse_index_profile :
  double_header_row_profile ([1;0;-1],2)=((0,3),(1,2)).
Proof. reflexivity. Qed.
Example double_header_reverse_index_limit :
  double_header_row_limit 101 ([1;0;-1],2)=98.
Proof. reflexivity. Qed.
Example double_header_reverse_index_checked :
  double_header_row_bounds_check 98 101 ([1;0;-1],2)=true /\
  double_header_row_bounds_check 99 101 ([1;0;-1],2)=false.
Proof. split; reflexivity. Qed.

Print Assumptions double_header_dot_bounds_scaling.
Print Assumptions double_header_row_profile_sound.
Print Assumptions double_header_linear_interval.
Print Assumptions double_header_row_bounds_check_sound.
Print Assumptions double_header_footprint_check_sound.
Print Assumptions double_header_instruction_bounds_check_sound.
Print Assumptions double_header_reverse_index_profile.
Print Assumptions double_header_reverse_index_limit.
Print Assumptions double_header_reverse_index_checked.
