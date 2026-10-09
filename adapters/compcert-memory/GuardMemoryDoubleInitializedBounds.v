From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightGlobalScope ClightRegionProgress.
From GuardMemory Require Import GuardMemoryDoubleAffineSourceAccess GuardMemoryDoubleSourceInstruction
  GuardMemoryDoubleSourceResolvedPoints GuardMemoryDoubleInitializedReductionData
  GuardMemoryDoubleInitializedReductionSource GuardMemoryDoubleInitializedNestData
  GuardMemoryDoubleInitializedNestSyntax GuardMemoryDoubleInitializedNestSource
  GuardMemoryDoubleInitializedRawNest.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Checked affine footprints for the source family's common captured bound.
    The returned range condition is sufficient; no allocation/read permission
    follows from these purely mathematical access bounds. *)
Fixpoint double_initialized_dot_bounds cap coefficients : Z*Z :=
  match coefficients with
  | [] => (0,0)
  | coefficient::rest =>
    let '(low,high) := double_initialized_dot_bounds cap rest in
    if 0<=?coefficient then (low,high+coefficient*cap)
    else (low+coefficient*cap,high)
  end.
Lemma double_initialized_dot_bounds_sound coefficients : forall cap parameters,
  0<=cap -> Forall (fun value => 0<=value<=cap) parameters ->
  fst (double_initialized_dot_bounds cap coefficients)<=dot_product coefficients parameters<=
    snd (double_initialized_dot_bounds cap coefficients).
Proof.
  induction coefficients as [|coefficient rest IH]; intros cap parameters CAP WITHIN.
  - rewrite dot_product_nil_left; cbn [double_initialized_dot_bounds fst snd]; lia.
  - destruct parameters as [|value tail].
    + pose proof (IH cap [] CAP ltac:(constructor)) as REST.
      rewrite dot_product_nil_right in REST.
      cbn [dot_product] in REST; cbn [double_initialized_dot_bounds dot_product].
      destruct (double_initialized_dot_bounds cap rest) as [low high]; cbn [fst snd] in REST.
      destruct (0<=?coefficient) eqn:SIGN; cbn [fst snd];
        [apply Z.leb_le in SIGN|apply Z.leb_gt in SIGN]; nia.
    + inversion WITHIN; subst.
      pose proof (IH cap tail CAP ltac:(assumption)) as REST.
      cbn [double_initialized_dot_bounds dot_product].
      destruct (double_initialized_dot_bounds cap rest) as [low high]; cbn [fst snd] in REST.
      destruct (0<=?coefficient) eqn:SIGN; cbn [fst snd];
        [apply Z.leb_le in SIGN|apply Z.leb_gt in SIGN]; nia.
Qed.
Definition double_initialized_row_bounds cap row :=
  let '(coefficients,bias) := row in
  let '(low,high) := double_initialized_dot_bounds cap coefficients in (low+bias,high+bias).
Lemma double_initialized_row_bounds_sound cap row parameters :
  0<=cap -> Forall (fun value => 0<=value<=cap) parameters ->
  fst (double_initialized_row_bounds cap row)<=dot_product (fst row) parameters+snd row<=
    snd (double_initialized_row_bounds cap row).
Proof.
  destruct row as [coefficients bias]; intros CAP WITHIN.
  pose proof (@double_initialized_dot_bounds_sound coefficients cap parameters CAP WITHIN) as BOUNDS.
  unfold double_initialized_row_bounds; destruct (double_initialized_dot_bounds cap coefficients) as [low high].
  cbn [fst snd] in *; lia.
Qed.
Fixpoint double_initialized_footprint_check cap dimensions rows :=
  match dimensions,rows with
  | [],[] => true
  | dimension::dimensions,row::rows =>
    let '(low,high) := double_initialized_row_bounds cap row in
    (0<=?low) && (high<?dimension) && double_initialized_footprint_check cap dimensions rows
  | _,_ => false end.
Theorem double_initialized_footprint_check_sound dimensions : forall cap rows parameters,
  0<=cap -> double_initialized_footprint_check cap dimensions rows=true ->
  Forall (fun value => 0<=value<=cap) parameters ->
  Forall2 (fun dimension coordinate => 0<=coordinate<dimension) dimensions (affine_product rows parameters).
Proof.
  induction dimensions as [|dimension dimensions IH]; intros cap rows parameters CAP CHECK WITHIN;
    destruct rows as [|row rows]; cbn [double_initialized_footprint_check affine_product map] in CHECK |- *;
    try discriminate; [constructor|].
  pose proof (@double_initialized_row_bounds_sound cap row parameters CAP WITHIN) as VALUE.
  destruct (double_initialized_row_bounds cap row) as [low high] eqn:RANGE; cbn [fst snd] in VALUE.
  apply andb_true_iff in CHECK as [HEAD TAIL]; apply andb_true_iff in HEAD as [LOW HIGH].
  apply Z.leb_le in LOW; apply Z.ltb_lt in HIGH; constructor;
    [lia|exact (@IH cap rows parameters CAP TAIL WITHIN)].
Qed.
Definition double_initialized_instruction_bounds_check cap description := forallb
  (fun access => double_initialized_footprint_check cap (double_affine_source_dimensions access)
    (snd (double_affine_source_function access))) (double_source_instruction_accesses description).
Lemma double_initialized_instruction_bounds_check_sound cap description parameters :
  0<=cap -> double_initialized_instruction_bounds_check cap description=true ->
  Forall (fun value => 0<=value<=cap) parameters -> double_source_instruction_bounded description parameters.
Proof.
  intros CAP CHECK WITHIN access MEMBER; unfold double_initialized_instruction_bounds_check in CHECK.
  apply forallb_forall with (x:=access) in CHECK; [|exact MEMBER].
  unfold double_source_access_bounded; eapply double_initialized_footprint_check_sound; eassumption.
Qed.
Definition double_initialized_entry_bounds_check limit description :=
  (0<?limit) && (limit<=?Int.max_signed) &&
  double_initialized_instruction_bounds_check (limit-1) (initialized_reduction_initial_instruction description) &&
  double_initialized_instruction_bounds_check (limit-1) (initialized_reduction_body_instruction description).
Theorem double_initialized_entry_bounds_check_ready p source outers description limit ge locals count :
  checked_double_initialized_raw_nest p [] source=Some (outers,description) ->
  double_initialized_entry_bounds_check limit description=true ->
  preserving_globals (globalenv p) ge -> locals_avoid (double_initialized_reduction_globals description) locals ->
  Z.of_nat count<=limit -> double_initialized_nest_ready description ge count [] (length outers).
Proof.
  intros CHECK BOUNDS GLOBAL LOCAL UPPER.
  unfold double_initialized_entry_bounds_check in BOUNDS.
  apply andb_true_iff in BOUNDS as [BOUNDS BODY].
  apply andb_true_iff in BOUNDS as [BOUNDS INITIAL].
  apply andb_true_iff in BOUNDS as [POSITIVE MACHINE]; apply Z.ltb_lt in POSITIVE.
  destruct (@checked_double_initialized_raw_nest_sound p [] source outers description CHECK) as [RAW [CANONICAL EQUIV]].
  destruct (@checked_double_initialized_nest_sound p [] (double_initialized_nest_code outers description)
    outers description CANONICAL) as [CODE [LEAF FRESH]].
  destruct (@checked_double_initialized_reduction_sound p ([]++outers) (double_initialized_reduction_code description)
    description LEAF) as [_ [IC [BC STATIC]]].
  destruct (@double_initialized_reduction_static_sound p ([]++outers) description STATIC)
    as [_ [_ [_ [_ [IL BL]]]]].
  destruct (@double_initialized_reduction_scope description locals LOCAL) as [LI LB].
  intros coordinates LENGTH WITHIN; cbn [app].
  assert (RANGE : Forall (fun value => 0<=value<=limit-1) coordinates).
  { apply Forall_forall; intros value MEMBER; apply Forall_forall with (x:=value) in WITHIN; [lia|exact MEMBER]. }
  split.
  - eapply checked_double_source_instruction_resolved_from_bounds;
      [exact IC|exact IL|exact GLOBAL|exact LI|].
    exact (@double_initialized_instruction_bounds_check_sound (limit-1)
      (initialized_reduction_initial_instruction description) coordinates ltac:(lia) INITIAL RANGE).
  - intros value VALUE; eapply checked_double_source_instruction_resolved_from_bounds;
      [exact BC|exact BL|exact GLOBAL|exact LB|].
    apply (@double_initialized_instruction_bounds_check_sound (limit-1)
      (initialized_reduction_body_instruction description) (coordinates++[value]) ltac:(lia) BODY).
    apply Forall_app; split; [exact RANGE|constructor; [lia|constructor]].
Qed.

Print Assumptions double_initialized_dot_bounds_sound.
Print Assumptions double_initialized_footprint_check_sound.
Print Assumptions double_initialized_instruction_bounds_check_sound.
Print Assumptions double_initialized_entry_bounds_check_ready.
