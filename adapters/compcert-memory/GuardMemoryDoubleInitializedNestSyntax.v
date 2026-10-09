From Stdlib Require Import List Bool Arith ZArith Lia.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightSyntaxEquality ClightLoopSyntax ClightTempFrame.
From GuardMemory Require Import GuardMemoryDoubleInitializedReductionData GuardMemoryDoubleInitializedNestData
  GuardMemoryDoubleMatmulLoops GuardMemoryLongLoopControl.
Import ListNotations.
Set Implicit Arguments.

Lemma double_initialized_nest_code_fuel outers description :
  length outers<double_initialized_nest_fuel (double_initialized_nest_code outers description).
Proof.
  induction outers as [|iterator rest IH]; cbn [double_initialized_nest_code].
  - unfold double_initialized_reduction_code,memory_long_initialized_loop,memory_long_frontend_loop;
      destruct (initialized_reduction_initializer description); cbn [double_initialized_nest_fuel length]; lia.
  - unfold memory_long_initialized_loop,memory_long_frontend_loop; cbn [double_initialized_nest_fuel length]; lia.
Qed.
Lemma double_initialized_nest_with_fuel_complete outers : forall fuel p controls description,
  length outers<fuel -> double_initialized_nest_fresh controls outers ->
  checked_double_initialized_reduction p (controls++outers) (double_initialized_reduction_code description)=Some description ->
  checked_double_initialized_nest_with_fuel fuel p controls (double_initialized_nest_code outers description)=Some (outers,description).
Proof.
  induction outers as [|iterator rest IH]; intros fuel p controls description LENGTH FRESH LEAF;
    destruct fuel as [|fuel]; [cbn in LENGTH; lia| |cbn in LENGTH; lia|].
  - cbn [double_initialized_nest_code checked_double_initialized_nest_with_fuel].
    rewrite app_nil_r in LEAF; rewrite LEAF; reflexivity.
  - destruct FRESH as [DISTINCT TAIL].
    assert (NOT_FOUND : existsb (Pos.eqb iterator) controls=false).
    { destruct (existsb (Pos.eqb iterator) controls) eqn:FOUND; [|reflexivity].
      apply existsb_exists in FOUND as [key [MEMBER SAME]]; apply Pos.eqb_eq in SAME; subst; contradiction. }
    assert (CHILD : checked_double_initialized_nest_with_fuel fuel p (controls++[iterator])
      (double_initialized_nest_code rest description)=Some (rest,description)).
    { apply IH; [cbn in LENGTH; lia|exact TAIL|].
      replace ((controls++[iterator])++rest) with (controls++iterator::rest) by (rewrite <- app_assoc; reflexivity).
      exact LEAF. }
    cbn [double_initialized_nest_code]; unfold memory_long_initialized_loop,memory_long_frontend_loop.
    cbn [checked_double_initialized_nest_with_fuel checked_double_initialized_reduction
      propose_double_initialized_reduction_shape double_initialized_outer_shape].
    rewrite NOT_FOUND; cbn [negb]; rewrite CHILD.
    destruct (statement_eq _ _) as [SAME|DIFFERENT]; [reflexivity|exfalso; apply DIFFERENT; reflexivity].
Qed.
Theorem checked_double_initialized_nest_complete p controls outers description :
  double_initialized_nest_fresh controls outers ->
  checked_double_initialized_reduction p (controls++outers) (double_initialized_reduction_code description)=Some description ->
  checked_double_initialized_nest p controls (double_initialized_nest_code outers description)=Some (outers,description).
Proof.
  intros FRESH LEAF; unfold checked_double_initialized_nest; apply double_initialized_nest_with_fuel_complete;
    [apply double_initialized_nest_code_fuel|exact FRESH|exact LEAF].
Qed.

Print Assumptions double_initialized_nest_code_fuel.
Print Assumptions checked_double_initialized_nest_complete.
