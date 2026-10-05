From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightPureExpr ClightNoWrap ClightStraightLine
  ClightTempFrame ClightRegionProgress ClightFrontendRegion ClightLoopSyntax ClightCountedLoop.
From GuardInterface Require Import ClightDualLoadedUnitSyntax ClightLoadedBoundSyntax ClightStrictLoopProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition dual_repeat_reset := dual_unit_reset.
Definition dual_repeat_store out := Sassign (signed_load out) (Econst_int (Int.repr 0) type_int32s).
Definition dual_repeat_source row rows outer := loaded_bound_loop row rows outer.
Definition dual_repeat_candidate row rows column columns out := Ssequence (dual_repeat_store out)
  (Ssequence (Sset column (signed_load columns)) (Sset row (signed_load rows))).
Lemma dual_repeat_store_encode fe ge locals le memory out b ofs final :
  le ! out = Some (Vptr b ofs) -> Mem.storev Mint32 memory (Vptr b ofs) (Vint (Int.repr 0)) = Some final ->
  exec_stmt fe ge locals le memory (dual_repeat_store out) E0 le final Out_normal.
Proof.
  intros P STORE; eapply exec_Sassign with (v := Vint (Int.repr 0)) (v2 := Vint (Int.repr 0)) (bf := Full).
  - apply eval_Ederef,eval_Etempvar; exact P.
  - constructor.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|exact STORE].
Qed.
Lemma dual_repeat_store_decode fe ge locals le memory out after final :
  exec_stmt fe ge locals le memory (dual_repeat_store out) E0 after final Out_normal ->
  exists b ofs, le ! out = Some (Vptr b ofs) /\ after = le /\
    Mem.storev Mint32 memory (Vptr b ofs) (Vint (Int.repr 0)) = Some final.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (signed_load out) _ _ _ |- _ => inversion LV; subst end.
  match goal with P : eval_expr _ _ _ _ (signed_pointer_temp out) _ |- _ => apply scalar_temp_inv in P end.
  match goal with V : eval_expr _ _ _ _ (Econst_int _ _) _ |- _ => apply scalar_const_inv in V; subst end.
  match goal with CAST : sem_cast _ _ _ _ = Some _ |- _ => inversion CAST; subst end.
  match goal with STORE : assign_loc _ _ _ _ _ _ _ _ |- _ => inversion STORE; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ => inversion MODE; subst end.
  do 2 eexists; repeat split; eauto.
Qed.
Lemma dual_repeat_body_quiet out body : flatten_region body = [dual_repeat_store out] -> quiet_statement body = true.
Proof. intro FLAT; apply flatten_quiet_certificate; rewrite FLAT; constructor; [reflexivity|constructor]. Qed.
Lemma dual_repeat_outer_quiet out column columns body outer :
  flatten_region body = [dual_repeat_store out] ->
  flatten_region outer = [dual_unit_reset column;loaded_bound_loop column columns body] -> quiet_statement outer = true.
Proof.
  intros BODY OUTER; apply flatten_quiet_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
  cbn [loaded_bound_loop strict_frontend_loop quiet_statement counter_increment]; rewrite (@dual_repeat_body_quiet out body BODY); reflexivity.
Qed.
Lemma dual_repeat_outer_normal out column columns body outer :
  flatten_region body = [dual_repeat_store out] ->
  flatten_region outer = [dual_unit_reset column;loaded_bound_loop column columns body] -> normal_statement outer = true.
Proof.
  intros BODY OUTER; apply flatten_normal_certificate; rewrite OUTER; constructor; [reflexivity|constructor; [|constructor]].
  cbn [loaded_bound_loop strict_frontend_loop normal_statement quiet_statement counter_increment];
    rewrite (@dual_repeat_body_quiet out body BODY); reflexivity.
Qed.
Lemma dual_repeat_source_quiet row rows out column columns body outer :
  flatten_region body = [dual_repeat_store out] ->
  flatten_region outer = [dual_unit_reset column;loaded_bound_loop column columns body] ->
  quiet_statement (dual_repeat_source row rows outer) = true.
Proof.
  intros BODY OUTER; cbn [dual_repeat_source loaded_bound_loop strict_frontend_loop quiet_statement counter_increment];
    rewrite (@dual_repeat_outer_quiet out column columns body outer BODY OUTER); reflexivity.
Qed.
Print Assumptions dual_repeat_store_decode.
Print Assumptions dual_repeat_source_quiet.
