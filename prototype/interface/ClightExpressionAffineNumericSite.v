From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightSyntaxEquality ClightTempFootprint ClightTempFrame ClightCondition ClightPureExpr ClightRedundantSet.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestPackageGuard AffineNestMathDomain AffineNestExit.
From GuardInterface Require Import ClightSignedExpressionProgress ClightStrictLoopProgress ClightCheckPlanFrame
  ClightMaterializedCheck ClightExpressionHeaderCapture ClightLoadedAffineNumericGuard ClightAffineNestMaterialized.
Import ListNotations.
Set Implicit Arguments.

Definition expression_affine_numeric_source bound proposal :=
  strict_frontend_loop (affine_proposed_iterator proposal)
    (signed_expression_test (affine_proposed_iterator proposal) bound) (affine_proposed_body proposal).

(** This site checks the actual compound header and reuses the existing
    recursive affine numeric checker. It certifies the first guard phase;
    neither read stability nor a candidate transformation is certified here. *)
Record expression_affine_numeric_site source parameters live proposal bound := {
  expression_numeric_type : typeof bound=type_int32s;
  expression_numeric_exact : source=expression_affine_numeric_source bound proposal;
  expression_numeric_private : ~In (affine_proposed_bound proposal) (statement_temps source++live);
  expression_numeric_frameable : check_plan_frameable source=true;
  expression_numeric_package : affine_guard_package (affine_nest_source (affine_proposal_nest proposal))
    parameters (affine_proposed_bound proposal::live) proposal;
  expression_numeric_test : materialized_check;
  expression_numeric_describe : describe_materialized_check (affine_package_guard_code expression_numeric_package)
    (Etempvar (affine_proposed_result proposal) type_int32s)=Some expression_numeric_test
}.

Definition check_expression_affine_numeric_site source parameters live proposal bound :
  option (expression_affine_numeric_site source parameters live proposal bound).
Proof.
  destruct (type_eq (typeof bound) type_int32s) as [TYPE|]; [|exact None].
  destruct (statement_eq source (expression_affine_numeric_source bound proposal)) as [EXACT|]; [|exact None].
  destruct (in_dec peq (affine_proposed_bound proposal) (statement_temps source++live)) as [|PRIVATE]; [exact None|].
  destruct (Bool.bool_dec (check_plan_frameable source) true) as [FRAMEABLE|]; [|exact None].
  destruct (check_affine_guard_package (affine_nest_source (affine_proposal_nest proposal))
    parameters (affine_proposed_bound proposal::live) proposal) as [package|]; [|exact None].
  destruct (describe_materialized_check (affine_package_guard_code package)
    (Etempvar (affine_proposed_result proposal) type_int32s)) as [test|] eqn:DESCRIBE; [|exact None].
  exact (Some {| expression_numeric_type:=TYPE; expression_numeric_exact:=EXACT;
    expression_numeric_private:=PRIVATE; expression_numeric_frameable:=FRAMEABLE;
    expression_numeric_package:=package; expression_numeric_test:=test; expression_numeric_describe:=DESCRIBE |}).
Defined.

Definition expression_numeric_check_code source parameters live proposal bound
  (site : expression_affine_numeric_site source parameters live proposal bound) :=
  Ssequence (Sset (affine_proposed_bound proposal) bound) (materialized_body (expression_numeric_test site)).

Theorem expression_numeric_site_execution source parameters live proposal bound
  (site : expression_affine_numeric_site source parameters live proposal bound) fe ge locals le memory after final :
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  exists upper checked,
    exec_stmt fe ge locals le memory (expression_numeric_check_code site) E0 checked memory Out_normal /\
    temp_agree live le checked /\
    checked!(affine_proposed_bound proposal)=Some(Vint upper) /\
    checked!(affine_proposed_result proposal)=Some(Vint(if affine_package_guard_flag parameters proposal
      (Entry ge locals (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory)
      then Int.one else Int.zero)) /\
    (affine_package_guard_flag parameters proposal
      (Entry ge locals (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory)=true ->
      affine_loaded_numeric_premise parameters proposal
        (Entry ge locals (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory)) /\
    eval_expr ge locals le memory bound (Vint upper).
Proof.
  intro SOURCE.
  pose proof (expression_numeric_private site) as PRIVATE; rewrite (expression_numeric_exact site) in PRIVATE,SOURCE.
  pose proof (expression_numeric_frameable site) as FRAMEABLE; rewrite (expression_numeric_exact site) in FRAMEABLE.
  destruct (affine_loaded_numeric_body_properties (expression_numeric_package site)) as [NORMAL QUIET].
  destruct (@signed_expression_capture_receipt fe ge locals le memory (affine_proposed_iterator proposal) bound
    (affine_proposed_body proposal) (affine_proposed_bound proposal) live after final
    (expression_numeric_type site) NORMAL QUIET FRAMEABLE PRIVATE SOURCE)
    as [upper [prepared_after [CAPTURE [PREPARED [PUBLIC [RECEIPT EVAL]]]]]].
  destruct (@affine_receipted_package_guard_execution _ parameters _ proposal (expression_numeric_package site)
    fe ge locals (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory RECEIPT)
    as [checked [GUARD [FRAME [RESULT MATH]]]].
  destruct (@describe_materialized_check_exact _ _ _ (expression_numeric_describe site)) as [BODY COND].
  exists upper,checked; split.
  - unfold expression_numeric_check_code; rewrite BODY; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); eassumption.
  - split.
    + eapply temp_agree_trans; [apply temp_agree_set; intro MEMBER; apply PRIVATE,in_or_app; right; exact MEMBER|].
      eapply temp_agree_weaken; [|exact FRAME].
      unfold affine_single_materialized_ports; intros identifier MEMBER;
        apply in_or_app; right; apply in_or_app; right; cbn; auto.
    + split.
      * rewrite FRAME; [apply PTree.gss|].
        unfold affine_single_materialized_ports; apply in_or_app; right; apply in_or_app; left; cbn; auto.
      * split; [exact RESULT|split; [intro ACCEPT; split; [exact ACCEPT|apply MATH; exact ACCEPT]|exact EVAL]].
Qed.

Print Assumptions check_expression_affine_numeric_site.
Print Assumptions expression_numeric_site_execution.
