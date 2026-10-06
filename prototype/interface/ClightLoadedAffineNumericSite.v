From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightSyntaxEquality ClightTempFootprint ClightTempFrame ClightCondition.
From GuardAffineNest Require Import AffineNestSyntax AffineNestGuardPackage AffineNestPackageGuard AffineNestMathDomain AffineNestExit.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightCheckPlanFrame ClightMaterializedCheck
  ClightLoadedAffineFirstPath ClightLoadedAffineNumericGuard ClightAffineNestMaterialized.
Import ListNotations.
Set Implicit Arguments.

(** This checked site binds the actual loaded source to a cached mathematical
    package. It certifies numeric checking only, not a candidate rewrite. *)
Record loaded_affine_numeric_site source parameters live proposal pointer := {
  loaded_numeric_exact : source=affine_loaded_numeric_source pointer proposal;
  loaded_numeric_private : ~In (affine_proposed_bound proposal) (statement_temps source++live);
  loaded_numeric_frameable : check_plan_frameable source=true;
  loaded_numeric_package : affine_guard_package (affine_nest_source (affine_proposal_nest proposal))
    parameters (affine_proposed_bound proposal::live) proposal;
  loaded_numeric_test : materialized_check;
  loaded_numeric_describe : describe_materialized_check (affine_package_guard_code loaded_numeric_package)
    (Etempvar (affine_proposed_result proposal) type_int32s)=Some loaded_numeric_test
}.

Definition check_loaded_affine_numeric_site source parameters live proposal pointer :
  option (loaded_affine_numeric_site source parameters live proposal pointer).
Proof.
  destruct (statement_eq source (affine_loaded_numeric_source pointer proposal)) as [EXACT|]; [|exact None].
  destruct (in_dec peq (affine_proposed_bound proposal) (statement_temps source++live)) as [|PRIVATE]; [exact None|].
  destruct (Bool.bool_dec (check_plan_frameable source) true) as [FRAMEABLE|]; [|exact None].
  destruct (check_affine_guard_package (affine_nest_source (affine_proposal_nest proposal))
    parameters (affine_proposed_bound proposal::live) proposal) as [package|]; [|exact None].
  destruct (describe_materialized_check (affine_package_guard_code package)
    (Etempvar (affine_proposed_result proposal) type_int32s)) as [test|] eqn:DESCRIBE; [|exact None].
  exact (Some {| loaded_numeric_exact:=EXACT; loaded_numeric_private:=PRIVATE;
    loaded_numeric_frameable:=FRAMEABLE; loaded_numeric_package:=package;
    loaded_numeric_test:=test; loaded_numeric_describe:=DESCRIBE |}).
Defined.

Definition loaded_numeric_check_code source parameters live proposal pointer
  (site : loaded_affine_numeric_site source parameters live proposal pointer) :=
  Ssequence (Sset (affine_proposed_bound proposal) (signed_load pointer))
    (materialized_body (loaded_numeric_test site)).

Theorem loaded_numeric_site_execution source parameters live proposal pointer
  (site : loaded_affine_numeric_site source parameters live proposal pointer) fe ge locals le memory after final :
  exec_stmt fe ge locals le memory source E0 after final Out_normal ->
  exists upper checked,
    exec_stmt fe ge locals le memory (loaded_numeric_check_code site) E0 checked memory Out_normal /\
    temp_agree live le checked /\
    checked!(affine_proposed_bound proposal)=Some(Vint upper) /\
    checked!(affine_proposed_result proposal)=Some(Vint(if affine_package_guard_flag parameters proposal
      (Entry ge locals (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory)
      then Int.one else Int.zero)) /\
    (affine_package_guard_flag parameters proposal
      (Entry ge locals (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory)=true ->
      affine_loaded_numeric_premise parameters proposal
        (Entry ge locals (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory)).
Proof.
  intro SOURCE.
  pose proof (loaded_numeric_private site) as PRIVATE; rewrite (loaded_numeric_exact site) in PRIVATE,SOURCE.
  pose proof (loaded_numeric_frameable site) as FRAMEABLE; rewrite (loaded_numeric_exact site) in FRAMEABLE.
  destruct (affine_loaded_numeric_body_properties (loaded_numeric_package site)) as [NORMAL QUIET].
  destruct (@loaded_affine_capture_receipt fe ge locals le memory (affine_proposed_iterator proposal) pointer
    (affine_proposed_body proposal) (affine_proposed_bound proposal) live after final NORMAL QUIET FRAMEABLE PRIVATE SOURCE)
    as [upper [prepared_after [CAPTURE [PREPARED [PUBLIC RECEIPT]]]]].
  destruct (@affine_receipted_package_guard_execution _ parameters _ proposal (loaded_numeric_package site)
    fe ge locals (PTree.set (affine_proposed_bound proposal) (Vint upper) le) memory RECEIPT)
    as [checked [GUARD [FRAME [RESULT MATH]]]].
  destruct (@describe_materialized_check_exact _ _ _ (loaded_numeric_describe site)) as [BODY COND].
  exists upper,checked; split.
  - unfold loaded_numeric_check_code; rewrite BODY; eapply exec_Sseq_1 with (t1:=E0) (t2:=E0); eassumption.
  - split.
    + eapply temp_agree_trans; [apply temp_agree_set; intro MEMBER; apply PRIVATE,in_or_app; right; exact MEMBER|].
      eapply temp_agree_weaken; [|exact FRAME].
      unfold affine_single_materialized_ports; intros identifier MEMBER;
        apply in_or_app; right; apply in_or_app; right; cbn; auto.
    + split.
      * rewrite FRAME; [apply PTree.gss|].
        unfold affine_single_materialized_ports; apply in_or_app; right; apply in_or_app; left; cbn; auto.
      * split; [exact RESULT|intro ACCEPT; split; [exact ACCEPT|apply MATH; exact ACCEPT]].
Qed.

Print Assumptions check_loaded_affine_numeric_site.
Print Assumptions loaded_numeric_site_execution.
