From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestValuation AffineNestMathDomain
  AffineNestScanModel AffineNestScanSyntax AffineNestScanExecution AffineNestScanNamespace.
Import ListNotations.
Set Implicit Arguments.

Theorem affine_scan_named_execution nest parameters live controls flag
  (names:affine_scan_namespace nest parameters live controls flag)
  fe ge locals memory original temps valuation lower lower_code accepted test bounds layout leaf :
  affine_nest_bound_dependencies [] parameters nest -> incl parameters live ->
  affine_math_domain bounds layout nest valuation lower ->
  affine_word_view parameters valuation original -> temp_agree live original temps ->
  temps!flag=Some(memory_boolean_word accepted) ->
  eval_expr ge locals temps memory lower_code(Vint(Int.repr lower)) ->
  (forall point current good protected,
    affine_scan_point nest valuation lower point ->
    affine_scan_word_view(affine_nest_iterators nest++parameters)(affine_scan_values nest controls) point current ->
    temp_agree live original current -> current!flag=Some(memory_boolean_word good) -> ~In flag protected ->
    incl protected(map controls(affine_nest_controls nest)++live) ->
    exists after, exec_stmt fe ge locals current memory leaf E0 after memory Out_normal /\
      temp_agree protected current after /\ after!flag=Some(memory_boolean_word(good&&test point))) ->
  exists after,
    exec_stmt fe ge locals temps memory(affine_scan_statement nest controls(affine_scan_values nest controls) lower_code leaf)
      E0 after memory Out_normal /\ temp_agree live temps after /\
    after!flag=Some(memory_boolean_word(accepted&&affine_scan_result nest valuation lower test)).
Proof.
  intros DEPENDENCIES PARAMETERS DOMAIN WORDS FRAME FLAG LOWER BODY.
  eapply affine_scan_execution with(prefix:=[])(parameters:=parameters)(public:=live)(base:=original)
    (test:=test)(bounds:=bounds)(layout:=layout); try eassumption.
  - exact(affine_scan_names_unique names).
  - intros identifier MEMBER; apply affine_scan_values_iterator; exact MEMBER.
  - intros identifier MEMBER; destruct(affine_scan_names_private names identifier MEMBER) as [FRESH NOT_FLAG].
    split; [|exact NOT_FLAG]; intro BAD; apply FRESH,in_or_app; auto.
  - intro BAD; apply(affine_scan_names_flag_private names),in_or_app; auto.
  - apply incl_refl.
  - cbn; intros identifier MEMBER; apply in_map_iff in MEMBER as [parameter [<- MEMBER]].
    rewrite(affine_scan_names_parameters names parameter MEMBER); apply PARAMETERS; exact MEMBER.
  - cbn; intros identifier MEMBER; rewrite(affine_scan_names_parameters names identifier MEMBER).
    rewrite FRAME by(apply PARAMETERS; exact MEMBER); apply WORDS; exact MEMBER.
Qed.
Print Assumptions affine_scan_named_execution.
