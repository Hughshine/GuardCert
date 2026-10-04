From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep Ctypes.
From Guard Require Import ClightCondition ClightNoWrap ClightRedundantSet ClightTempFrame.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstDomain AffineNestGuardDomain
  AffineNestProbeRenaming AffineNestProbe AffineNestProbeStage AffineNestProbeInitialize AffineNestInitializedProbeFrame
  AffineNestNumericGuard AffineNestNumericExecution.
Import ListNotations.
Set Implicit Arguments.

Definition affine_domain_guard_code iterator bound expression body child ranges parameters floor cap rename result :=
  Ssequence (Ssequence(affine_root_probe_initialize iterator bound rename)
    (affine_first_probe(AffineSourceAxis iterator bound expression body child) rename result))
    (Sifthenelse(Etempvar result type_int32s)
      (affine_numeric_guard_statement ranges parameters iterator floor cap result) Sskip).
Definition affine_domain_guard_flag nest ranges parameters iterator floor cap state :=
  affine_first_path_flag nest(entry_temps state) && affine_numeric_guard_flag ranges parameters iterator floor cap state.

Lemma affine_probe_result_test result (flag : bool) ge locals temps memory :
  temps!result=Some(Vint(if flag then Int.one else Int.zero)) ->
  expression_test(Etempvar result type_int32s)(Entry ge locals temps memory) flag.
Proof.
  intro WORD; exists(Vint(if flag then Int.one else Int.zero)); split; [constructor; exact WORD|destruct flag; reflexivity].
Qed.

Theorem affine_domain_guard_execution iterator bound expression body child ranges parameters floor cap live registers rename result
  fe ge locals temps memory :
  affine_nest_bound_dependencies [] parameters(AffineSourceAxis iterator bound expression body child) ->
  affine_probe_stage_coverage registers(AffineSourceAxis iterator bound expression body child) [] parameters ->
  affine_rename_injective registers rename -> rename iterator<>rename bound ->
  ~In result(parameters++[iterator;bound]++live) ->
  (forall identifier, In identifier(affine_nest_controls(AffineSourceAxis iterator bound expression body child)) ->
    ~In(rename identifier)(parameters++[iterator;bound]++live)) ->
  (forall identifier, In identifier parameters -> identifier<>iterator -> identifier<>bound -> rename identifier=identifier) ->
  affine_first_header_domain(AffineSourceAxis iterator bound expression body child) temps ->
  (affine_first_path_flag(AffineSourceAxis iterator bound expression body child) temps=true ->
    Forall(fun identifier => register_domain identifier(Entry ge locals temps memory)) parameters) ->
  exists after,
    exec_stmt fe ge locals temps memory
      (affine_domain_guard_code iterator bound expression body child ranges parameters floor cap rename result) E0 after memory Out_normal /\
    temp_agree(parameters++[iterator;bound]++live) temps after /\
    after!result=Some(Vint(if affine_domain_guard_flag(AffineSourceAxis iterator bound expression body child)
      ranges parameters iterator floor cap(Entry ge locals temps memory) then Int.one else Int.zero)).
Proof.
  intros DEPENDENCIES COVERAGE UNIQUE DISTINCT RESULT_PRIVATE PRIVATE PARAMETERS DOMAIN PARAMETER_DOMAINS.
  assert (ITERATOR_PRIVATE:~In(rename iterator)(parameters++[iterator;bound])).
  { intro MEMBER; apply(PRIVATE iterator); [cbn [affine_nest_controls List.In]; auto|].
    apply in_app_or in MEMBER; destruct MEMBER as [MEMBER|MEMBER]; [apply in_or_app; auto|apply in_or_app; right; apply in_or_app; auto]. }
  assert (BOUND_PRIVATE:~In(rename bound)(parameters++[iterator;bound])).
  { intro MEMBER; apply(PRIVATE bound); [cbn [affine_nest_controls List.In]; auto|].
    apply in_app_or in MEMBER; destruct MEMBER as [MEMBER|MEMBER]; [apply in_or_app; auto|apply in_or_app; right; apply in_or_app; auto]. }
  destruct(@affine_initialized_first_probe_execution iterator bound expression body child fe ge locals parameters registers rename result temps memory
    DEPENDENCIES COVERAGE UNIQUE DISTINCT ITERATOR_PRIVATE BOUND_PRIVATE PARAMETERS DOMAIN) as [probed [PROBE PROBED]].
  pose proof(@affine_initialized_probe_public_frame iterator bound expression body child fe ge locals rename result
    (parameters++[iterator;bound]++live) temps memory probed memory RESULT_PRIVATE PRIVATE PROBE) as FRAME.
  pose proof(@affine_probe_result_test result _ ge locals probed memory PROBED) as TEST.
  destruct TEST as [test_value [EVAL BOOL]].
  destruct(affine_first_path_flag(AffineSourceAxis iterator bound expression body child) temps) eqn:ACTIVE.
  - assert (PARAMETER_DOMAIN:Forall(fun identifier=>register_domain identifier(Entry ge locals probed memory)) parameters).
    { apply affine_register_domains_transport with(before:=temps); [apply PARAMETER_DOMAINS; reflexivity|].
      intros identifier MEMBER; apply FRAME,in_or_app; auto. }
    assert (ITERATOR_DOMAIN:register_domain iterator(Entry ge locals probed memory)).
    { destruct DOMAIN as [[word WORD] REST]; exists word; cbn [entry_temps]; rewrite FRAME;
        [exact WORD|apply in_or_app; right; cbn; auto]. }
    pose proof(@affine_numeric_guard_execution ranges parameters iterator floor cap result fe ge locals probed memory PARAMETER_DOMAIN ITERATOR_DOMAIN) as NUMERIC.
    pose proof(@affine_numeric_guard_flag_frame ranges parameters iterator floor cap ge locals temps probed memory
      ltac:(intros identifier MEMBER; apply FRAME; repeat rewrite in_app_iff in *; cbn [List.In] in *; tauto)) as FLAG.
    exists(PTree.set result(Vint(if affine_numeric_guard_flag ranges parameters iterator floor cap(Entry ge locals probed memory)
      then Int.one else Int.zero)) probed).
    split.
    + unfold affine_domain_guard_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact PROBE|].
      eapply exec_Sifthenelse with(v1:=test_value)(b:=true); [exact EVAL|exact BOOL|exact NUMERIC].
    + split.
      * eapply temp_agree_trans; [exact FRAME|apply temp_agree_set; exact RESULT_PRIVATE].
      * rewrite PTree.gss,FLAG; unfold affine_domain_guard_flag; cbn [entry_temps]; rewrite ACTIVE; reflexivity.
  - exists probed; split.
    + unfold affine_domain_guard_code; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact PROBE|].
      eapply exec_Sifthenelse with(v1:=test_value)(b:=false); [exact EVAL|exact BOOL|constructor].
    + split; [exact FRAME|].
      unfold affine_domain_guard_flag; cbn [entry_temps]; rewrite ACTIVE; exact PROBED.
Qed.
Print Assumptions affine_domain_guard_execution.
