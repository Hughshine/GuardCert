From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep Ctypes.
From Guard Require Import ClightTempFrame.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestFirstDomain
  AffineNestProbeRenaming AffineNestProbe AffineNestProbeStage AffineNestProbePartialExecution.
Import ListNotations.
Set Implicit Arguments.

Definition affine_root_probe_initialize iterator bound rename :=
  Ssequence(Sset(rename bound)(Etempvar bound type_int32s))
    (Sset(rename iterator)(Etempvar iterator type_int32s)).

Lemma affine_root_probe_initial_view iterator bound expression body child parameters rename temps iterator_word bound_word :
  temps!iterator=Some(Vint iterator_word) -> temps!bound=Some(Vint bound_word) ->
  rename iterator<>rename bound ->
  ~In(rename iterator)(parameters++[iterator;bound]) -> ~In(rename bound)(parameters++[iterator;bound]) ->
  (forall identifier, In identifier parameters -> identifier<>iterator -> identifier<>bound -> rename identifier=identifier) ->
  affine_renamed_view(affine_probe_needed(AffineSourceAxis iterator bound expression body child) [] parameters)
    rename temps(PTree.set(rename iterator)(Vint iterator_word)(PTree.set(rename bound)(Vint bound_word) temps)).
Proof.
  intros ITERATOR BOUND DISTINCT PRIVATE_ITERATOR PRIVATE_BOUND PARAMETERS identifier MEMBER.
  destruct(peq identifier iterator) as [->|NOT_ITERATOR]; [rewrite PTree.gss; symmetry; exact ITERATOR|].
  destruct(peq identifier bound) as [->|NOT_BOUND].
  - rewrite PTree.gso by congruence; rewrite PTree.gss; symmetry; exact BOUND.
  - assert (PARAMETER:In identifier parameters).
    { unfold affine_probe_needed in MEMBER; cbn in MEMBER; apply in_app_or in MEMBER.
      destruct MEMBER as [MEMBER|MEMBER]; [exact MEMBER|cbn in MEMBER; intuition congruence]. }
    rewrite PARAMETERS by assumption.
    rewrite !PTree.gso; [reflexivity| |].
    + intro SAME; subst; apply PRIVATE_BOUND,in_or_app; auto.
    + intro SAME; subst; apply PRIVATE_ITERATOR,in_or_app; auto.
Qed.

Theorem affine_initialized_first_probe_execution iterator bound expression body child fe ge locals parameters registers rename result temps memory :
  affine_nest_bound_dependencies [] parameters(AffineSourceAxis iterator bound expression body child) ->
  affine_probe_stage_coverage registers(AffineSourceAxis iterator bound expression body child) [] parameters ->
  affine_rename_injective registers rename -> rename iterator<>rename bound ->
  ~In(rename iterator)(parameters++[iterator;bound]) -> ~In(rename bound)(parameters++[iterator;bound]) ->
  (forall identifier, In identifier parameters -> identifier<>iterator -> identifier<>bound -> rename identifier=identifier) ->
  affine_first_header_domain(AffineSourceAxis iterator bound expression body child) temps ->
  exists after,
    exec_stmt fe ge locals temps memory
      (Ssequence(affine_root_probe_initialize iterator bound rename)
        (affine_first_probe(AffineSourceAxis iterator bound expression body child) rename result))
      E0 after memory Out_normal /\
    after!result=Some(Vint(if affine_first_path_flag(AffineSourceAxis iterator bound expression body child) temps then Int.one else Int.zero)).
Proof.
  intros DEPENDENCIES COVERAGE UNIQUE DISTINCT PRIVATE_ITERATOR PRIVATE_BOUND PARAMETERS DOMAIN.
  pose proof DOMAIN as HEADERS; destruct HEADERS as [[iterator_word ITERATOR] [[bound_word BOUND] REST]].
  pose proof(@affine_root_probe_initial_view iterator bound expression body child parameters rename temps iterator_word bound_word
    ITERATOR BOUND DISTINCT PRIVATE_ITERATOR PRIVATE_BOUND PARAMETERS) as VIEW.
  destruct(@affine_first_probe_partial_execution (AffineSourceAxis iterator bound expression body child)
    fe ge locals [] parameters registers rename result temps
    (PTree.set(rename iterator)(Vint iterator_word)(PTree.set(rename bound)(Vint bound_word) temps)) memory
    DEPENDENCIES COVERAGE UNIQUE DOMAIN VIEW) as [after [RUN RESULT]].
  exists after; split; [|exact RESULT].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [|exact RUN].
  unfold affine_root_probe_initialize; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0).
  - constructor; constructor; exact BOUND.
  - constructor; constructor; rewrite PTree.gso; [exact ITERATOR|].
    intro SAME; subst; apply PRIVATE_BOUND,in_or_app; right; cbn; auto.
Qed.
Print Assumptions affine_root_probe_initial_view.
Print Assumptions affine_initialized_first_probe_execution.
