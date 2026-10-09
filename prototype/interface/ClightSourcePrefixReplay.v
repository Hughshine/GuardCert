From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardInterface Require Import ClightSourceObservation ClightLoadedBoundSyntax.
Import ListNotations.
Set Implicit Arguments.

(** Transport source reads by their pointer inputs alone. Their output
    temporaries need not agree initially, and duplicate outputs are allowed. *)
Lemma source_prefix_output_transport loads fe ge locals original memory after :
  exec_stmt fe ge locals original memory(source_load_prefix loads)E0 after memory Out_normal ->
  forall current,temp_agree(source_load_pointers loads)original current ->
  exists target,exec_stmt fe ge locals current memory(source_load_prefix loads)E0 target memory Out_normal /\
    temp_agree(source_load_targets loads)after target.
Proof.
  revert original after; induction loads as [|[out pointer]rest IH]; intros original after RUN current FRAME.
  - inversion RUN; subst; exists current; split; [constructor|intros id MEMBER; contradiction].
  - cbn [source_load_prefix]in RUN; inversion RUN; subst.
    2:match goal with SET:exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _=>inversion SET; subst; contradiction end.
    match goal with SET:exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ |- _=>inversion SET; subst end.
    match goal with EMPTY:E0 ** ?tail=E0 |- _=>cbn in EMPTY; subst tail end.
    match goal with EVAL:eval_expr _ _ _ ?mem (signed_load pointer) ?value |- _=>
      assert(LOAD:eval_expr ge locals current mem(signed_load pointer)value)by
        (eapply expression_temp_transport with(live:=source_load_pointers((out,pointer)::rest));
          [unfold expression_scope; cbn [expression_temps signed_load]; intros id MEMBER;
           cbn in MEMBER; destruct MEMBER as [->|[]]; cbn; auto|exact FRAME|exact EVAL]) end.
    match goal with TAIL:exec_stmt _ _ _ (PTree.set out ?value original) _ (source_load_prefix rest) _ _ _ _ |- _=>
      destruct(IH _ _ TAIL(PTree.set out value current))as [target[EXECUTE PUBLIC]] end.
    + intros id MEMBER; rewrite !PTree.gsspec; destruct(peq id out); [reflexivity|].
      apply FRAME; cbn [source_load_pointers map snd]; right; exact MEMBER.
    + exists target; split.
      * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; exact LOAD|exact EXECUTE].
      * intros id MEMBER; cbn [source_load_targets map fst]in MEMBER; destruct MEMBER as [EQUAL|MEMBER].
        -- subst id; destruct(in_dec peq out(source_load_targets rest))as [IN|OUT].
           ++ apply PUBLIC; exact IN.
           ++ rewrite(@writes_only_frame _ _ _ _ _ _ _ _ _ _ EXECUTE
                (source_load_targets rest)(source_load_prefix_writes rest)out OUT).
              match goal with TAIL:exec_stmt _ _ _ (PTree.set out _ original) _ (source_load_prefix rest) _ _ _ _ |- _=>
                rewrite(@writes_only_frame _ _ _ _ _ _ _ _ _ _ TAIL
                  (source_load_targets rest)(source_load_prefix_writes rest)out OUT) end.
              rewrite !PTree.gss; reflexivity.
        -- apply PUBLIC; exact MEMBER.
Qed.

Theorem source_prefix_replay loads fe ge locals before memory after :
  (forall id,In id(source_load_targets loads)->~In id(source_load_pointers loads)) ->
  exec_stmt fe ge locals before memory(source_load_prefix loads)E0 after memory Out_normal ->
  exec_stmt fe ge locals after memory(source_load_prefix loads)E0 after memory Out_normal.
Proof.
  intros FRESH RUN.
  assert(POINTERS:temp_agree(source_load_pointers loads)before after).
  { intros id MEMBER; eapply writes_only_frame; [exact RUN|apply source_load_prefix_writes|].
    intro TARGET; exact(FRESH id TARGET MEMBER). }
  destruct(@source_prefix_output_transport loads fe ge locals before memory after RUN after POINTERS)
    as [target[EXECUTE PUBLIC]].
  assert(SAME:target=after).
  { apply PTree.extensionality; intro id; destruct(in_dec peq id(source_load_targets loads))as [IN|OUT].
    - apply PUBLIC; exact IN.
    - eapply writes_only_frame; [exact EXECUTE|apply source_load_prefix_writes|exact OUT]. }
  subst target; exact EXECUTE.
Qed.

Print Assumptions source_prefix_output_transport.
Print Assumptions source_prefix_replay.
