From Stdlib Require Import List.
From compcert.lib Require Import Maps Coqlib.
From compcert.common Require Import AST Values.
From compcert.common Require Import Memory Events.
From compcert.lib Require Import Integers.
From Stdlib Require Import ZArith Lia.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightNoWrap ClightCountedLoop ClightFrontendLoopProtocol.
From GuardInterface Require Import ClightIdempotentControlLoop.
Import ListNotations.
Set Implicit Arguments.

Fixpoint fixed_temp_patch (assignments:list(ident*val)) (temps:temp_env) : temp_env :=
  match assignments with
  | []=>temps
  | (identifier,value)::rest=>fixed_temp_patch rest(PTree.set identifier value temps) end.
Fixpoint fixed_patch_value identifier (assignments:list(ident*val)) : option val :=
  match assignments with
  | []=>None
  | (key,value)::rest=>match fixed_patch_value identifier rest with
    | Some later=>Some later
    | None=>if peq identifier key then Some value else None end end.

Lemma fixed_temp_patch_lookup assignments : forall identifier temps,
  (fixed_temp_patch assignments temps)!identifier=
    match fixed_patch_value identifier assignments with Some value=>Some value|None=>temps!identifier end.
Proof.
  induction assignments as [|[key value] rest IH]; intros identifier temps; cbn; [reflexivity|].
  rewrite IH; destruct(fixed_patch_value identifier rest); [reflexivity|].
  rewrite PTree.gsspec; destruct(peq identifier key); reflexivity.
Qed.
Lemma fixed_patch_value_absent assignments : forall identifier,
  ~In identifier(map fst assignments) -> fixed_patch_value identifier assignments=None.
Proof.
  induction assignments as [|[key value] rest IH]; intros identifier FRESH; [reflexivity|].
  cbn in FRESH |- *; rewrite IH by tauto; destruct(peq identifier key) as [SAME|DIFFERENT].
  - subst identifier; exfalso; apply FRESH; left; reflexivity.
  - reflexivity.
Qed.
Theorem fixed_temp_patch_idempotent assignments temps :
  fixed_temp_patch assignments(fixed_temp_patch assignments temps)=fixed_temp_patch assignments temps.
Proof.
  apply PTree.extensionality; intro identifier; rewrite !fixed_temp_patch_lookup.
  destruct(fixed_patch_value identifier assignments); reflexivity.
Qed.
Theorem fixed_temp_patch_commute assignments iterator value temps :
  ~In iterator(map fst assignments) ->
  fixed_temp_patch assignments(PTree.set iterator value temps)=PTree.set iterator value(fixed_temp_patch assignments temps).
Proof.
  intro FRESH; apply PTree.extensionality; intro identifier.
  rewrite !fixed_temp_patch_lookup,!PTree.gsspec,!fixed_temp_patch_lookup;
    destruct(peq identifier iterator) as [SAME|DIFFERENT].
  - subst identifier; rewrite fixed_patch_value_absent by exact FRESH; reflexivity.
  - destruct(fixed_patch_value identifier assignments); reflexivity.
Qed.
Theorem fixed_temp_patch_frame assignments protected temps :
  (forall identifier,In identifier protected -> ~In identifier(map fst assignments)) ->
  temp_agree protected temps(fixed_temp_patch assignments temps).
Proof.
  intros PRIVATE identifier MEMBER; rewrite fixed_temp_patch_lookup,
    fixed_patch_value_absent by(apply PRIVATE; exact MEMBER); reflexivity.
Qed.
Lemma fixed_temp_patch_agree assignments protected before after :
  temp_agree protected before after ->
  temp_agree protected(fixed_temp_patch assignments before)(fixed_temp_patch assignments after).
Proof.
  intros FRAME identifier MEMBER; rewrite !fixed_temp_patch_lookup;
    destruct(fixed_patch_value identifier assignments); [reflexivity|apply FRAME; exact MEMBER].
Qed.

Print Assumptions fixed_temp_patch_lookup.
Print Assumptions fixed_temp_patch_idempotent.
Print Assumptions fixed_temp_patch_commute.
Print Assumptions fixed_temp_patch_frame.
Print Assumptions fixed_temp_patch_agree.

Theorem patched_frontend_control_execution fe ge locals iterator bound body assignments (invariant:temp_env->Prop)
  (DISTINCT:iterator<>bound)
  (ITERATOR_PRIVATE:~In iterator(map fst assignments))
  (BOUND_PRIVATE:~In bound(map fst assignments))
  (BODY:forall temps memory,invariant temps ->
    exec_stmt fe ge locals temps memory body E0(fixed_temp_patch assignments temps) memory Out_normal)
  (SETTLED:forall temps,invariant temps -> invariant(fixed_temp_patch assignments temps))
  (INCREMENT:forall temps word,invariant temps -> invariant(PTree.set iterator(Vint word)temps))
  x upper temps memory :
  (x<upper)%Z -> signed_range x -> signed_range upper -> invariant temps ->
  temps!iterator=Some(Vint(Int.repr x)) -> temps!bound=Some(Vint(Int.repr upper)) ->
  exec_stmt fe ge locals temps memory(frontend_counted_loop iterator bound body)
    E0(PTree.set iterator(Vint(Int.repr upper))(fixed_temp_patch assignments temps)) memory Out_normal.
Proof.
  intros ACTIVE RANGE UPPER INV ITERATOR BOUND.
  set(count:=Z.to_nat(upper-x)).
  assert(SPAN:upper=(x+Z.of_nat count)%Z) by(unfold count; rewrite Z2Nat.id by lia; lia).
  assert(FRAME:forall current,(fixed_temp_patch assignments current)!iterator=current!iterator /\
    (fixed_temp_patch assignments current)!bound=current!bound).
  { intro current; split; rewrite fixed_temp_patch_lookup,fixed_patch_value_absent by assumption; reflexivity. }
  pose proof(@frontend_idempotent_control_execution fe ge locals iterator bound body
    (fixed_temp_patch assignments) invariant DISTINCT BODY FRAME(fixed_temp_patch_idempotent assignments)
    ltac:(intros current word; apply fixed_temp_patch_commute; exact ITERATOR_PRIVATE)
    SETTLED INCREMENT count x upper temps memory SPAN RANGE UPPER INV ITERATOR BOUND) as RUN.
  destruct count as [|count]; [cbn in SPAN; lia|exact RUN].
Qed.
Print Assumptions patched_frontend_control_execution.
