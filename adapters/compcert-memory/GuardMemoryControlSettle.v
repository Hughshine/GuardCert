From Stdlib Require Import List.
From compcert.lib Require Import Maps Coqlib.
From compcert.common Require Import AST Values.
From compcert.cfrontend Require Import Clight.
Import ListNotations.
Set Implicit Arguments.

Fixpoint memory_settle_controls (assignments : list (ident*val)) (temps : temp_env) :=
  match assignments with
  | [] => temps
  | (identifier,value)::rest => PTree.set identifier value (memory_settle_controls rest temps)
  end.
Lemma memory_settle_controls_frame assignments temps identifier :
  ~ In identifier (map fst assignments) ->
  (memory_settle_controls assignments temps) ! identifier = temps ! identifier.
Proof.
  induction assignments as [|[id value] rest IH]; cbn; [reflexivity|].
  intro FRESH; rewrite PTree.gso by (intro SAME; subst; apply FRESH; cbn; auto).
  apply IH; intro MEMBER; apply FRESH; cbn; auto.
Qed.
Lemma memory_settle_controls_commute assignments temps identifier value :
  ~ In identifier (map fst assignments) ->
  memory_settle_controls assignments (PTree.set identifier value temps) =
    PTree.set identifier value (memory_settle_controls assignments temps).
Proof.
  induction assignments as [|[id word] rest IH]; cbn; [reflexivity|].
  intro FRESH; rewrite IH by (intro MEMBER; apply FRESH; cbn; auto).
  apply PTree.extensionality; intro key; rewrite !PTree.gsspec.
  destruct (peq key id),(peq key identifier); subst; intuition congruence.
Qed.
Lemma memory_settle_controls_lookup assignments temps first identifier :
  In identifier (map fst assignments) ->
  (memory_settle_controls assignments temps) ! identifier =
    (memory_settle_controls assignments first) ! identifier.
Proof.
  induction assignments as [|[id value] rest IH]; cbn; [contradiction|].
  intro MEMBER; rewrite !PTree.gsspec; destruct (peq identifier id); [reflexivity|].
  apply IH; destruct MEMBER as [SAME|MEMBER]; [congruence|exact MEMBER].
Qed.
Theorem memory_settle_controls_idempotent assignments temps :
  memory_settle_controls assignments (memory_settle_controls assignments temps) =
    memory_settle_controls assignments temps.
Proof.
  apply PTree.extensionality; intro identifier.
  destruct (in_dec peq identifier (map fst assignments)) as [MEMBER|FRESH].
  - apply memory_settle_controls_lookup; exact MEMBER.
  - rewrite !memory_settle_controls_frame by exact FRESH; reflexivity.
Qed.
Print Assumptions memory_settle_controls_idempotent.
Print Assumptions memory_settle_controls_commute.
