From Stdlib Require Import List Bool PArith.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Smallstep.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightTempFootprint ClightTempScope ClightRegionProgress
  ClightPrivateRegion ClightPrivateRegionProof.
Import ListNotations PrivateRegion.
Set Implicit Arguments.

Definition private_pool_check live pool :=
  forallb (fun id => negb (existsb (Pos.eqb id) live)) (var_names pool).
Lemma private_pool_check_sound live pool : private_pool_check live pool = true ->
  forall id, In id live -> ~ In id (var_names pool).
Proof.
  intros CHECK id USED DECLARED; apply forallb_forall with (x := id) in CHECK; [|exact DECLARED].
  apply negb_true_iff in CHECK.
  assert (FOUND : existsb (Pos.eqb id) live = true).
  { apply existsb_exists; exists id; split; [exact USED|apply Pos.eqb_refl]. }
  congruence.
Qed.
Definition propose_private_names live count : list (ident * type) :=
  let first := Pos.succ (fold_right Pos.max 1%positive live) in
  map (fun n => (Pos.add first (Pos.of_nat n),type_int32s)) (seq 1 count).

Definition transform_private_program supported
  (select : list ident -> list (ident * type) -> statement -> option statement)
  pool p :=
  let live := program_temps p in
  if private_pool_check live pool then
    PrivateRegion.transform_program pool supported (select live pool) p else p.

Theorem transform_private_program_correct supported select :
  (forall s, supported s = true -> exists MODEL : region_progress s, True) ->
  (forall live pool s ts, select live pool s = Some ts -> projected_region_contract live s ts) ->
  forall pool p, forward_simulation (Clight.semantics2 p)
    (Clight.semantics2 (transform_private_program supported select pool p)).
Proof.
  intros SUPPORTED SOUND pool p; unfold transform_private_program.
  destruct (private_pool_check (program_temps p) pool) eqn:FRESH.
  - apply PrivateRegionProof.transform_program_correct2 with (live := program_temps p).
    + exact SUPPORTED.
    + intros; eapply SOUND; eauto.
    + apply program_scope_computed.
    + eapply private_pool_check_sound; exact FRESH.
  - apply forward_simulation_step with (match_states := @eq Clight.state).
    + reflexivity.
    + intros source INIT; exists source; auto.
    + intros; subst; assumption.
    + intros source events next STEP target SAME; subst target; exists next; auto.
Qed.
Print Assumptions transform_private_program_correct.
