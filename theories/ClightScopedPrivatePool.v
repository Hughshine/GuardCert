From Stdlib Require Import List Bool.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST Smallstep.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightTempFootprint ClightTempScope ClightRegionProgress
  ClightPrivatePool ClightScopedPrivateRegion ClightScopedPrivateRegionProof ClightGlobalScope.
Set Implicit Arguments.

(** The selector is certified for this actual program's global environment.
    Metadata and resource failures keep the source program. The AST pass is
    the original private-region transform. *)
Definition transform_scoped_private_program globals supported
  (select : Clight.program -> list ident -> list (ident * type) -> statement -> option statement)
  pool p :=
  let live := program_temps p in
  if program_avoids_check globals p && private_pool_check live pool then
    ScopedPrivateRegion.transform_program pool supported (select p live pool) p else p.

Theorem transform_scoped_private_program_correct globals supported select :
  (forall s, supported s=true -> exists MODEL : region_progress s, True) ->
  (forall p live pool s ts, select p live pool s=Some ts ->
    ScopedPrivateRegion.projected_region_contract live (globalenv p) globals s ts) ->
  forall pool p, forward_simulation (Clight.semantics2 p)
    (Clight.semantics2 (transform_scoped_private_program globals supported select pool p)).
Proof.
  intros SUPPORTED SELECT pool p; unfold transform_scoped_private_program.
  destruct (program_avoids_check globals p && private_pool_check (program_temps p) pool) eqn:CHECK.
  - apply andb_true_iff in CHECK as [GLOBAL FRESH].
    eapply ScopedPrivateRegionProof.transform_program_correct2 with (live:=program_temps p) (globals:=globals).
    + exact SUPPORTED.
    + apply program_avoids_check_sound; exact GLOBAL.
    + intros; eapply SELECT; eauto.
    + apply program_scope_computed.
    + apply private_pool_check_sound; exact FRESH.
  - apply forward_simulation_step with (match_states:=@eq Clight.state).
    + reflexivity.
    + intros source INIT; exists source; auto.
    + intros; subst; assumption.
    + intros source events next STEP target SAME; subst target; exists next; auto.
Qed.
Print Assumptions transform_scoped_private_program_correct.
