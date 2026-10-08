From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation
  GuardMemoryAffineSourceContext GuardMemoryAffineInnerPointerSyntax.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite
  ClightAffineSnapshotSyntax ClightAffineSnapshotRows ClightAffineSnapshotSourceInputs
  ClightAffineSnapshotPreparation ClightAffineZeroSnapshotPreparation
  ClightAffineEmptyWidth ClightAffineEmptySnapshotCondition ClightAffineEmptySnapshotSource
  ClightAffineEmptyRestore ClightAffineOuterEmpty.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition affine_empty_snapshot_restore original(site:affine_snapshot_source_package original):=
  let package:=snapshot_cached_package site in let shape:=affine_inner_pointer_shape package in
  affine_empty_restore(affine_inner_pointer_row shape)(affine_inner_pointer_bound shape)
    (affine_inner_pointer_column shape)(affine_inner_pointer_inner_bound shape)(affine_inner_pointer_expression package).

Section REWRITE.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Let row:=affine_inner_pointer_row shape.
Let bound:=affine_inner_pointer_bound shape.
Let column:=affine_inner_pointer_column shape.
Let inner_bound:=affine_inner_pointer_inner_bound shape.
Let expression:=affine_inner_pointer_expression package.
Let header:=memory_affine_inner_pointer_header shape expression.
Let CERT:=affine_inner_pointer_syntax package.
Variable width : decision_tree.
Hypothesis WIDTH : compile_affine_empty_width row header(affine_zero_snapshot_header_bounds site)expression=Some width.

Definition affine_empty_snapshot_guarded:=tree_statement(affine_outer_empty_tree row bound)Sskip
  (tree_statement(affine_empty_snapshot_tree site width)(affine_empty_snapshot_restore site)original).

Lemma affine_empty_snapshot_restore_execution fe entry :
  affine_snapshot_original_domain package(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe entry ->
  affine_empty_snapshot_facts site entry ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (affine_empty_snapshot_restore site)E0(affine_empty_snapshot_exit site entry)(entry_memory entry)Out_normal.
Proof.
  intros DOMAIN[HEAD EMPTY].
  destruct(@affine_empty_snapshot_initial_headers original site fe entry DOMAIN HEAD)as [ZERO[COUNT WORDS]].
  unfold affine_empty_snapshot_restore,affine_empty_snapshot_exit.
  apply affine_empty_restore_execution.
  - exact(affine_inner_pointer_rn CERT).
  - exact(affine_inner_pointer_rc CERT).
  - exact(affine_inner_pointer_rk CERT).
  - exact(affine_inner_pointer_nc CERT).
  - exact(affine_inner_pointer_nk CERT).
  - exact(affine_inner_pointer_ck CERT).
  - apply WORDS; unfold header,memory_affine_inner_pointer_header,memory_source_context; left; reflexivity.
  - intros id MEMBER; apply WORDS,memory_source_context_read;
      apply memory_source_affine_parameter_member in MEMBER; tauto.
Qed.

Theorem affine_empty_snapshot_guarded_execution fe ge locals temps memory after final :
  affine_snapshot_original_domain package(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe(Entry ge locals temps memory) ->
  exec_stmt fe ge locals temps memory original E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory affine_empty_snapshot_guarded E0 after final Out_normal.
Proof.
  intros DOMAIN SOURCE.
  pose proof(@affine_outer_empty_condition fe fragment_observation(@eq fragment_observation)row bound)as OUTER.
  pose proof(@affine_snapshot_initial_words(snapshot_cached_source site)package(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe(Entry ge locals temps memory)DOMAIN)as WORDS.
  destruct(readonly_available OUTER _ WORDS)as [empty[checked[RUN SAME]]]; subst checked.
  unfold affine_empty_snapshot_guarded; destruct empty.
  - destruct(readonly_sound OUTER _ _ _ WORDS(conj RUN eq_refl))as [_ SOUND].
    destruct(@affine_outer_empty_source_exit original site fe(Entry ge locals temps memory)after final
      DOMAIN(SOUND eq_refl)SOURCE)as [TEMPS MEMORY]; cbn [entry_temps entry_memory]in TEMPS,MEMORY; subst after final.
    eapply decision_fragment_run with(b:=true); [exact RUN|constructor].
  - eapply decision_fragment_run with(b:=false); [exact RUN|].
    pose proof(@affine_empty_snapshot_condition original site width WIDTH fe fragment_observation
      (@eq fragment_observation))as CONDITION.
    destruct(readonly_available CONDITION _ DOMAIN)as [accepted[checked[PATH SAME]]]; subst checked.
    destruct accepted.
    + destruct(readonly_sound CONDITION _ _ _ DOMAIN(conj PATH eq_refl))as [_ SOUND].
      pose proof(SOUND eq_refl)as FACTS; destruct FACTS as [HEAD EMPTY].
      destruct(@affine_empty_snapshot_source_exit original site fe(Entry ge locals temps memory)after final
        DOMAIN HEAD EMPTY SOURCE)as [TEMPS MEMORY].
      rewrite TEMPS,MEMORY; eapply decision_fragment_run with(b:=true); [exact PATH|].
      exact(@affine_empty_snapshot_restore_execution fe(Entry ge locals temps memory)DOMAIN(conj HEAD EMPTY)).
    + eapply decision_fragment_run with(b:=false); [exact PATH|exact SOURCE].
Qed.
End REWRITE.

Print Assumptions affine_empty_snapshot_restore_execution.
Print Assumptions affine_empty_snapshot_guarded_execution.
