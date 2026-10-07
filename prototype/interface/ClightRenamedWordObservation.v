From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightSameAddress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryPointerCellComparison.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyLoadedTreeSynthesis ClightWordArithmeticTransport ClightWordCoordinateRename
  ClightDirectWordObservation ClightAffineJointObservation ClightObservedHeaderPrefix
  ClightReadonlyCellSwap ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.

Definition renamed_word_observer_tree rename pointer index observers :=
  direct_word_observer_tree(fun _=>None)pointer(word_rename rename index)observers.
Definition renamed_word_point_flag rename pointer index observers entry :=
  match word_address_evaluate(entry_temps entry)pointer(word_rename rename index)with
  | Some(block,offset)=>forallb(direct_word_observer_flag block offset)observers
  | None=>false end.
Definition renamed_word_point_domain fe rename pointer index rhs observers entry :=
  Forall(word_observer_receipt(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry))observers /\
  exists current memory after final,
    renamed_word_frame rename pointer index current(entry_temps entry) /\
    memory_accesses_back(entry_memory entry)memory /\
    exec_stmt fe(entry_ge entry)(entry_env entry)current memory(direct_word_store pointer index rhs)
      E0 after final Out_normal.
Definition renamed_word_point_preserved fe rename pointer index rhs observers entry :=
  forall current memory after final,
    renamed_word_frame rename pointer index current(entry_temps entry) ->
    header_observations_match(map word_observer_snapshot observers)memory ->
    exec_stmt fe(entry_ge entry)(entry_env entry)current memory(direct_word_store pointer index rhs)
      E0 after final Out_normal ->
    header_observations_match(map word_observer_snapshot observers)final.

Theorem renamed_word_point_execution fe rename pointer index rhs observers entry :
  word_arithmetic index -> renamed_word_point_domain fe rename pointer index rhs observers entry ->
  decision_run entry(renamed_word_observer_tree rename pointer index observers)
    (renamed_word_point_flag rename pointer index observers entry).
Proof.
  intros WORD [READS [current [memory [after [final [FRAME [BACK SOURCE]]]]]]].
  destruct(direct_word_store_receipt SOURCE)as [block [offset [value [ADDRESS [STORE _]]]]].
  pose proof(@renamed_word_address_transport rename pointer index _ _ _ _ _ (entry_memory entry) _ _ WORD FRAME ADDRESS)as GUARDED.
  destruct(@direct_word_store_guard_permission _ _ _ _ _ _ BACK STORE)as [VALID ALIGN].
  pose proof(@word_address_evaluate_complete pointer(word_rename rename index)_ _ _ _ _ _
    (word_rename_arithmetic rename WORD)GUARDED)as RESOLVE.
  unfold renamed_word_point_flag; rewrite RESOLVE.
  unfold renamed_word_observer_tree; eapply direct_word_observer_tree_execution.
  - apply word_rename_arithmetic; exact WORD.
  - rewrite(word_replace_none(word_rename_arithmetic rename WORD)); exact GUARDED.
  - exact VALID.
  - exact READS.
Qed.

Theorem renamed_word_point_sound fe rename pointer index rhs observers entry :
  word_arithmetic index -> renamed_word_point_domain fe rename pointer index rhs observers entry ->
  renamed_word_point_flag rename pointer index observers entry=true ->
  renamed_word_point_preserved fe rename pointer index rhs observers entry.
Proof.
  intros WORD [READS [source_temps [source_memory [source_after [source_final [FRAME [BACK SOURCE]]]]]]] ACCEPT.
  destruct(direct_word_store_receipt SOURCE)as [block [offset [value [ADDRESS [STORE _]]]]].
  destruct(@direct_word_store_guard_permission _ _ _ _ _ _ BACK STORE)as [VALID ALIGN].
  pose proof(@renamed_word_address_transport rename pointer index _ _ _ _ _ (entry_memory entry) _ _ WORD FRAME ADDRESS)as GUARDED.
  pose proof(@word_address_evaluate_complete pointer(word_rename rename index)_ _ _ _ _ _
    (word_rename_arithmetic rename WORD)GUARDED)as RESOLVE.
  unfold renamed_word_point_flag in ACCEPT; rewrite RESOLVE in ACCEPT; rewrite List.forallb_forall in ACCEPT.
  intros current memory after final CURRENT INITIAL RUN.
  destruct(direct_word_store_receipt RUN)as [actual_block [actual_offset [actual_value [ACTUAL [ACTUAL_STORE _]]]]].
  pose proof(@renamed_word_address_transport rename pointer index _ _ _ _ _ (entry_memory entry) _ _ WORD CURRENT ACTUAL)as CURRENT_ADDRESS.
  pose proof(@word_address_evaluate_complete pointer(word_rename rename index)_ _ _ _ _ _
    (word_rename_arithmetic rename WORD)CURRENT_ADDRESS)as CURRENT_RESOLVE.
  rewrite RESOLVE in CURRENT_RESOLVE; injection CURRENT_RESOLVE as BLOCK OFFSET; subst actual_block actual_offset.
  destruct(@storev_word_facts _ _ _ _ _ ACTUAL_STORE)as [ACCESS RAW].
  unfold header_observations_match in INITIAL|-*; rewrite Forall_map in INITIAL|-*.
  apply Forall_forall; intros observer MEMBER.
  change(location_load(word_observer_location observer)final=Some(word_observer_value observer)).
  assert(RECEIPT:word_observer_receipt(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)observer).
  { rewrite Forall_forall in READS; exact(READS observer MEMBER). }
  destruct(word_observer_receipt_load RECEIPT)as [LOAD OBSERVER_ALIGN].
  assert(APART:location_disjoint(MemoryLocation Mint32 block(Ptrofs.unsigned offset))(word_observer_location observer)).
  { apply memory_pointer_cells_unequal_separated; [exact ALIGN|exact OBSERVER_ALIGN|apply ACCEPT; exact MEMBER]. }
  rewrite(@location_load_store_other(MemoryLocation Mint32 block(Ptrofs.unsigned offset))actual_value memory final
    (word_observer_location observer)RAW APART).
  rewrite Forall_forall in INITIAL; exact(INITIAL observer MEMBER).
Qed.

Definition renamed_word_point_condition fe O(observe:fragment_observation->O->Prop)
    rename pointer index rhs observers(WORD:word_arithmetic index) :
  readonly_condition(readonly_clight_host fe observe)
    (renamed_word_point_domain fe rename pointer index rhs observers)
    (renamed_word_point_preserved fe rename pointer index rhs observers)
    (renamed_word_observer_tree rename pointer index observers).
Proof.
  constructor.
  - intros entry DOMAIN; eapply readonly_decision_run_safe;
      exact(@renamed_word_point_execution fe rename pointer index rhs observers entry WORD DOMAIN).
  - intros entry DOMAIN; exists(renamed_word_point_flag rename pointer index observers entry),entry;
      split; [exact(@renamed_word_point_execution fe rename pointer index rhs observers entry WORD DOMAIN)|reflexivity].
  - intros entry accepted checked DOMAIN [RUN SAME]; subst checked; split; [reflexivity|].
    intro TRUE; subst accepted.
    pose proof(readonly_decision_determinate RUN(renamed_word_point_execution WORD DOMAIN))as FLAG.
    eapply renamed_word_point_sound; [exact WORD|exact DOMAIN|symmetry; exact FLAG].
Defined.

Definition renamed_word_check_code rename pointer index observers flag :=
  direct_word_check_code(fun _=>None)pointer(word_rename rename index)observers flag.
Theorem renamed_word_check_execution fe rename pointer index rhs observers entry flag :
  word_arithmetic index -> renamed_word_point_domain fe rename pointer index rhs observers entry ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (renamed_word_check_code rename pointer index observers flag)E0
    (PTree.set flag(Vint(if renamed_word_point_flag rename pointer index observers entry then Int.one else Int.zero))
      (entry_temps entry))(entry_memory entry)Out_normal.
Proof.
  intros WORD DOMAIN; destruct entry as [ge locals temps memory].
  unfold renamed_word_check_code,direct_word_check_code;
    eapply decision_fragment_run;
      [exact(@renamed_word_point_execution fe rename pointer index rhs observers
        (Entry ge locals temps memory)WORD DOMAIN)|].
  destruct(renamed_word_point_flag rename pointer index observers(Entry ge locals temps memory)); constructor; constructor.
Qed.

Print Assumptions renamed_word_point_execution.
Print Assumptions renamed_word_point_sound.
Print Assumptions renamed_word_point_condition.
Print Assumptions renamed_word_check_execution.
