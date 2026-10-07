From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint
  ClightSameAddress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryPointerAccess GuardMemoryPointerCellComparison.
From GuardInterface Require Import GuardInterface GuardedRewrite ClightReadonlyRewrite
  ClightReadonlyLoadedTreeSynthesis ClightWordArithmeticTransport ClightAffineJointObservation
  ClightObservedHeaderPrefix ClightObservedWordProbe ClightReadonlyCellSwap ClightStorePermissions ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition direct_word_address pointer index :=
  Ebinop Oadd(Etempvar pointer(Tpointer type_int32s noattr))index(Tpointer type_int32s noattr).
Definition direct_word_store pointer index rhs := Sassign(Ederef(direct_word_address pointer index)type_int32s)rhs.
Definition direct_word_frame binding pointer index before current :=
  before!pointer=current!pointer /\ word_replacement_frame binding index before current.

(** Successful original pointer arithmetic provides its actual word operands.
    Arithmetic keeps CompCert's modular semantics; no affine/no-wrap model is
    used to obtain the permission to perform a guard comparison. *)
Lemma direct_word_address_operands ge locals temps memory pointer index block offset :
  word_arithmetic index ->
  eval_expr ge locals temps memory(direct_word_address pointer index)(Vptr block offset) ->
  exists base word,temps!pointer=Some(Vptr block base) /\
    eval_expr ge locals temps memory index(Vint word) /\
    sem_binary_operation ge Oadd(Vptr block base)(Tpointer type_int32s noattr)
      (Vint word)type_int32s memory=Some(Vptr block offset).
Proof.
  intros WORD SOURCE; apply scalar_binary_inv in SOURCE as [left [right [POINTER [INDEX OP]]]].
  apply scalar_temp_inv in POINTER.
  cbn [typeof] in OP; rewrite(word_arithmetic_type WORD) in OP.
  destruct left,right; cbn in OP; try discriminate;
    try solve[destruct Archi.ptr64; discriminate].
  inversion OP; subst; do 2 eexists; repeat split; eassumption.
Qed.
Theorem direct_word_address_transport binding pointer index ge locals before memory current target_memory block offset :
  word_arithmetic index -> direct_word_frame binding pointer index before current ->
  eval_expr ge locals before memory(direct_word_address pointer index)(Vptr block offset) ->
  eval_expr ge locals current target_memory(direct_word_address pointer(word_replace binding index))(Vptr block offset).
Proof.
  intros WORD [POINTER FRAME] SOURCE.
  destruct(direct_word_address_operands WORD SOURCE)as [base [word [PTR [INDEX OP]]]].
  unfold direct_word_address; eapply eval_Ebinop.
  - constructor; rewrite <-POINTER; exact PTR.
  - eapply word_replacement_evaluation; eassumption.
  - rewrite word_replace_type,(word_arithmetic_type WORD); exact OP.
Qed.

Lemma direct_word_store_receipt fe ge locals temps memory pointer index rhs trace after final outcome :
  exec_stmt fe ge locals temps memory(direct_word_store pointer index rhs)trace after final outcome ->
  exists block offset value,
    eval_expr ge locals temps memory(direct_word_address pointer index)(Vptr block offset) /\
    Mem.storev Mint32 memory(Vptr block offset)value=Some final /\
    trace=E0 /\ after=temps /\ outcome=Out_normal.
Proof.
  unfold direct_word_store; intro SOURCE; inversion SOURCE; subst.
  match goal with LEFT : eval_lvalue _ _ _ _ (Ederef _ type_int32s) _ _ _ |- _ => inversion LEFT; subst end.
  match goal with ASSIGN : assign_loc _ _ _ _ _ _ _ _ |- _ =>
    inversion ASSIGN; subst; cbn [typeof access_mode] in *; try discriminate end.
  match goal with MODE : access_mode type_int32s=By_value _ |- _ => inversion MODE; subst end.
  do 3 eexists; repeat split; try reflexivity; eassumption.
Qed.

Lemma direct_word_store_guard_permission entry memory block offset value final :
  memory_accesses_back(entry_memory entry)memory ->
  Mem.storev Mint32 memory(Vptr block offset)value=Some final ->
  Mem.valid_pointer(entry_memory entry)block(Ptrofs.unsigned offset)=true /\
  (4|Ptrofs.unsigned offset).
Proof.
  intros BACK STORE; destruct(@storev_word_facts _ _ _ _ _ STORE)as [[ACCESS _] RAW].
  pose proof(BACK _ _ _ _ ACCESS)as ORIGINAL; split; [|exact(proj2 ORIGINAL)].
  apply Mem.valid_pointer_nonempty_perm; destruct ORIGINAL as [PERMISSION ALIGN].
  eapply Mem.perm_implies; [apply PERMISSION; cbn [size_chunk]; lia|constructor].
Qed.

Fixpoint direct_word_observer_tree binding pointer index observers := match observers with
| []=>Decision true
| observer::rest=>Test(memory_pointer_cells_test(direct_word_address pointer(word_replace binding index))
    (word_observer_address observer))(direct_word_observer_tree binding pointer index rest)(Decision false)
end.
Definition direct_word_observer_flag block offset observer :=
  memory_pointer_cells_unequal block offset(word_observer_block observer)(word_observer_offset observer).

Lemma direct_word_observer_tree_addresses binding pointer index first second :
  map word_observer_address first=map word_observer_address second ->
  direct_word_observer_tree binding pointer index first=direct_word_observer_tree binding pointer index second.
Proof.
  revert second; induction first as [|observer rest IH]; intros [|other tail] SAME; cbn in SAME; try discriminate.
  - reflexivity.
  - injection SAME as ADDRESS REST; cbn [direct_word_observer_tree]; rewrite ADDRESS,(IH _ REST); reflexivity.
Qed.

Lemma direct_word_observer_tree_execution binding pointer index observers entry block offset :
  word_arithmetic index ->
  eval_expr(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    (direct_word_address pointer(word_replace binding index))(Vptr block offset) ->
  Mem.valid_pointer(entry_memory entry)block(Ptrofs.unsigned offset)=true ->
  Forall(word_observer_receipt(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry))observers ->
  decision_run entry(direct_word_observer_tree binding pointer index observers)
    (forallb(direct_word_observer_flag block offset)observers).
Proof.
  intros WORD ADDRESS VALID READS; induction READS; cbn [direct_word_observer_tree forallb]; [constructor|].
  destruct H as [TYPE [OBSERVED LOAD]].
  pose proof(@memory_pointer_cells_test_evaluation _ _ _ _
    (direct_word_address pointer(word_replace binding index))(word_observer_address x)
    block offset(word_observer_block x)(word_observer_offset x) eq_refl TYPE ADDRESS OBSERVED
    VALID(@loaded_address_valid _ _ _ _ _ LOAD))as TEST.
  change(expression_test
    (memory_pointer_cells_test(direct_word_address pointer(word_replace binding index))(word_observer_address x))
    entry(direct_word_observer_flag block offset x))in TEST.
  destruct(direct_word_observer_flag block offset x)eqn:FLAG; cbn.
  - eapply run_test; [exact TEST|exact IHREADS].
  - eapply run_test; [exact TEST|constructor].
Qed.

Definition direct_word_point_domain fe binding pointer index rhs observers entry :=
  Forall(word_observer_receipt(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry))observers /\
  exists current memory after final,
    direct_word_frame binding pointer index current(entry_temps entry) /\
    memory_accesses_back(entry_memory entry)memory /\
    exec_stmt fe(entry_ge entry)(entry_env entry)current memory(direct_word_store pointer index rhs)
      E0 after final Out_normal.
Definition direct_word_point_preserved fe binding pointer index rhs observers entry :=
  forall current memory after final,
    direct_word_frame binding pointer index current(entry_temps entry) ->
    header_observations_match(map word_observer_snapshot observers)memory ->
    exec_stmt fe(entry_ge entry)(entry_env entry)current memory(direct_word_store pointer index rhs)
      E0 after final Out_normal ->
    header_observations_match(map word_observer_snapshot observers)final.

Theorem direct_word_point_available fe binding pointer index rhs observers entry :
  word_arithmetic index -> direct_word_point_domain fe binding pointer index rhs observers entry ->
  exists accepted,decision_run entry(direct_word_observer_tree binding pointer index observers)accepted.
Proof.
  intros WORD [READS [current [memory [after [final [FRAME [BACK SOURCE]]]]]]].
  destruct(direct_word_store_receipt SOURCE)as [block [offset [value [ADDRESS [STORE _]]]]].
  destruct(@direct_word_store_guard_permission _ _ _ _ _ _ BACK STORE)as [VALID ALIGN].
  eexists; apply direct_word_observer_tree_execution; [exact WORD| |exact VALID|exact READS].
  eapply direct_word_address_transport; eassumption.
Qed.

Theorem direct_word_point_sound fe binding pointer index rhs observers entry :
  word_arithmetic index -> direct_word_point_domain fe binding pointer index rhs observers entry ->
  decision_run entry(direct_word_observer_tree binding pointer index observers)true ->
  direct_word_point_preserved fe binding pointer index rhs observers entry.
Proof.
  intros WORD [READS [source_temps [source_memory [source_after [source_final [FRAME [BACK SOURCE]]]]]]] ACCEPT.
  destruct(direct_word_store_receipt SOURCE)as [block [offset [value [ADDRESS [STORE _]]]]].
  destruct(@direct_word_store_guard_permission _ _ _ _ _ _ BACK STORE)as [VALID ALIGN].
  pose proof(@direct_word_address_transport binding pointer index _ _ _ _ _ (entry_memory entry) _ _
    WORD FRAME ADDRESS)as GUARDED.
  pose proof(@direct_word_observer_tree_execution binding pointer index observers entry block offset
    WORD GUARDED VALID READS)as CHECK.
  pose proof(readonly_decision_determinate ACCEPT CHECK)as ALL.
  symmetry in ALL; rewrite List.forallb_forall in ALL.
  intros current memory after final CURRENT INITIAL RUN.
  destruct(direct_word_store_receipt RUN)as [actual_block [actual_offset [actual_value [ACTUAL [ACTUAL_STORE _]]]]].
  pose proof(@direct_word_address_transport binding pointer index _ _ _ _ _ (entry_memory entry) _ _
    WORD CURRENT ACTUAL)as CURRENT_ADDRESS.
  pose proof(proj1(expressions_determinate(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry))
    _ _ GUARDED _ CURRENT_ADDRESS)as SAME.
  injection SAME as BLOCK OFFSET; subst actual_block actual_offset.
  destruct(@storev_word_facts _ _ _ _ _ ACTUAL_STORE)as [ACCESS RAW].
  unfold header_observations_match in INITIAL|-*; rewrite Forall_map in INITIAL|-*.
  apply Forall_forall; intros observer MEMBER.
  change(location_load(word_observer_location observer)final=Some(word_observer_value observer)).
  assert(RECEIPT:word_observer_receipt(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)observer).
  { rewrite Forall_forall in READS; exact(READS observer MEMBER). }
  destruct(word_observer_receipt_load RECEIPT)as [LOAD OBSERVER_ALIGN].
  assert(APART:location_disjoint(MemoryLocation Mint32 block(Ptrofs.unsigned offset))(word_observer_location observer)).
  { apply memory_pointer_cells_unequal_separated; [exact ALIGN|exact OBSERVER_ALIGN|apply ALL; exact MEMBER]. }
  rewrite(@location_load_store_other(MemoryLocation Mint32 block(Ptrofs.unsigned offset))actual_value memory final
    (word_observer_location observer)RAW APART).
  rewrite Forall_forall in INITIAL; exact(INITIAL observer MEMBER).
Qed.

Definition direct_word_point_condition fe O (observe:fragment_observation->O->Prop)
    binding pointer index rhs observers (WORD:word_arithmetic index) :
  readonly_condition(readonly_clight_host fe observe)
    (direct_word_point_domain fe binding pointer index rhs observers)
    (direct_word_point_preserved fe binding pointer index rhs observers)
    (direct_word_observer_tree binding pointer index observers).
Proof.
  constructor.
  - intros entry DOMAIN; destruct(direct_word_point_available WORD DOMAIN)as [accepted RUN].
    eapply readonly_decision_run_safe; exact RUN.
  - intros entry DOMAIN; destruct(direct_word_point_available WORD DOMAIN)as [accepted RUN].
    exists accepted,entry; split; [exact RUN|reflexivity].
  - intros entry accepted checked DOMAIN [RUN SAME]; subst checked; split; [reflexivity|].
    intro TRUE; subst accepted; exact(direct_word_point_sound WORD DOMAIN RUN).
Defined.

Definition direct_word_check_code binding pointer index observers flag :=
  tree_statement(direct_word_observer_tree binding pointer index observers)
    (Sset flag(Econst_int Int.one type_int32s))(Sset flag(Econst_int Int.zero type_int32s)).
Theorem direct_word_point_check_execution fe binding pointer index rhs observers entry flag :
  word_arithmetic index -> direct_word_point_domain fe binding pointer index rhs observers entry ->
  exists accepted:bool,
    exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
      (direct_word_check_code binding pointer index observers flag)E0
      (PTree.set flag(Vint(if accepted then Int.one else Int.zero))(entry_temps entry))
      (entry_memory entry)Out_normal /\
    (accepted=true -> direct_word_point_preserved fe binding pointer index rhs observers entry).
Proof.
  intros WORD DOMAIN; destruct entry as [ge locals temps memory].
  destruct(direct_word_point_available WORD DOMAIN)as [accepted RUN].
  exists accepted; split.
  - unfold direct_word_check_code; eapply decision_fragment_run; [exact RUN|].
    destruct accepted; constructor; constructor.
  - intro TRUE; subst accepted; exact(direct_word_point_sound WORD DOMAIN RUN).
Qed.

Print Assumptions direct_word_address_operands.
Print Assumptions direct_word_address_transport.
Print Assumptions direct_word_store_receipt.
Print Assumptions direct_word_store_guard_permission.
Print Assumptions direct_word_observer_tree_execution.
Print Assumptions direct_word_point_available.
Print Assumptions direct_word_point_sound.
Print Assumptions direct_word_point_condition.
Print Assumptions direct_word_observer_tree_addresses.
Print Assumptions direct_word_point_check_execution.
