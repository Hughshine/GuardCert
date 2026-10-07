From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightSameAddress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryPointerCellComparison.
From GuardInterface Require Import ClightWordArithmeticTransport ClightDirectWordObservation
  ClightAffineJointObservation ClightNestedConstantHeaders ClightNestedConstantSite
  ClightLoadedBoundSyntax ClightSignedIndexedOffsetHeader ClightObservedHeaderPrefix.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The actual index contains a runtime product. This fixture deliberately
    wraps 2*MAX: ((2*MAX)+3)*5+4 is the machine word 9. Separation can be
    checked safely without using the later mathematical no-wrap premise. *)
Definition thp_index := Ebinop Oadd
  (Ebinop Omul(Ebinop Oadd
    (Ebinop Omul(Etempvar 1%positive type_int32s)(Etempvar 6%positive type_int32s)type_int32s)
    (Etempvar 2%positive type_int32s)type_int32s)(Econst_int(Int.repr 5)type_int32s)type_int32s)
  (Etempvar 3%positive type_int32s)type_int32s.
Definition thp_cell := Ederef(direct_word_address 10%positive thp_index)type_int32s.
Definition thp_rhs := Ebinop Oadd thp_cell(Etempvar 7%positive type_int32s)type_int32s.
Definition thp_body := direct_word_store 10%positive thp_index thp_rhs.
Definition thp_shape := NestedConstantShape 1%positive 2%positive 3%positive
  4%positive 5%positive 50%positive 51%positive 5 thp_body 11%positive Int.one Int.one Int.one.
Definition thp_temps := PTree.set 1%positive(Vint(Int.repr 2))
  (PTree.set 2%positive(Vint(Int.repr 3))(PTree.set 3%positive(Vint(Int.repr 4))
    (PTree.set 6%positive(Vint(Int.repr Int.max_signed))(PTree.set 7%positive(Vint(Int.repr 7))
      (PTree.set 10%positive(Vptr 1%positive(Ptrofs.repr 16))
        (PTree.set 11%positive(Vptr 1%positive Ptrofs.zero)(PTree.empty val))))))).
Definition thp_observers :=
  [ClightWordObserver(signed_pointer_temp 11%positive)1%positive Ptrofs.zero(Vint Int.zero);
   ClightWordObserver(signed_indexed_pointer 11%positive Int.one)1%positive(Ptrofs.repr 4)(Vint Int.zero)].

Example thp_dynamic_product_recognized : word_arithmetic_check thp_index=true.
Proof. vm_compute; reflexivity. Qed.
Lemma thp_index_arithmetic : word_arithmetic thp_index.
Proof. apply word_arithmetic_check_sound; exact thp_dynamic_product_recognized. Qed.
Example thp_load_not_transportable : word_arithmetic_check thp_cell=false.
Proof. reflexivity. Qed.
Example thp_division_not_transportable : word_arithmetic_check
  (Ebinop Odiv(Etempvar 1%positive type_int32s)(Etempvar 6%positive type_int32s)type_int32s)=false.
Proof. reflexivity. Qed.
Example thp_wrap_is_not_mathematical :
  Int.signed(Int.mul(Int.repr 2)(Int.repr Int.max_signed))=(-2) /\
  ~(-2147483648<=2*Int.max_signed<=2147483647).
Proof. split; [reflexivity|change(~(-2147483648<=4294967294<=2147483647)); lia]. Qed.

Definition thp_allocated := fst(Mem.alloc Mem.empty 0 64).
Lemma thp_allocated_access offset : 0<=offset -> offset+4<=64 -> (4|offset) ->
  Mem.valid_access thp_allocated Mint32 1%positive offset Writable.
Proof.
  intros LOW HIGH ALIGN; eapply Mem.valid_access_implies with(p1:=Freeable); [|constructor].
  eapply Mem.valid_access_alloc_same with(m1:=Mem.empty)(lo:=0)(hi:=64);
    [reflexivity|exact LOW|exact HIGH|exact ALIGN].
Qed.
Definition thp_root_state : {memory|Mem.store Mint32 thp_allocated 1%positive 0(Vint Int.zero)=Some memory}.
Proof. apply Mem.valid_access_store,thp_allocated_access; try lia; exists 0; reflexivity. Defined.
Definition thp_root := proj1_sig thp_root_state.
Definition thp_child_state : {memory|Mem.store Mint32 thp_root 1%positive 4(Vint Int.zero)=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig thp_root_state)|].
  apply thp_allocated_access; try lia; exists 1; reflexivity.
Defined.
Definition thp_child := proj1_sig thp_child_state.
Definition thp_data_state : {memory|Mem.store Mint32 thp_child 1%positive 52(Vint Int.zero)=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig thp_child_state)|].
  eapply Mem.store_valid_access_1; [exact(proj2_sig thp_root_state)|].
  apply thp_allocated_access; try lia; exists 13; reflexivity.
Defined.
Definition thp_memory := proj1_sig thp_data_state.
Lemma thp_header_reads :
  Mem.loadv Mint32 thp_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.zero) /\
  Mem.loadv Mint32 thp_memory(Vptr 1%positive(Ptrofs.repr 4))=Some(Vint Int.zero).
Proof.
  change(Mem.load Mint32 thp_memory 1%positive 0=Some(Vint Int.zero) /\
    Mem.load Mint32 thp_memory 1%positive 4=Some(Vint Int.zero)); split.
  - rewrite(@Mem.load_store_other Mint32 thp_child 1%positive 52(Vint Int.zero)thp_memory
      (proj2_sig thp_data_state)Mint32 1%positive 0)by(cbn; lia).
    rewrite(@Mem.load_store_other Mint32 thp_root 1%positive 4(Vint Int.zero)thp_child
      (proj2_sig thp_child_state)Mint32 1%positive 0)by(cbn; lia).
    rewrite(@Mem.load_store_same Mint32 thp_allocated 1%positive 0(Vint Int.zero)thp_root
      (proj2_sig thp_root_state)); reflexivity.
  - rewrite(@Mem.load_store_other Mint32 thp_child 1%positive 52(Vint Int.zero)thp_memory
      (proj2_sig thp_data_state)Mint32 1%positive 4)by(cbn; lia).
    rewrite(@Mem.load_store_same Mint32 thp_root 1%positive 4(Vint Int.zero)thp_child
      (proj2_sig thp_child_state)); reflexivity.
Qed.
Lemma thp_data_read : Mem.loadv Mint32 thp_memory(Vptr 1%positive(Ptrofs.repr 52))=Some(Vint Int.zero).
Proof.
  change(Mem.load Mint32 thp_memory 1%positive 52=Some(Vint Int.zero)).
  rewrite(@Mem.load_store_same Mint32 thp_child 1%positive 52(Vint Int.zero)thp_memory
    (proj2_sig thp_data_state)); reflexivity.
Qed.
Definition thp_final_state : {memory|Mem.store Mint32 thp_memory 1%positive 52(Vint(Int.repr 7))=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig thp_data_state)|].
  eapply Mem.store_valid_access_3; exact(proj2_sig thp_data_state).
Defined.
Definition thp_final := proj1_sig thp_final_state.

Lemma thp_index_evaluation ge locals memory : eval_expr ge locals thp_temps memory thp_index(Vint(Int.repr 9)).
Proof.
  unfold thp_index; eapply eval_Ebinop with(v1:=Vint(Int.repr 5))(v2:=Vint(Int.repr 4));
    [|apply eval_Etempvar; reflexivity|reflexivity].
  eapply eval_Ebinop with(v1:=Vint Int.one)(v2:=Vint(Int.repr 5)); [|constructor|reflexivity].
  eapply eval_Ebinop with(v1:=Vint(Int.repr(-2)))(v2:=Vint(Int.repr 3));
    [|apply eval_Etempvar; reflexivity|].
  2: { change(Some(Vint(Int.add(Int.repr(-2))(Int.repr 3)))=Some(Vint Int.one)).
       f_equal; f_equal; apply Int.same_if_eq; reflexivity. }
  eapply eval_Ebinop with(v1:=Vint(Int.repr 2))(v2:=Vint(Int.repr Int.max_signed));
    [apply eval_Etempvar; reflexivity|apply eval_Etempvar; reflexivity|].
  change(Some(Vint(Int.mul(Int.repr 2)(Int.repr Int.max_signed)))=Some(Vint(Int.repr(-2)))).
  f_equal; f_equal; apply Int.same_if_eq; reflexivity.
Qed.
Lemma thp_address_evaluation ge locals memory : eval_expr ge locals thp_temps memory
  (direct_word_address 10%positive thp_index)(Vptr 1%positive(Ptrofs.repr 52)).
Proof. eapply eval_Ebinop; [constructor; reflexivity|apply thp_index_evaluation|reflexivity]. Qed.
Theorem thp_actual_wrapping_rmw fe ge locals : exec_stmt fe ge locals thp_temps thp_memory thp_body
  E0 thp_temps thp_final Out_normal.
Proof.
  unfold thp_body,direct_word_store; eapply exec_Sassign with(v2:=Vint(Int.repr 7))(v:=Vint(Int.repr 7)).
  - apply eval_Ederef,thp_address_evaluation.
  - unfold thp_rhs; eapply eval_Ebinop with(v1:=Vint Int.zero)(v2:=Vint(Int.repr 7));
      [|constructor; reflexivity|reflexivity].
    eapply eval_Elvalue with(loc:=1%positive)(ofs:=Ptrofs.repr 52)(bf:=Full);
      [apply eval_Ederef,thp_address_evaluation|].
    apply deref_loc_value with(chunk:=Mint32); [reflexivity|exact thp_data_read].
  - reflexivity.
  - apply assign_loc_value with(chunk:=Mint32); [reflexivity|].
    exact(proj2_sig thp_final_state).
Qed.

Lemma thp_observer_receipts ge locals : Forall(word_observer_receipt ge locals thp_temps thp_memory)thp_observers.
Proof.
  destruct thp_header_reads as [ROOT CHILD]; unfold thp_observers; constructor.
  - split; [reflexivity|split; [apply eval_Etempvar; reflexivity|exact ROOT]].
  - constructor; [|constructor].
    split; [reflexivity|split].
    + exact(@signed_indexed_pointer_eval ge locals thp_temps thp_memory 11%positive Int.one
        1%positive Ptrofs.zero eq_refl).
    + exact CHILD.
Qed.
Theorem thp_actual_separation_check ge locals : decision_run(Entry ge locals thp_temps thp_memory)
  (direct_word_observer_tree(fun _=>None)10%positive thp_index thp_observers)true.
Proof.
  change true with(forallb(direct_word_observer_flag 1%positive(Ptrofs.repr 52))thp_observers).
  eapply direct_word_observer_tree_execution; [exact thp_index_arithmetic| | |apply thp_observer_receipts].
  - rewrite(word_replace_none thp_index_arithmetic); apply thp_address_evaluation.
  - eapply loaded_address_valid; exact thp_data_read.
Qed.

Lemma thp_point_domain fe ge locals : direct_word_point_domain fe(fun _=>None)
  10%positive thp_index thp_rhs thp_observers(Entry ge locals thp_temps thp_memory).
Proof.
  split; [apply thp_observer_receipts|].
  exists thp_temps,thp_memory,thp_temps,thp_final; split.
  - split; [reflexivity|intros id MEMBER; reflexivity].
  - split; [apply ClightStorePermissions.memory_accesses_back_refl|apply thp_actual_wrapping_rmw].
Qed.
Theorem thp_acceptance_preserves_both_headers
  (fe:genv->function->list val->mem->env->temp_env->mem->Prop)(ge:genv)(locals:env) :
  header_observations_match(map word_observer_snapshot thp_observers)thp_final.
Proof.
  pose proof(direct_word_point_sound thp_index_arithmetic(thp_point_domain fe ge locals)
    (thp_actual_separation_check ge locals))as PRESERVE.
  eapply PRESERVE; [split; [reflexivity|intros id MEMBER; reflexivity]| |apply thp_actual_wrapping_rmw].
  unfold header_observations_match; rewrite Forall_map.
  eapply Forall_impl; [|exact(thp_observer_receipts ge locals)].
  intros observer READ; exact(proj1(word_observer_receipt_load READ)).
Qed.

(** A failed first comparison skips a deliberately undefined second test.
    This proves an actual Clight check path, without a totality claim for
    the unvisited tree. The full observer service uses real read receipts. *)
Definition thp_refusal_observers :=
  [hd(ClightWordObserver(Econst_int Int.zero type_int32s)1%positive Ptrofs.zero Vundef)thp_observers;
   ClightWordObserver(Etempvar 99%positive(Tpointer type_int32s noattr))2%positive(Ptrofs.repr 4)Vundef].
Example thp_refusal_second_temp_missing : thp_temps!99%positive=None.
Proof. reflexivity. Qed.
Theorem thp_alias_refusal_skips_undefined_test ge locals : decision_run(Entry ge locals thp_temps thp_memory)
  (direct_word_observer_tree(fun _=>None)11%positive(Econst_int Int.zero type_int32s)thp_refusal_observers)false.
Proof.
  destruct thp_header_reads as [ROOT CHILD].
  pose proof(@loaded_address_valid _ _ _ _ _ ROOT)as VALID.
  assert(FIRST:eval_expr ge locals thp_temps thp_memory
    (direct_word_address 11%positive(Econst_int Int.zero type_int32s))(Vptr 1%positive Ptrofs.zero)).
  { eapply eval_Ebinop; [apply eval_Etempvar; reflexivity|constructor|reflexivity]. }
  pose proof(@memory_pointer_cells_test_evaluation ge locals thp_temps thp_memory
    (direct_word_address 11%positive(Econst_int Int.zero type_int32s))(signed_pointer_temp 11%positive)
    1%positive Ptrofs.zero 1%positive Ptrofs.zero eq_refl eq_refl FIRST
    ltac:(apply eval_Etempvar; reflexivity)VALID VALID)as TEST.
  change(expression_test
    (memory_pointer_cells_test(direct_word_address 11%positive(Econst_int Int.zero type_int32s))
      (signed_pointer_temp 11%positive))(Entry ge locals thp_temps thp_memory)false)in TEST.
  eapply run_test with(b:=false); [exact TEST|constructor].
Qed.
Theorem thp_actual_alias_check_statement fe ge locals : exec_stmt fe ge locals thp_temps thp_memory
  (direct_word_check_code(fun _=>None)11%positive(Econst_int Int.zero type_int32s)thp_refusal_observers 108%positive)
  E0(PTree.set 108%positive(Vint Int.zero)thp_temps)thp_memory Out_normal.
Proof.
  unfold direct_word_check_code; eapply decision_fragment_run;
    [apply thp_alias_refusal_skips_undefined_test|constructor; constructor].
Qed.

Print Assumptions thp_dynamic_product_recognized.
Print Assumptions thp_index_arithmetic.
Print Assumptions thp_load_not_transportable.
Print Assumptions thp_division_not_transportable.
Print Assumptions thp_wrap_is_not_mathematical.
Print Assumptions thp_header_reads.
Print Assumptions thp_data_read.
Print Assumptions thp_index_evaluation.
Print Assumptions thp_address_evaluation.
Print Assumptions thp_actual_wrapping_rmw.
Print Assumptions thp_observer_receipts.
Print Assumptions thp_actual_separation_check.
Print Assumptions thp_point_domain.
Print Assumptions thp_acceptance_preserves_both_headers.
Print Assumptions thp_refusal_second_temp_missing.
Print Assumptions thp_alias_refusal_skips_undefined_test.
Print Assumptions thp_actual_alias_check_statement.
