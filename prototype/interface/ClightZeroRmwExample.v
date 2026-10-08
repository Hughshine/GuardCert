From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes Cop ClightBigstep.
From Guard Require Import ClightCondition ClightRedundantSet ClightSameAddress.
From GuardInterface Require Import ClightZeroRmwObservation ClightZeroRmwCondition
  ClightTensorHeaderPointExample ClightTensorLoadedWordFactoryExample ClightDirectWordObservation
  ClightWordArithmeticTransport ClightAffineJointObservation ClightNestedConstantHeaders
  ClightObservedHeaderPrefix ClightSignedIndexedOffsetHeader ClightNestedConstantSite
  ClightNestedIndexedObservers.
Import ListNotations.
Local Open Scope Z_scope.

Example zero_rmw_horner_source_checked : check_zero_rmw_control 5%positive(ncs_original lwf_shape)=true.
Proof. vm_compute; reflexivity. Qed.
Example zero_rmw_increment_write_refused :
  check_zero_rmw_control 5%positive(Ssequence(ncs_original lwf_shape)
    (Sset 5%positive(Econst_int Int.one type_int32s)))=false.
Proof. vm_compute; reflexivity. Qed.
Example zero_rmw_changed_value_refused :
  check_zero_rmw_control 7%positive(direct_word_store 10%positive(Econst_int Int.zero type_int32s)
    (Econst_int Int.zero type_int32s))=false.
Proof. vm_compute; reflexivity. Qed.

(** Two distinct raw header words; the first output is the root header itself.
    Reuse only the earlier allocated memory/permission fixture. *)
Definition zr_root_state : {memory|Mem.store Mint32 thp_allocated 1%positive 0(Vint(Int.repr 2))=Some memory}.
Proof. apply Mem.valid_access_store,thp_allocated_access; try lia; exists 0; reflexivity. Defined.
Definition zr_root := proj1_sig zr_root_state.
Definition zr_child_state : {memory|Mem.store Mint32 zr_root 1%positive 4(Vint(Int.repr 3))=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig zr_root_state)|].
  apply thp_allocated_access; try lia; exists 1; reflexivity.
Defined.
Definition zr_memory := proj1_sig zr_child_state.
Definition zr_final_state : {memory|Mem.store Mint32 zr_memory 1%positive 0(Vint(Int.repr 2))=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig zr_child_state)|].
  eapply Mem.store_valid_access_1; [exact(proj2_sig zr_root_state)|].
  apply thp_allocated_access; try lia; exists 0; reflexivity.
Defined.
Definition zr_final := proj1_sig zr_final_state.
Definition zr_temps alpha := PTree.set 7%positive(Vint alpha)
  (PTree.set 10%positive(Vptr 1%positive Ptrofs.zero)
    (PTree.set 11%positive(Vptr 1%positive Ptrofs.zero)(PTree.empty val))).
Definition zr_index := Econst_int Int.zero type_int32s.
Definition zr_cell := Ederef(direct_word_address 10%positive zr_index)type_int32s.
Definition zr_body := direct_word_store 10%positive zr_index(zero_rmw_rhs 7%positive zr_cell).
Definition zr_observers := ncs_observers thp_shape 1%positive Ptrofs.zero(Int.repr 2)(Int.repr 3).

Lemma zr_header_reads :
  Mem.loadv Mint32 zr_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint(Int.repr 2)) /\
  Mem.loadv Mint32 zr_memory(Vptr 1%positive(Ptrofs.repr 4))=Some(Vint(Int.repr 3)).
Proof.
  change(Mem.load Mint32 zr_memory 1%positive 0=Some(Vint(Int.repr 2)) /\
    Mem.load Mint32 zr_memory 1%positive 4=Some(Vint(Int.repr 3))); split.
  - erewrite Mem.load_store_other; [|exact(proj2_sig zr_child_state)|cbn; right; lia].
    change(Some(Vint(Int.repr 2)))with(Some(Val.load_result Mint32(Vint(Int.repr 2)))).
    eapply Mem.load_store_same; exact(proj2_sig zr_root_state).
  - change(Some(Vint(Int.repr 3)))with(Some(Val.load_result Mint32(Vint(Int.repr 3)))).
    eapply Mem.load_store_same; exact(proj2_sig zr_child_state).
Qed.
Lemma zr_address ge locals memory alpha : eval_expr ge locals(zr_temps alpha)memory
  (direct_word_address 10%positive zr_index)(Vptr 1%positive Ptrofs.zero).
Proof. eapply eval_Ebinop; [constructor; reflexivity|constructor|reflexivity]. Qed.
Theorem zr_actual_aliasing_zero_rmw fe ge locals :
  exec_stmt fe ge locals(zr_temps Int.zero)zr_memory zr_body E0(zr_temps Int.zero)zr_final Out_normal.
Proof.
  unfold zr_body,direct_word_store; eapply exec_Sassign with(v2:=Vint(Int.repr 2))(v:=Vint(Int.repr 2)).
  - apply eval_Ederef,zr_address.
  - unfold zero_rmw_rhs; eapply eval_Ebinop with(v1:=Vint(Int.repr 2))(v2:=Vint Int.zero);
      [|constructor; reflexivity|reflexivity].
    eapply eval_Elvalue with(loc:=1%positive)(ofs:=Ptrofs.zero)(bf:=Full);
      [apply eval_Ederef,zr_address|].
    apply deref_loc_value with(chunk:=Mint32); [reflexivity|exact(proj1 zr_header_reads)].
  - reflexivity.
  - apply assign_loc_value with(chunk:=Mint32); [reflexivity|exact(proj2_sig zr_final_state)].
Qed.
Theorem zr_new_constant_condition_accepts ge locals :
  decision_run(Entry ge locals(zr_temps Int.zero)zr_memory)(zero_rmw_condition 7%positive)true.
Proof. change true with(register_flag 7%positive Int.zero(Entry ge locals(zr_temps Int.zero)zr_memory)).
  apply register_tree_run; exists Int.zero; reflexivity. Qed.
Theorem zr_new_constant_condition_refuses_nonzero ge locals :
  decision_run(Entry ge locals(zr_temps Int.one)zr_memory)(zero_rmw_condition 7%positive)false.
Proof. change false with(register_flag 7%positive Int.zero(Entry ge locals(zr_temps Int.one)zr_memory)).
  apply register_tree_run; exists Int.one; reflexivity. Qed.
Theorem zr_old_separation_condition_refuses ge locals :
  decision_run(Entry ge locals(zr_temps Int.zero)zr_memory)
    (direct_word_observer_tree(fun _=>None)10%positive zr_index zr_observers)false.
Proof.
  change false with(forallb(direct_word_observer_flag 1%positive Ptrofs.zero)zr_observers).
  eapply direct_word_observer_tree_execution.
  - constructor.
  - apply zr_address.
  - eapply loaded_address_valid; exact(proj1 zr_header_reads).
  - unfold zr_observers,ncs_observers,nested_indexed_word_observers; constructor.
    + split; [reflexivity|split; [constructor; reflexivity|exact(proj1 zr_header_reads)]].
    + constructor; [|constructor]; split; [reflexivity|split; [|exact(proj2 zr_header_reads)]].
      exact(@signed_indexed_pointer_eval ge locals(zr_temps Int.zero)zr_memory 11%positive Int.one
        1%positive Ptrofs.zero eq_refl).
Qed.
Theorem zr_distinct_headers_preserved
  (fe:genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)(ge:genv)(locals:env) :
  Mem.loadv Mint32 zr_final(Vptr 1%positive Ptrofs.zero)=Some(Vint(Int.repr 2)) /\
  Mem.loadv Mint32 zr_final(Vptr 1%positive(Ptrofs.repr 4))=Some(Vint(Int.repr 3)).
Proof.
  pose proof(@checked_zero_rmw_control_execution 7%positive fe ge locals(zr_temps Int.zero)zr_memory zr_body
    E0(zr_temps Int.zero)zr_final Out_normal(zr_actual_aliasing_zero_rmw fe ge locals)eq_refl eq_refl)as [PRESERVED _].
  change(Mem.load Mint32 zr_final 1%positive 0=Some(Vint(Int.repr 2)) /\
    Mem.load Mint32 zr_final 1%positive 4=Some(Vint(Int.repr 3))).
  destruct zr_header_reads as [ROOT CHILD]; split; apply PRESERVED; assumption.
Qed.

Print Assumptions zero_rmw_horner_source_checked.
Print Assumptions zero_rmw_increment_write_refused.
Print Assumptions zero_rmw_changed_value_refused.
Print Assumptions zr_actual_aliasing_zero_rmw.
Print Assumptions zr_new_constant_condition_accepts.
Print Assumptions zr_new_constant_condition_refuses_nonzero.
Print Assumptions zr_old_separation_condition_refuses.
Print Assumptions zr_distinct_headers_preserved.
