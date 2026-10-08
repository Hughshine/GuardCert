(** Real intermediate memories: an initializing first store licenses the
    second RHS, while a second-store/header alias is refused. *)
From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightStraightLine.
From GuardInterface Require Import ClightWordArithmeticTransport ClightWordCoordinateRename
  ClightDirectWordObservation ClightAffineJointObservation ClightObservedHeaderPrefix
  ClightStorePermissions ClightWordStoreSequence ClightWordStoreSequenceFactory
  ClightWordStoreSequenceLoaded ClightLoadedOffsetHeader ClightLoadedBoundSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition sequence_demo_zero := Econst_int Int.zero type_int32s.
Definition sequence_demo_rhs source delta :=
  Ebinop Oadd (Ederef (Etempvar source (Tpointer type_int32s noattr)) type_int32s)
    (Econst_int delta type_int32s) type_int32s.
Definition sequence_demo_sites delta :=
  [WordStoreSite 9%positive sequence_demo_zero (sequence_demo_rhs 10%positive delta);
   WordStoreSite 10%positive sequence_demo_zero (sequence_demo_rhs 9%positive delta)].
Definition sequence_demo_body delta :=
  Ssequence (word_store_site_code (hd (WordStoreSite 1%positive sequence_demo_zero sequence_demo_zero)
    (sequence_demo_sites delta)))
    (word_store_site_code (hd (WordStoreSite 1%positive sequence_demo_zero sequence_demo_zero)
      (tl (sequence_demo_sites delta)))).

Definition sequence_demo_alloc := fst (Mem.alloc Mem.empty 0 12).
Definition sequence_demo_write memory offset word :=
  match Mem.store Mint32 memory 1%positive offset (Vint word) with
  | Some written => written | None => memory end.
Definition sequence_demo_memory := sequence_demo_write
  (sequence_demo_write sequence_demo_alloc 0 Int.one) 8 (Int.repr 5).
Definition sequence_demo_middle := sequence_demo_write sequence_demo_memory 4 (Int.repr 8).
Definition sequence_demo_final := sequence_demo_write sequence_demo_middle 8 (Int.repr 11).
Definition sequence_demo_alias_memory := sequence_demo_write sequence_demo_alloc 0 (Int.repr 2).
Definition sequence_demo_alias_middle := sequence_demo_write sequence_demo_alias_memory 4 Int.zero.
Definition sequence_demo_alias_final := sequence_demo_write sequence_demo_alias_middle 0 (Int.repr (-2)).
Definition sequence_demo_temps second_offset :=
  PTree.set 11%positive (Vptr 1%positive Ptrofs.zero)
    (PTree.set 10%positive (Vptr 1%positive (Ptrofs.repr second_offset))
      (PTree.set 9%positive (Vptr 1%positive (Ptrofs.repr 4))
        (PTree.set 2%positive (Vint Int.one)
          (PTree.set 1%positive (Vint Int.zero) (PTree.empty val))))).
Definition sequence_demo_observers value :=
  [ClightWordObserver (signed_pointer_temp 11%positive) 1%positive Ptrofs.zero (Vint value)].

Definition sequence_demo_cells memory :=
  forall offset, In offset [0;4;8] -> Mem.valid_access memory Mint32 1%positive offset Writable.
Lemma sequence_demo_alloc_cells : sequence_demo_cells sequence_demo_alloc.
Proof.
  intros offset MEMBER.
  assert (RANGE : 0 <= offset /\ offset + size_chunk Mint32 <= 12).
  { cbn in MEMBER |- *; intuition lia. }
  assert (ALIGN : (align_chunk Mint32 | offset)).
  { cbn in MEMBER |- *; destruct MEMBER as [SAME|[SAME|[SAME|BAD]]];
      try contradiction; subst offset; [exists 0|exists 1|exists 2]; reflexivity. }
  eapply Mem.valid_access_implies.
  - exact (@Mem.valid_access_alloc_same Mem.empty 0 12 sequence_demo_alloc 1%positive
      eq_refl Mint32 offset (proj1 RANGE) (proj2 RANGE) ALIGN).
  - constructor.
Qed.
Lemma sequence_demo_write_success memory offset word :
  Mem.valid_access memory Mint32 1%positive offset Writable ->
  Mem.store Mint32 memory 1%positive offset (Vint word) = Some (sequence_demo_write memory offset word).
Proof.
  intro ACCESS; destruct (@Mem.valid_access_store memory Mint32 1%positive offset (Vint word) ACCESS)
    as [written STORE]; unfold sequence_demo_write; rewrite STORE; reflexivity.
Qed.
Lemma sequence_demo_write_cells memory offset word :
  sequence_demo_cells memory -> In offset [0;4;8] ->
  sequence_demo_cells (sequence_demo_write memory offset word).
Proof.
  intros CELLS MEMBER wanted LIVE; eapply Mem.store_valid_access_1;
    [apply sequence_demo_write_success; apply CELLS; exact MEMBER|apply CELLS; exact LIVE].
Qed.
Lemma sequence_demo_memory_cells : sequence_demo_cells sequence_demo_memory.
Proof.
  unfold sequence_demo_memory; apply sequence_demo_write_cells; [|cbn; tauto].
  apply sequence_demo_write_cells; [apply sequence_demo_alloc_cells|cbn; tauto].
Qed.
Lemma sequence_demo_middle_cells : sequence_demo_cells sequence_demo_middle.
Proof. apply sequence_demo_write_cells; [apply sequence_demo_memory_cells|cbn; tauto]. Qed.
Lemma sequence_demo_alias_memory_cells : sequence_demo_cells sequence_demo_alias_memory.
Proof. apply sequence_demo_write_cells; [apply sequence_demo_alloc_cells|cbn; tauto]. Qed.
Lemma sequence_demo_alias_middle_cells : sequence_demo_cells sequence_demo_alias_middle.
Proof. apply sequence_demo_write_cells; [apply sequence_demo_alias_memory_cells|cbn; tauto]. Qed.

Lemma sequence_demo_write_same memory offset word :
  sequence_demo_cells memory -> In offset [0;4;8] ->
  Mem.load Mint32 (sequence_demo_write memory offset word) 1%positive offset = Some (Vint word).
Proof.
  intros CELLS MEMBER; exact (@Mem.load_store_same Mint32 memory 1%positive offset (Vint word)
    (sequence_demo_write memory offset word) (sequence_demo_write_success word (CELLS offset MEMBER))).
Qed.
Lemma sequence_demo_write_other memory offset word wanted :
  sequence_demo_cells memory -> In offset [0;4;8] ->
  wanted + 4 <= offset \/ offset + 4 <= wanted ->
  Mem.load Mint32 (sequence_demo_write memory offset word) 1%positive wanted =
    Mem.load Mint32 memory 1%positive wanted.
Proof.
  intros CELLS MEMBER APART; eapply Mem.load_store_other;
    [apply sequence_demo_write_success; apply CELLS; exact MEMBER|cbn; tauto].
Qed.
Lemma sequence_demo_loadv memory offset value :
  In offset [0;4;8] -> Mem.load Mint32 memory 1%positive offset = Some value ->
  Mem.loadv Mint32 memory (Vptr 1%positive (Ptrofs.repr offset)) = Some value.
Proof.
  intros MEMBER LOAD; unfold Mem.loadv.
  rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;
    cbn in MEMBER; intuition lia).
  rewrite zle_true by (change Ptrofs.modulus with 18446744073709551616;
    cbn in MEMBER |- *; intuition lia); exact LOAD.
Qed.
Lemma sequence_demo_storev memory offset word :
  sequence_demo_cells memory -> In offset [0;4;8] ->
  Mem.storev Mint32 memory (Vptr 1%positive (Ptrofs.repr offset)) (Vint word) =
    Some (sequence_demo_write memory offset word).
Proof.
  intros CELLS MEMBER; unfold Mem.storev.
  rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;
    cbn in MEMBER; intuition lia).
  rewrite zle_true by (change Ptrofs.modulus with 18446744073709551616;
    cbn in MEMBER |- *; intuition lia); apply sequence_demo_write_success; apply CELLS; exact MEMBER.
Qed.
Lemma sequence_demo_memory_header :
  Mem.load Mint32 sequence_demo_memory 1%positive 0 = Some (Vint Int.one).
Proof.
  unfold sequence_demo_memory; rewrite sequence_demo_write_other;
    [apply sequence_demo_write_same; [apply sequence_demo_alloc_cells|cbn; tauto]| |cbn; tauto|lia].
  apply sequence_demo_write_cells; [apply sequence_demo_alloc_cells|cbn; tauto].
Qed.
Lemma sequence_demo_memory_B : Mem.load Mint32 sequence_demo_memory 1%positive 8 = Some (Vint (Int.repr 5)).
Proof.
  apply sequence_demo_write_same; [|cbn; tauto].
  apply sequence_demo_write_cells; [apply sequence_demo_alloc_cells|cbn; tauto].
Qed.
Lemma sequence_demo_middle_A : Mem.load Mint32 sequence_demo_middle 1%positive 4 = Some (Vint (Int.repr 8)).
Proof. apply sequence_demo_write_same; [apply sequence_demo_memory_cells|cbn; tauto]. Qed.
Lemma sequence_demo_alias_memory_header :
  Mem.load Mint32 sequence_demo_alias_memory 1%positive 0 = Some (Vint (Int.repr 2)).
Proof. apply sequence_demo_write_same; [apply sequence_demo_alloc_cells|cbn; tauto]. Qed.
Lemma sequence_demo_alias_middle_A :
  Mem.load Mint32 sequence_demo_alias_middle 1%positive 4 = Some (Vint Int.zero).
Proof. apply sequence_demo_write_same; [apply sequence_demo_alias_memory_cells|cbn; tauto]. Qed.

Example sequence_demo_checker_accepts delta :
  check_word_store_sites (flatten_region (sequence_demo_body delta)) = Some (sequence_demo_sites delta).
Proof. reflexivity. Qed.
Example sequence_demo_checker_reassociation delta :
  check_word_store_sites (flatten_region (Ssequence Sskip
    (Ssequence (sequence_demo_body delta) Sskip))) = Some (sequence_demo_sites delta).
Proof. reflexivity. Qed.
Example sequence_demo_checker_rejects_load_index :
  check_word_store_site (direct_word_store 9%positive
    (Ederef (Etempvar 11%positive (Tpointer type_int32s noattr)) type_int32s)
    sequence_demo_zero) = None.
Proof. reflexivity. Qed.
Example sequence_demo_checker_rejects_temp_assignment :
  check_word_store_body (Sset 9%positive sequence_demo_zero) = None.
Proof. reflexivity. Qed.

Lemma sequence_demo_store_execution fe ge locals temps memory destination source delta block
    destination_offset source_offset raw final :
  temps!destination = Some (Vptr block destination_offset) ->
  temps!source = Some (Vptr block source_offset) ->
  Mem.loadv Mint32 memory (Vptr block source_offset) = Some (Vint raw) ->
  Mem.storev Mint32 memory (Vptr block destination_offset) (Vint (Int.add raw delta)) = Some final ->
  exec_stmt fe ge locals temps memory
    (direct_word_store destination sequence_demo_zero (sequence_demo_rhs source delta))
    E0 temps final Out_normal.
Proof.
  intros DESTINATION SOURCE LOAD STORE; unfold direct_word_store,sequence_demo_rhs.
  eapply exec_Sassign with (loc:=block) (ofs:=destination_offset)
    (v:=Vint (Int.add raw delta)) (v2:=Vint (Int.add raw delta)) (bf:=Full).
  - apply eval_Ederef; unfold direct_word_address,sequence_demo_zero.
    eapply eval_Ebinop with (v1:=Vptr block destination_offset) (v2:=Vint Int.zero);
      [constructor; exact DESTINATION|constructor|].
    change (Some (Vptr block (Ptrofs.add destination_offset (Ptrofs.mul (Ptrofs.repr 4)
      (Ptrofs.repr (Int.signed Int.zero))))) = Some (Vptr block destination_offset)).
    rewrite Int.signed_zero; change (Ptrofs.repr 0) with Ptrofs.zero.
    rewrite Ptrofs.mul_zero,Ptrofs.add_zero; reflexivity.
  - eapply eval_Ebinop.
    + eapply eval_Elvalue; [apply eval_Ederef; constructor; exact SOURCE|].
      apply deref_loc_value with (chunk:=Mint32); [reflexivity|exact LOAD].
    + constructor.
    + reflexivity.
  - reflexivity.
  - apply assign_loc_value with (chunk:=Mint32); [reflexivity|exact STORE].
Qed.

Example sequence_demo_entry_A_is_undefined :
  Mem.load Mint32 sequence_demo_memory 1%positive 4 = Some Vundef /\
  (forall ge, sem_binary_operation ge Oadd Vundef type_int32s
    (Vint (Int.repr 3)) type_int32s sequence_demo_memory = None).
Proof.
  split; [|intro; reflexivity].
  unfold sequence_demo_memory; rewrite sequence_demo_write_other;
    [|apply sequence_demo_write_cells; [apply sequence_demo_alloc_cells|cbn; tauto]|cbn; tauto|lia].
  rewrite sequence_demo_write_other; [|apply sequence_demo_alloc_cells|cbn; tauto|lia].
  exact (@Mem.load_alloc_same' Mem.empty 0 12 sequence_demo_alloc 1%positive eq_refl
    Mint32 4 ltac:(lia) ltac:(cbn; lia) ltac:(exists 1; reflexivity)).
Qed.

Theorem sequence_demo_actual_source fe ge locals :
  exec_stmt fe ge locals (sequence_demo_temps 8) sequence_demo_memory
    (sequence_demo_body (Int.repr 3)) E0 (sequence_demo_temps 8) sequence_demo_final Out_normal.
Proof.
  unfold sequence_demo_body; cbn [sequence_demo_sites hd tl word_store_site_code].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=sequence_demo_temps 8) (m1:=sequence_demo_middle).
  - eapply sequence_demo_store_execution with (block:=1%positive)
      (destination_offset:=Ptrofs.repr 4) (source_offset:=Ptrofs.repr 8) (raw:=Int.repr 5);
      [reflexivity|reflexivity| |].
    + apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_memory_B].
    + change (Mem.storev Mint32 sequence_demo_memory (Vptr 1%positive (Ptrofs.repr 4))
        (Vint (Int.repr 8)) = Some sequence_demo_middle).
      apply sequence_demo_storev; [apply sequence_demo_memory_cells|cbn; tauto].
  - eapply sequence_demo_store_execution with (block:=1%positive)
      (destination_offset:=Ptrofs.repr 8) (source_offset:=Ptrofs.repr 4) (raw:=Int.repr 8);
      [reflexivity|reflexivity| |].
    + apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_middle_A].
    + change (Mem.storev Mint32 sequence_demo_middle (Vptr 1%positive (Ptrofs.repr 8))
        (Vint (Int.repr 11)) = Some sequence_demo_final).
      apply sequence_demo_storev; [apply sequence_demo_middle_cells|cbn; tauto].
Qed.

Theorem sequence_demo_alias_actual_source fe ge locals :
  exec_stmt fe ge locals (sequence_demo_temps 0) sequence_demo_alias_memory
    (sequence_demo_body (Int.repr (-2))) E0 (sequence_demo_temps 0) sequence_demo_alias_final Out_normal.
Proof.
  unfold sequence_demo_body; cbn [sequence_demo_sites hd tl word_store_site_code].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=sequence_demo_temps 0) (m1:=sequence_demo_alias_middle).
  - eapply sequence_demo_store_execution with (block:=1%positive)
      (destination_offset:=Ptrofs.repr 4) (source_offset:=Ptrofs.zero) (raw:=Int.repr 2);
      [reflexivity|reflexivity| |].
    + apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_alias_memory_header].
    + assert (WORD : Int.add (Int.repr 2) (Int.repr (-2)) = Int.zero) by
        (rewrite Int.add_signed; reflexivity).
      rewrite WORD.
      change (Mem.storev Mint32 sequence_demo_alias_memory (Vptr 1%positive (Ptrofs.repr 4))
        (Vint Int.zero) = Some sequence_demo_alias_middle).
      apply sequence_demo_storev; [apply sequence_demo_alias_memory_cells|cbn; tauto].
  - eapply sequence_demo_store_execution with (block:=1%positive)
      (destination_offset:=Ptrofs.zero) (source_offset:=Ptrofs.repr 4) (raw:=Int.zero);
      [reflexivity|reflexivity| |].
    + apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_alias_middle_A].
    + rewrite Int.add_zero_l.
      change (Mem.storev Mint32 sequence_demo_alias_middle (Vptr 1%positive Ptrofs.zero)
        (Vint (Int.repr (-2))) = Some sequence_demo_alias_final).
      apply sequence_demo_storev; [apply sequence_demo_alias_middle_cells|cbn; tauto].
Qed.

Example sequence_demo_header_and_arrays :
  Mem.load Mint32 sequence_demo_final 1%positive 0 = Some (Vint Int.one) /\
  Mem.load Mint32 sequence_demo_final 1%positive 4 = Some (Vint (Int.repr 8)) /\
  Mem.load Mint32 sequence_demo_final 1%positive 8 = Some (Vint (Int.repr 11)).
Proof.
  split.
  - unfold sequence_demo_final; rewrite sequence_demo_write_other;
      [|apply sequence_demo_middle_cells|cbn; tauto|lia].
    unfold sequence_demo_middle; rewrite sequence_demo_write_other;
      [apply sequence_demo_memory_header|apply sequence_demo_memory_cells|cbn; tauto|lia].
  - split.
    + unfold sequence_demo_final; rewrite sequence_demo_write_other;
        [apply sequence_demo_middle_A|apply sequence_demo_middle_cells|cbn; tauto|lia].
    + apply sequence_demo_write_same; [apply sequence_demo_middle_cells|cbn; tauto].
Qed.
Example sequence_demo_alias_changes_loaded_header :
  Mem.load Mint32 sequence_demo_alias_memory 1%positive 0 = Some (Vint (Int.repr 2)) /\
  Mem.load Mint32 sequence_demo_alias_final 1%positive 0 = Some (Vint (Int.repr (-2))).
Proof.
  split; [apply sequence_demo_alias_memory_header|].
  apply sequence_demo_write_same; [apply sequence_demo_alias_middle_cells|cbn; tauto].
Qed.

Lemma sequence_demo_frame delta offset :
  Forall (fun site => word_store_site_frame (fun id=>id) site
    (sequence_demo_temps offset) (sequence_demo_temps offset)) (sequence_demo_sites delta).
Proof. repeat constructor; intros id MEMBER; reflexivity. Qed.
Lemma sequence_demo_words delta :
  Forall (fun site => word_arithmetic (wss_index site)) (sequence_demo_sites delta).
Proof. repeat constructor. Qed.

Lemma sequence_demo_domain fe ge locals :
  word_store_sequence_domain fe (fun id=>id) (sequence_demo_sites (Int.repr 3))
    (sequence_demo_observers Int.one) (Entry ge locals (sequence_demo_temps 8) sequence_demo_memory).
Proof.
  eapply word_store_sequence_domain_from_body with (body:=sequence_demo_body (Int.repr 3))
    (current:=sequence_demo_temps 8) (memory:=sequence_demo_memory).
  - reflexivity.
  - constructor; [|constructor]. split; [reflexivity|split].
    + constructor; reflexivity.
    + apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_memory_header].
  - apply sequence_demo_frame.
  - apply memory_accesses_back_refl.
  - apply sequence_demo_actual_source.
Qed.
Lemma sequence_demo_alias_domain fe ge locals :
  word_store_sequence_domain fe (fun id=>id) (sequence_demo_sites (Int.repr (-2)))
    (sequence_demo_observers (Int.repr 2)) (Entry ge locals (sequence_demo_temps 0) sequence_demo_alias_memory).
Proof.
  eapply word_store_sequence_domain_from_body with (body:=sequence_demo_body (Int.repr (-2)))
    (current:=sequence_demo_temps 0) (memory:=sequence_demo_alias_memory).
  - reflexivity.
  - constructor; [|constructor]. split; [reflexivity|split].
    + constructor; reflexivity.
    + apply sequence_demo_loadv; [cbn; tauto|apply sequence_demo_alias_memory_header].
  - apply sequence_demo_frame.
  - apply memory_accesses_back_refl.
  - apply sequence_demo_alias_actual_source.
Qed.

Example sequence_demo_flag_accepts ge locals :
  word_store_sequence_flag (fun id=>id) (sequence_demo_sites (Int.repr 3))
    (sequence_demo_observers Int.one) (Entry ge locals (sequence_demo_temps 8) sequence_demo_memory) = true.
Proof. reflexivity. Qed.
Example sequence_demo_second_store_flag_refuses ge locals :
  word_store_sequence_flag (fun id=>id) (sequence_demo_sites (Int.repr (-2)))
    (sequence_demo_observers (Int.repr 2)) (Entry ge locals (sequence_demo_temps 0) sequence_demo_alias_memory) = false.
Proof. reflexivity. Qed.
Theorem sequence_demo_actual_check_accepts fe ge locals :
  exec_stmt fe ge locals (sequence_demo_temps 8) sequence_demo_memory
    (word_store_sequence_check_code (fun id=>id) (sequence_demo_sites (Int.repr 3))
      (sequence_demo_observers Int.one) 100%positive) E0
    (PTree.set 100%positive (Vint Int.one) (sequence_demo_temps 8)) sequence_demo_memory Out_normal.
Proof.
  exact (@word_store_sequence_check_execution fe (fun id=>id) (sequence_demo_sites (Int.repr 3))
    (sequence_demo_observers Int.one) (Entry ge locals (sequence_demo_temps 8) sequence_demo_memory)
    100%positive (sequence_demo_words _) (sequence_demo_domain fe ge locals)).
Qed.
Theorem sequence_demo_actual_check_refuses fe ge locals :
  exec_stmt fe ge locals (sequence_demo_temps 0) sequence_demo_alias_memory
    (word_store_sequence_check_code (fun id=>id) (sequence_demo_sites (Int.repr (-2)))
      (sequence_demo_observers (Int.repr 2)) 100%positive) E0
    (PTree.set 100%positive (Vint Int.zero) (sequence_demo_temps 0)) sequence_demo_alias_memory Out_normal.
Proof.
  exact (@word_store_sequence_check_execution fe (fun id=>id) (sequence_demo_sites (Int.repr (-2)))
    (sequence_demo_observers (Int.repr 2)) (Entry ge locals (sequence_demo_temps 0) sequence_demo_alias_memory)
    100%positive (sequence_demo_words _) (sequence_demo_alias_domain fe ge locals)).
Qed.

Theorem sequence_demo_accepted_preserves_header fe ge locals :
  word_store_sequence_preserved fe (fun id=>id) (sequence_demo_sites (Int.repr 3))
    (sequence_demo_observers Int.one) (Entry ge locals (sequence_demo_temps 8) sequence_demo_memory).
Proof.
  eapply word_store_sequence_sound; [apply sequence_demo_words|apply sequence_demo_domain|reflexivity].
Qed.

Print Assumptions sequence_demo_checker_accepts.
Print Assumptions sequence_demo_checker_reassociation.
Print Assumptions sequence_demo_checker_rejects_load_index.
Print Assumptions sequence_demo_checker_rejects_temp_assignment.
Print Assumptions sequence_demo_store_execution.
Print Assumptions sequence_demo_entry_A_is_undefined.
Print Assumptions sequence_demo_actual_source.
Print Assumptions sequence_demo_alias_actual_source.
Print Assumptions sequence_demo_header_and_arrays.
Print Assumptions sequence_demo_alias_changes_loaded_header.
Print Assumptions sequence_demo_frame.
Print Assumptions sequence_demo_words.
Print Assumptions sequence_demo_domain.
Print Assumptions sequence_demo_alias_domain.
Print Assumptions sequence_demo_flag_accepts.
Print Assumptions sequence_demo_second_store_flag_refuses.
Print Assumptions sequence_demo_actual_check_accepts.
Print Assumptions sequence_demo_actual_check_refuses.
Print Assumptions sequence_demo_accepted_preserves_header.
