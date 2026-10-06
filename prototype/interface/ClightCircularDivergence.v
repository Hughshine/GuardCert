From Stdlib Require Import List Bool ZArith Lia Wellfounded.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Smallstep.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightSameAddress.
From GuardInterface Require Import ClightCircularMachine ClightCircularGuard ClightCircularPrefix
  ClightReadonlyCellSwap.
Set Implicit Arguments.
Local Open Scope Z_scope.

Lemma circular_increment_apart word : Int.add word Int.one <> word.
Proof.
  intro SAME; pose proof (f_equal (fun value => Int.sub value word) SAME) as GAP.
  change (Int.sub (Int.add word Int.one) word = Int.sub word word) in GAP.
  rewrite Int.sub_add_l, !Int.sub_idem in GAP; vm_compute in GAP; discriminate.
Qed.
Lemma circular_next_bound word :
  Int.add word (Int.repr 2) = Int.add (Int.add word Int.one) Int.one.
Proof. rewrite Int.add_assoc; f_equal; vm_compute; reflexivity. Qed.

Lemma circular_silent_prefix_diverges temps ge first last :
  star (adapter_step temps) ge first E0 last ->
  forever_silent (adapter_step temps) ge last -> forever_silent (adapter_step temps) ge first.
Proof.
  intro RUN; pattern first, last; eapply star_E0_ind; [| |exact RUN].
  - intros state INFINITE; exact INFINITE.
  - intros before middle final STEP IH INFINITE.
    eapply forever_silent_intro; [exact STEP | apply IH; exact INFINITE].
Qed.

Section ALIAS.
Variable iterator out bound : ident.
Hypothesis ITER_OUT : iterator <> out.
Hypothesis ITER_BOUND : iterator <> bound.
Variable temps : bool.
Variable ge : genv.
Variable fn : function.
Variable outside : cont.
Variable locals : env.
Let head := circular_loaded_test iterator bound.

Lemma circular_alias_store le m word b ofs :
  le ! iterator = Some (Vint word) -> le ! out = Some (Vptr b ofs) -> writable_word m b ofs ->
  exists final,
    exec_stmt (adapter_entry temps) ge locals le m (circular_store out iterator) E0 le final Out_normal /\
    writable_word final b ofs /\
    Mem.loadv Mint32 final (Vptr b ofs) = Some (Vint (Int.add word (Int.repr 2))).
Proof.
  intros ITER OUT [VALID RANGE].
  destruct (Mem.valid_access_store m Mint32 b (Ptrofs.unsigned ofs)
    (Vint (Int.add word (Int.repr 2))) VALID) as [final STORE].
  exists final; split.
  - eapply exec_Sassign with (loc := b) (ofs := ofs) (bf := Full)
      (v2 := Vint (Int.add word (Int.repr 2))) (v := Vint (Int.add word (Int.repr 2))).
    + apply eval_Ederef, eval_Etempvar; exact OUT.
    + eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint (Int.repr 2));
        [apply eval_Etempvar; exact ITER | constructor | reflexivity].
    + reflexivity.
    + apply assign_loc_value with (chunk := Mint32); [reflexivity |].
      apply word_storev_from_store; [split; assumption | exact STORE].
  - split.
    + split; [eapply Mem.store_valid_access_1; eassumption | exact RANGE].
    + cbn [Mem.loadv]; rewrite zle_true by exact RANGE.
      exact (Mem.load_store_same _ _ _ _ _ _ STORE).
Qed.

Lemma circular_alias_head le m word upper b ofs :
  le ! iterator = Some (Vint word) -> le ! bound = Some (Vptr b ofs) ->
  Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint upper) -> word <> upper ->
  expression_test head (Entry ge locals le m) true.
Proof.
  intros ITER BOUND READ APART.
  pose proof (@circular_head_entry_test iterator bound (Entry ge locals le m)
    ltac:(exists word, upper, b, ofs; auto)) as TEST.
  unfold circular_head_flag in TEST; cbn [entry_temps entry_memory] in TEST; rewrite ITER, BOUND, READ in TEST.
  assert (NE : Int.eq word upper = false).
  { pose proof (Int.eq_spec word upper); destruct (Int.eq word upper); [contradiction | reflexivity]. }
  rewrite NE in TEST; exact TEST.
Qed.

Lemma circular_after_store_cycle le m word : le ! iterator = Some (Vint word) ->
  star (adapter_step temps) ge
    (circular_machine_state iterator out fn outside locals head cm_after_store le m) E0
    (circular_machine_state iterator out fn outside locals head cm_start
      (PTree.set iterator (Vint (Int.add word Int.one)) le) m).
Proof.
  intro ITER.
  eapply star_step; [apply circular_machine_step_sound; constructor | |reflexivity].
  eapply star_step; [apply circular_machine_step_sound; constructor | |reflexivity].
  eapply star_step; [apply circular_machine_step_sound; constructor | |reflexivity].
  eapply star_step; [apply circular_machine_step_sound; constructor | |reflexivity].
  - eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint Int.one);
      [apply eval_Etempvar; exact ITER | constructor | reflexivity].
  - apply star_one; apply circular_machine_step_sound; constructor.
Qed.

Lemma circular_alias_cycle le m word upper b ofs :
  le ! iterator = Some (Vint word) -> le ! out = Some (Vptr b ofs) -> le ! bound = Some (Vptr b ofs) ->
  writable_word m b ofs -> Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint upper) -> word <> upper ->
  exists final,
    plus (adapter_step temps) ge
      (circular_machine_state iterator out fn outside locals head cm_start le m) E0
      (circular_machine_state iterator out fn outside locals head cm_start
        (PTree.set iterator (Vint (Int.add word Int.one)) le) final) /\
    writable_word final b ofs /\
    Mem.loadv Mint32 final (Vptr b ofs) = Some (Vint (Int.add (Int.add word Int.one) Int.one)).
Proof.
  intros ITER OUT BOUND WRITABLE READ APART.
  destruct (@circular_alias_store le m word b ofs ITER OUT WRITABLE) as [final [STORE [NEXT LOAD]]].
  pose proof (@circular_prefix_store iterator out temps ge fn outside locals head le m final
    (@circular_alias_head le m word upper b ofs ITER BOUND READ APART) STORE) as PREFIX.
  assert (POSITIVE : plus (adapter_step temps) ge
    (circular_machine_state iterator out fn outside locals head cm_start le m) E0
    (circular_machine_state iterator out fn outside locals head cm_after_store le final)).
  { destruct (star_inv PREFIX) as [[SAME TRACE]|RUN]; [discriminate SAME | exact RUN]. }
  exists final; split.
  - eapply plus_star_trans; [exact POSITIVE | apply circular_after_store_cycle; exact ITER |reflexivity].
  - split; [exact NEXT | rewrite <- circular_next_bound; exact LOAD].
Qed.

Lemma circular_alias_infinite le m word upper b ofs :
  le ! iterator = Some (Vint word) -> le ! out = Some (Vptr b ofs) -> le ! bound = Some (Vptr b ofs) ->
  writable_word m b ofs -> Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint upper) -> word <> upper ->
  forever_silent_N (adapter_step temps) lt ge 0%nat
    (circular_machine_state iterator out fn outside locals head cm_start le m).
Proof.
  revert le m word upper b ofs; cofix FOREVER; intros le m word upper b ofs ITER OUT BOUND WRITABLE READ APART.
  destruct (@circular_alias_cycle le m word upper b ofs ITER OUT BOUND WRITABLE READ APART) as [final [RUN [NEXT LOAD]]].
  eapply forever_silent_N_plus with (a2 := 0%nat); [exact RUN |].
  eapply FOREVER with (word := Int.add word Int.one); [apply PTree.gss | | |exact NEXT |exact LOAD |].
  - rewrite PTree.gso by exact (not_eq_sym ITER_OUT); exact OUT.
  - rewrite PTree.gso by exact (not_eq_sym ITER_BOUND); exact BOUND.
  - exact (not_eq_sym (@circular_increment_apart (Int.add word Int.one))).
Qed.

Theorem circular_alias_source_diverges le m word upper b ofs :
  le ! iterator = Some (Vint word) -> le ! out = Some (Vptr b ofs) -> le ! bound = Some (Vptr b ofs) ->
  writable_word m b ofs -> Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint upper) -> word <> upper ->
  forever_silent (adapter_step temps) ge
    (State fn (circular_memory_loop iterator out head) outside locals le m).
Proof.
  intros ITER OUT BOUND WRITABLE READ APART.
  apply forever_silent_N_forever with (order := lt) (a := 0%nat); [apply lt_wf |].
  eapply circular_alias_infinite; eassumption.
Qed.

Theorem circular_alias_guarded_diverges cache le m word upper b ofs :
  le ! iterator = Some (Vint word) -> le ! out = Some (Vptr b ofs) -> le ! bound = Some (Vptr b ofs) ->
  writable_word m b ofs -> Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint upper) -> word <> upper ->
  forever_silent (adapter_step temps) ge
    (State fn (guarded_circular_region iterator out bound cache) outside locals le m).
Proof.
  intros ITER OUT BOUND WRITABLE READ APART.
  pose proof (@circular_alias_head le m word upper b ofs ITER BOUND READ APART) as HEAD.
  assert (DOMAIN : address_domain out bound (Entry ge locals le m)).
  { exists b, ofs, b, ofs; split; [exact OUT | split; [exact BOUND | split]];
      apply writable_word_valid_pointer; exact WRITABLE. }
  assert (ALIAS : expression_test (same_address_guard out bound) (Entry ge locals le m) true).
  { apply (proj2 (@address_guard_correct out bound (Entry ge locals le m) true DOMAIN)).
    unfold address_accept; cbn [entry_temps]; rewrite OUT, BOUND; unfold address_flag.
    rewrite Pos.eqb_refl, Ptrofs.eq_true; reflexivity. }
  destruct (@circular_alias_store le m word b ofs ITER OUT WRITABLE) as [final [STORE [NEXT LOAD]]].
  eapply circular_silent_prefix_diverges.
  - eapply circular_guard_alias; [exact HEAD | exact ALIAS | exact STORE].
  - eapply circular_silent_prefix_diverges; [apply circular_after_store_cycle; exact ITER |].
    eapply circular_alias_source_diverges with (word := Int.add word Int.one) (upper := Int.add word (Int.repr 2)).
    + apply PTree.gss.
    + rewrite PTree.gso by exact (not_eq_sym ITER_OUT); exact OUT.
    + rewrite PTree.gso by exact (not_eq_sym ITER_BOUND); exact BOUND.
    + exact NEXT.
    + exact LOAD.
    + rewrite circular_next_bound; exact (not_eq_sym (@circular_increment_apart (Int.add word Int.one))).
Qed.
End ALIAS.

Print Assumptions circular_increment_apart.
Print Assumptions circular_alias_cycle.
Print Assumptions circular_alias_source_diverges.
Print Assumptions circular_alias_guarded_diverges.
