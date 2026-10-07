From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A sufficient memory condition distinct from non-aliasing: an aligned
    Mint32 store of the observed word preserves a Mint32 observation even
    when it writes the very same cell. Successful loads/stores provide the
    alignment facts; this statement does not apply to partial-byte stores. *)
Theorem mint32_store_preserves_equal_word before after word block offset observed_block observed_offset :
  Mem.load Mint32 before observed_block observed_offset = Some (Vint word) ->
  Mem.store Mint32 before block offset (Vint word) = Some after ->
  Mem.load Mint32 after observed_block observed_offset = Some (Vint word).
Proof.
  intros LOAD STORE.
  destruct (peq observed_block block) as [SAME_BLOCK|OTHER_BLOCK].
  - subst observed_block.
    destruct (Z.eq_dec observed_offset offset) as [SAME_OFFSET|OTHER_OFFSET].
    + subst observed_offset; change (Some (Vint word)) with (Some (Val.load_result Mint32 (Vint word))).
      eapply Mem.load_store_same; exact STORE.
    + pose proof (Mem.load_valid_access _ _ _ _ _ LOAD) as LOAD_ACCESS.
      pose proof (Mem.store_valid_access_3 _ _ _ _ _ _ STORE) as STORE_ACCESS.
      destruct LOAD_ACCESS as [_ [read_multiple READ_ALIGN]].
      destruct STORE_ACCESS as [_ [write_multiple WRITE_ALIGN]].
      cbn [align_chunk] in READ_ALIGN, WRITE_ALIGN.
      erewrite Mem.load_store_other; [exact LOAD|exact STORE|].
      cbn [size_chunk]; right; lia.
  - erewrite Mem.load_store_other; [exact LOAD|exact STORE|].
    left; exact OTHER_BLOCK.
Qed.

Inductive constant_word_stores (word : int) : mem -> mem -> Prop :=
| constant_word_stores_none : forall memory, constant_word_stores word memory memory
| constant_word_stores_next : forall before block offset middle after,
    Mem.store Mint32 before block offset (Vint word) = Some middle ->
    constant_word_stores word middle after ->
    constant_word_stores word before after.

Theorem constant_word_stores_preserve_observation word before after block offset :
  constant_word_stores word before after ->
  Mem.load Mint32 before block offset = Some (Vint word) ->
  Mem.load Mint32 after block offset = Some (Vint word).
Proof.
  intros STORES; induction STORES; intro LOAD; [exact LOAD|].
  apply IHSTORES; eapply mint32_store_preserves_equal_word; eassumption.
Qed.

Theorem constant_word_stores_preserve_two_observations word before after b1 o1 b2 o2 :
  constant_word_stores word before after ->
  Mem.load Mint32 before b1 o1 = Some (Vint word) ->
  Mem.load Mint32 before b2 o2 = Some (Vint word) ->
  Mem.load Mint32 after b1 o1 = Some (Vint word) /\
  Mem.load Mint32 after b2 o2 = Some (Vint word).
Proof.
  intros STORES FIRST SECOND; split;
    eapply constant_word_stores_preserve_observation; eassumption.
Qed.

Lemma constant_word_stores_trans word before middle after :
  constant_word_stores word before middle ->
  constant_word_stores word middle after ->
  constant_word_stores word before after.
Proof.
  intros FIRST; induction FIRST; intro LAST; [exact LAST|].
  econstructor; [exact H|apply IHFIRST; exact LAST].
Qed.

(** Restrict assignments to typed dereferences: an arbitrary int-typed
    lvalue could designate a bitfield and need not store the literal word. *)
Inductive constant_word_statement (word : int) : statement -> Prop :=
| constant_word_skip : constant_word_statement word Sskip
| constant_word_set : forall identifier expression,
    constant_word_statement word (Sset identifier expression)
| constant_word_assign : forall address,
    constant_word_statement word
      (Sassign (Ederef address (Tint I32 Signed noattr))
               (Econst_int word (Tint I32 Signed noattr)))
| constant_word_sequence : forall first second,
    constant_word_statement word first -> constant_word_statement word second ->
    constant_word_statement word (Ssequence first second)
| constant_word_if : forall expression yes no,
    constant_word_statement word yes -> constant_word_statement word no ->
    constant_word_statement word (Sifthenelse expression yes no).

Fixpoint check_constant_word_statement (word : int) (code : statement) : bool :=
  match code with
  | Sskip | Sset _ _ => true
  | Sassign (Ederef _ lhs_type) (Econst_int value rhs_type) =>
      if type_eq lhs_type (Tint I32 Signed noattr) then
        if type_eq rhs_type (Tint I32 Signed noattr) then Int.eq value word else false
      else false
  | Ssequence first second =>
      check_constant_word_statement word first && check_constant_word_statement word second
  | Sifthenelse _ yes no =>
      check_constant_word_statement word yes && check_constant_word_statement word no
  | _ => false
  end.

Theorem check_constant_word_statement_sound word code :
  check_constant_word_statement word code = true -> constant_word_statement word code.
Proof.
  induction code; cbn; intro CHECK; try discriminate; try solve [constructor].
  - destruct e; try discriminate; destruct e0; try discriminate.
    destruct (type_eq t (Tint I32 Signed noattr)); try discriminate.
    destruct (type_eq t0 (Tint I32 Signed noattr)); try discriminate.
    subst t t0; apply Int.same_if_eq in CHECK; subst; constructor.
  - apply andb_true_iff in CHECK as [FIRST SECOND]; constructor; auto.
  - apply andb_true_iff in CHECK as [YES NO]; constructor; auto.
Qed.

Theorem constant_word_statement_execution word code :
  constant_word_statement word code ->
  forall fe ge locals before memory trace after final outcome,
  exec_stmt fe ge locals before memory code trace after final outcome ->
  constant_word_stores word memory final.
Proof.
  intro CHECK; induction CHECK; intros fe ge locals before memory trace after final outcome RUN.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; constructor.
  - inversion RUN; subst; inversion H1; subst; inversion H2; subst;
      try match goal with BAD : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion BAD end.
    cbn [typeof Cop.sem_cast Cop.classify_cast Cop.cast_int_int] in H6.
    inversion H6; subst; inversion H11; subst; cbn [typeof access_mode] in *; try discriminate.
    match goal with H : By_value Mint32 = By_value _ |- _ => inversion H; subst end.
    econstructor; [eapply Mem.storev_store; eassumption|constructor].
  - inversion RUN; subst; eauto using constant_word_stores_trans.
  - inversion RUN; subst; destruct b; cbn in *; eauto.
Qed.

Theorem checked_constant_word_body_preserves_observation word code
  fe ge locals before memory trace after final outcome block offset :
  check_constant_word_statement word code = true ->
  Mem.load Mint32 memory block offset = Some (Vint word) ->
  exec_stmt fe ge locals before memory code trace after final outcome ->
  Mem.load Mint32 final block offset = Some (Vint word).
Proof.
  intros CHECK LOAD RUN.
  eapply constant_word_stores_preserve_observation; [|exact LOAD].
  eapply constant_word_statement_execution; [eapply check_constant_word_statement_sound; exact CHECK|exact RUN].
Qed.

Theorem mint32_store_different_word_changes_same_cell before after word other block offset :
  word <> other ->
  Mem.store Mint32 before block offset (Vint other) = Some after ->
  Mem.load Mint32 after block offset <> Some (Vint word).
Proof.
  intros DIFFERENT STORE.
  pose proof (Mem.load_store_same _ _ _ _ _ _ STORE) as RESULT.
  cbn [Val.load_result] in RESULT; rewrite RESULT; intro SAME.
  injection SAME as EQUAL; apply DIFFERENT; symmetry; exact EQUAL.
Qed.

Print Assumptions mint32_store_preserves_equal_word.
Print Assumptions constant_word_stores_preserve_observation.
Print Assumptions constant_word_stores_preserve_two_observations.
Print Assumptions mint32_store_different_word_changes_same_cell.
Print Assumptions check_constant_word_statement_sound.
Print Assumptions constant_word_statement_execution.
Print Assumptions checked_constant_word_body_preserves_observation.
