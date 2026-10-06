From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightSameAddress ClightPureExpr ClightNoWrap ClightCountedLoop CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryPointerAccess.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ClightReadonlyLoadedTreeSynthesis ClightLoadedBoundSyntax ClightStableLoadBody ClightWordAddressSeparation.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A writable aligned word must avoid both word slots of a wide observation.
    Equality with the starting address alone does not establish byte separation. *)
Definition word_observation_chunk (wide : bool) := if wide then Mint64 else Mint32.
Definition word_chunk_second_address address :=
  Ebinop Oadd address (Econst_int Int.one type_int32s) (Tpointer type_int32s noattr).
Definition word_chunk_equal code address := Ebinop Oeq code address type_int32s.
Definition word_chunk_separation code address (wide : bool) :=
  Test (word_chunk_equal code address) (Decision false)
    (if wide then Test (word_chunk_equal code (word_chunk_second_address address)) (Decision false) (Decision true)
     else Decision true).
Definition word_chunk_domain code address wide entry :=
  exists block offset other base loaded,
    eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) code (Vptr block offset) /\
    eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) address (Vptr other base) /\
    Mem.valid_access (entry_memory entry) Mint32 block (Ptrofs.unsigned offset) Writable /\
    Mem.loadv (word_observation_chunk wide) (entry_memory entry) (Vptr other base) = Some loaded.
Definition word_chunk_separated code address wide entry :=
  exists block offset other base,
    eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) code (Vptr block offset) /\
    eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) address (Vptr other base) /\
    location_disjoint (MemoryLocation Mint32 block (Ptrofs.unsigned offset))
      (MemoryLocation (word_observation_chunk wide) other (Ptrofs.unsigned base)).

Lemma wide_second_offset memory block base loaded :
  Mem.loadv Mint64 memory (Vptr block base) = Some loaded ->
  Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr 4)) = Ptrofs.unsigned base + 4.
Proof.
  cbn [Mem.loadv]; destruct (zle (Ptrofs.unsigned base + size_chunk Mint64) Ptrofs.modulus);
    [|discriminate]; intro READ.
  unfold Ptrofs.add; rewrite Ptrofs.unsigned_repr_eq.
  change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4.
  rewrite Z.mod_small; [reflexivity|pose proof (Ptrofs.unsigned_range base); change (size_chunk Mint64) with 8 in *; lia].
Qed.

Lemma wide_second_valid memory block base loaded :
  Mem.loadv Mint64 memory (Vptr block base) = Some loaded ->
  Mem.valid_pointer memory block (Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr 4))) = true.
Proof.
  intro READ; rewrite (@wide_second_offset _ _ _ _ READ).
  cbn [Mem.loadv] in READ; destruct (zle _ _); [|discriminate].
  destruct (Mem.load_valid_access _ _ _ _ _ READ) as [PERMISSION ALIGN].
  apply Mem.valid_pointer_nonempty_perm; eapply Mem.perm_implies; [apply PERMISSION|constructor].
  change (size_chunk Mint64) with 8; lia.
Qed.

Lemma aligned_wide_pointers_apart block offset other base :
  (4 | Ptrofs.unsigned offset) -> (8 | Ptrofs.unsigned base) ->
  Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr 4)) = Ptrofs.unsigned base + 4 ->
  Vptr block offset <> Vptr other base ->
  Vptr block offset <> Vptr other (Ptrofs.add base (Ptrofs.repr 4)) ->
  location_disjoint (MemoryLocation Mint32 block (Ptrofs.unsigned offset))
    (MemoryLocation Mint64 other (Ptrofs.unsigned base)).
Proof.
  intros [x X] [y Y] SECOND DIFFERENT SECOND_DIFFERENT.
  destruct (peq block other) as [SAME|APART]; [subst other|left; exact APART].
  assert (FIRST : Ptrofs.unsigned offset <> Ptrofs.unsigned base).
  { intro SAME; apply DIFFERENT; f_equal; apply (f_equal Ptrofs.repr) in SAME;
      rewrite !Ptrofs.repr_unsigned in SAME; exact SAME. }
  assert (NEXT : Ptrofs.unsigned offset <> Ptrofs.unsigned base + 4).
  { intro SAME; apply SECOND_DIFFERENT; f_equal; rewrite <- SECOND in SAME;
      apply (f_equal Ptrofs.repr) in SAME; rewrite !Ptrofs.repr_unsigned in SAME; exact SAME. }
  unfold location_disjoint; cbn; right; lia.
Qed.

Lemma word_chunk_equality_test code address entry block offset other base :
  typeof code = Tpointer type_int32s noattr -> typeof address = Tpointer type_int32s noattr ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) code (Vptr block offset) ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) address (Vptr other base) ->
  Mem.valid_pointer (entry_memory entry) block (Ptrofs.unsigned offset) = true ->
  Mem.valid_pointer (entry_memory entry) other (Ptrofs.unsigned base) = true ->
  expression_test (word_chunk_equal code address) entry (address_flag block offset other base).
Proof.
  intros LEFT RIGHT CODE ADDRESS VALID LOAD.
  exists (Val.of_bool (address_flag block offset other base)); split; [|apply bool_of_bool].
  eapply eval_Ebinop; [exact CODE|exact ADDRESS|].
  unfold sem_binary_operation; rewrite LEFT,RIGHT.
  change (cmp_ptr (entry_memory entry) Ceq (Vptr block offset) (Vptr other base) =
    Some (Val.of_bool (address_flag block offset other base))).
  apply pointer_equality_value; assumption.
Qed.

Lemma word_chunk_second_evaluation address entry block base :
  typeof address = Tpointer type_int32s noattr ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) address (Vptr block base) ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
    (word_chunk_second_address address) (Vptr block (Ptrofs.add base (Ptrofs.repr 4))).
Proof.
  intros TYPE ADDRESS; eapply eval_Ebinop with (v1:=Vptr block base) (v2:=Vint Int.one); [exact ADDRESS|constructor|].
  cbn [typeof]; rewrite TYPE.
  replace 4 with (4*1) by ring.
  apply (@memory_pointer_add (entry_ge entry) (entry_memory entry) block base 1).
  unfold signed_range; change (-2147483648 <= 1 <= 2147483647); lia.
Qed.

Theorem word_chunk_separation_condition fe O (observe : fragment_observation -> O -> Prop) code address wide :
  typeof code = Tpointer type_int32s noattr -> typeof address = Tpointer type_int32s noattr ->
  readonly_condition (readonly_clight_host fe observe) (word_chunk_domain code address wide)
    (word_chunk_separated code address wide) (word_chunk_separation code address wide).
Proof.
  intros LEFT RIGHT; apply readonly_completed_tree_condition.
  - intros entry [block [offset [other [base [loaded [CODE [ADDRESS [WRITE READ]]]]]]]].
    pose proof (@word_chunk_equality_test code address entry block offset other base LEFT RIGHT CODE ADDRESS
      (@valid_word_address _ _ _ WRITE) (@loaded_address_valid _ _ _ _ _ READ)) as FIRST.
    destruct wide; cbn [word_observation_chunk] in READ.
    + pose proof (@word_chunk_equality_test code (word_chunk_second_address address) entry block offset other
        (Ptrofs.add base (Ptrofs.repr 4)) LEFT eq_refl CODE (@word_chunk_second_evaluation _ _ _ _ RIGHT ADDRESS)
        (@valid_word_address _ _ _ WRITE) (@wide_second_valid _ _ _ _ READ)) as SECOND.
      exists (negb (address_flag block offset other base) &&
        negb (address_flag block offset other (Ptrofs.add base (Ptrofs.repr 4)))).
      unfold word_chunk_separation; eapply run_test; [exact FIRST|].
      destruct (address_flag block offset other base); cbn; [constructor|].
      eapply run_test; [exact SECOND|destruct (address_flag block offset other (Ptrofs.add base (Ptrofs.repr 4))); constructor].
    + exists (negb (address_flag block offset other base)); unfold word_chunk_separation.
      eapply run_test; [exact FIRST|destruct (address_flag block offset other base); constructor].
  - intros entry [block [offset [other [base [loaded [CODE [ADDRESS [WRITE READ]]]]]]]] RUN.
    pose proof (@word_chunk_equality_test code address entry block offset other base LEFT RIGHT CODE ADDRESS
      (@valid_word_address _ _ _ WRITE) (@loaded_address_valid _ _ _ _ _ READ)) as FIRST.
    unfold word_chunk_separation in RUN; inversion RUN as [|a yes no choice result TEST BRANCH]; subst.
    assert (FLAG : choice = address_flag block offset other base) by (eapply readonly_test_determinate; eassumption); subst choice.
    assert (APART : address_flag block offset other base = false).
    { destruct (address_flag block offset other base); [inversion BRANCH|reflexivity]. }
    assert (DISTINCT : Vptr block offset <> Vptr other base).
    { intro SAME; inversion SAME; subst; unfold address_flag in APART; rewrite Pos.eqb_refl,Ptrofs.eq_true in APART; discriminate. }
    exists block,offset,other,base; split; [exact CODE|split; [exact ADDRESS|]].
    destruct WRITE as [PERMISSIONS ALIGN]; change (4 | Ptrofs.unsigned offset) in ALIGN.
    destruct wide; cbn [word_observation_chunk] in READ |- *.
    + pose proof (@wide_second_offset _ _ _ _ READ) as SECOND_OFFSET.
      pose proof (@word_chunk_equality_test code (word_chunk_second_address address) entry block offset other
        (Ptrofs.add base (Ptrofs.repr 4)) LEFT eq_refl CODE (@word_chunk_second_evaluation _ _ _ _ RIGHT ADDRESS)
        (@valid_word_address _ _ _ (conj PERMISSIONS ALIGN)) (@wide_second_valid _ _ _ _ READ)) as SECOND.
      assert (SECOND_APART : address_flag block offset other (Ptrofs.add base (Ptrofs.repr 4)) = false).
      { rewrite APART in BRANCH; inversion BRANCH as [|a yes no choice result TEST_SECOND LEAF]; subst.
        assert (FLAG : choice = address_flag block offset other (Ptrofs.add base (Ptrofs.repr 4)))
          by (eapply readonly_test_determinate; eassumption); subst choice.
        destruct (address_flag block offset other (Ptrofs.add base (Ptrofs.repr 4))); inversion LEAF; reflexivity. }
      assert (SECOND_DISTINCT : Vptr block offset <> Vptr other (Ptrofs.add base (Ptrofs.repr 4))).
      { intro SAME; injection SAME as BLOCK OFFSET; subst; unfold address_flag in SECOND_APART;
        rewrite Pos.eqb_refl,Ptrofs.eq_true in SECOND_APART; discriminate. }
      cbn [Mem.loadv] in READ; destruct (zle _ _); [|discriminate].
      destruct (Mem.load_valid_access _ _ _ _ _ READ) as [LOAD_PERMISSIONS LOAD_ALIGN].
      apply aligned_wide_pointers_apart; assumption.
    + cbn [Mem.loadv] in READ; destruct (zle _ _); [|discriminate].
      destruct (Mem.load_valid_access _ _ _ _ _ READ) as [LOAD_PERMISSIONS LOAD_ALIGN].
      exact (aligned_word_pointers_apart ALIGN LOAD_ALIGN DISTINCT).
Defined.

Print Assumptions wide_second_offset.
Print Assumptions wide_second_valid.
Print Assumptions aligned_wide_pointers_apart.
Print Assumptions word_chunk_equality_test.
Print Assumptions word_chunk_second_evaluation.
Print Assumptions word_chunk_separation_condition.
