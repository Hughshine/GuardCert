From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import ClightCondition ClightSameAddress ClightPureExpr ClightNoWrap CompCertMemoryActions.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyCompletedCondition
  ClightReadonlyLoadedTreeSynthesis ClightLoadedBoundSyntax ClightStableLoadBody.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The write-address expression may describe an affine array access. Its
    permission comes from a reached source store, not from non-aliasing.
    Equality is defined for valid pointers in different memory blocks too. *)
Definition word_address_domain code parameter entry :=
  exists block offset other base loaded,
    eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      code (Vptr block offset) /\
    (entry_temps entry) ! parameter = Some (Vptr other base) /\
    Mem.valid_access (entry_memory entry) Mint32 block (Ptrofs.unsigned offset) Writable /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr other base) = Some loaded.

Definition word_address_separated code parameter entry :=
  exists block offset other base,
    eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      code (Vptr block offset) /\
    (entry_temps entry) ! parameter = Some (Vptr other base) /\
    location_disjoint (MemoryLocation Mint32 block (Ptrofs.unsigned offset))
      (MemoryLocation Mint32 other (Ptrofs.unsigned base)).

Definition word_address_equal code parameter :=
  Ebinop Oeq code (signed_pointer_temp parameter) type_int32s.
Definition word_address_separation code parameter :=
  Test (word_address_equal code parameter) (Decision false) (Decision true).

Lemma valid_word_address memory block offset :
  Mem.valid_access memory Mint32 block offset Writable -> Mem.valid_pointer memory block offset = true.
Proof.
  intros [PERMISSION ALIGN]; apply Mem.valid_pointer_nonempty_perm.
  eapply Mem.perm_implies; [apply PERMISSION; change (size_chunk Mint32) with 4; lia|constructor].
Qed.

Lemma word_address_equality_test code parameter entry block offset other base loaded :
  typeof code = Tpointer type_int32s noattr ->
  eval_expr (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry) code (Vptr block offset) ->
  (entry_temps entry) ! parameter = Some (Vptr other base) ->
  Mem.valid_access (entry_memory entry) Mint32 block (Ptrofs.unsigned offset) Writable ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr other base) = Some loaded ->
  expression_test (word_address_equal code parameter) entry (address_flag block offset other base).
Proof.
  intros TYPE EVALUATE POINTER ACCESS READ.
  exists (Val.of_bool (address_flag block offset other base)); split; [|apply bool_of_bool].
  eapply eval_Ebinop; [exact EVALUATE|constructor; exact POINTER|].
  unfold sem_binary_operation; rewrite TYPE.
  change (cmp_ptr (entry_memory entry) Ceq (Vptr block offset) (Vptr other base) =
    Some (Val.of_bool (address_flag block offset other base))).
  apply pointer_equality_value; [apply valid_word_address; exact ACCESS|eapply loaded_address_valid; exact READ].
Qed.

Theorem word_address_separation_condition fe O (observe : fragment_observation -> O -> Prop) code parameter :
  typeof code = Tpointer type_int32s noattr ->
  readonly_condition (readonly_clight_host fe observe) (word_address_domain code parameter)
    (word_address_separated code parameter) (word_address_separation code parameter).
Proof.
  intro TYPE; apply readonly_completed_tree_condition.
  - intros entry [block [offset [other [base [loaded [EVALUATE [POINTER [ACCESS READ]]]]]]]].
    pose proof (@word_address_equality_test code parameter entry block offset other base loaded
      TYPE EVALUATE POINTER ACCESS READ) as TEST.
    exists (negb (address_flag block offset other base)); unfold word_address_separation.
    eapply run_test; [exact TEST|destruct (address_flag block offset other base); constructor].
  - intros entry [block [offset [other [base [loaded [EVALUATE [POINTER [ACCESS READ]]]]]]]] RUN.
    pose proof (@word_address_equality_test code parameter entry block offset other base loaded
      TYPE EVALUATE POINTER ACCESS READ) as TEST.
    assert (APART : address_flag block offset other base = false).
    { unfold word_address_separation in RUN; inversion RUN; subst.
      match goal with LEAF : decision_run _ (if ?choice then Decision false else Decision true) true |- _ =>
        destruct choice; inversion LEAF; subst end.
      eapply readonly_test_determinate; eassumption. }
    assert (DISTINCT : Vptr block offset <> Vptr other base).
    { intro SAME; inversion SAME; subst; unfold address_flag in APART;
        rewrite Pos.eqb_refl,Ptrofs.eq_true in APART; discriminate. }
    destruct ACCESS as [PERMISSION ALIGN].
    cbn [Mem.loadv] in READ; destruct (zle (Ptrofs.unsigned base + size_chunk Mint32) Ptrofs.modulus);
      [|discriminate READ].
    destruct (Mem.load_valid_access _ _ _ _ _ READ) as [LOAD_PERMISSIONS LOAD_ALIGN].
    change (4 | Ptrofs.unsigned offset) in ALIGN; change (4 | Ptrofs.unsigned base) in LOAD_ALIGN.
    exists block,offset,other,base; split; [exact EVALUATE|split; [exact POINTER|]].
    exact (aligned_word_pointers_apart ALIGN LOAD_ALIGN DISTINCT).
Defined.

Print Assumptions word_address_equality_test.
Print Assumptions word_address_separation_condition.
