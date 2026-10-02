From Stdlib Require Import Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr
  ClightTreeRule ClightTreeRewrite ClightNoWrap ClightTreeExamples.
Set Implicit Arguments.
Open Scope Z_scope.

(** A memory-sensitive expression rule: two ordinary uint32 loads can share
    an address after a runtime pointer equality check. Defined source loads
    justify the validity of the comparison; no pointer ordering is used. *)
Definition word_pointer := Tpointer type_int32u noattr.
Definition pointer_temp p := Etempvar p word_pointer.
Definition word_load p := Ederef (pointer_temp p) type_int32u.
Definition same_load_source p q := Ebinop Oadd (word_load p) (word_load q) type_int32u.
Definition same_load_candidate p := Ebinop Oadd (word_load p) (word_load p) type_int32u.
Definition same_address_guard p q := Ebinop Oeq (pointer_temp p) (pointer_temp q) type_int32s.

Definition address_flag b1 ofs1 b2 ofs2 := Pos.eqb b1 b2 && Ptrofs.eq ofs1 ofs2.

Lemma loaded_pointer_valid chunk m b ofs v : Mem.load chunk m b ofs = Some v ->
  Mem.valid_pointer m b ofs = true.
Proof.
  intro LOAD. apply Mem.valid_pointer_nonempty_perm.
  destruct (Mem.load_valid_access _ _ _ _ _ LOAD) as [PERM _].
  eapply Mem.perm_implies; [apply PERM; pose proof (size_chunk_pos chunk); lia | constructor].
Qed.

Lemma word_load_inv ge locals le m p v : eval_expr ge locals le m (word_load p) v ->
  exists b ofs, le ! p = Some (Vptr b ofs) /\
    Mem.loadv Mint32 m (Vptr b ofs) = Some v.
Proof.
  intro RUN. inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ (word_load p) _ _ _ |- _ => inversion LV; subst end.
  match goal with TEMP : eval_expr _ _ _ _ (pointer_temp p) _ |- _ =>
    apply scalar_temp_inv in TEMP end.
  match goal with LOAD : deref_loc _ _ _ _ _ _ |- _ => inversion LOAD; subst; try discriminate end.
  match goal with MODE : access_mode _ = By_value _ |- _ =>
    change (By_value Mint32 = By_value chunk) in MODE; inversion MODE; subst end.
  eexists; eexists; split; eauto.
Qed.

Lemma loaded_address_valid chunk m b ofs v : Mem.loadv chunk m (Vptr b ofs) = Some v ->
  Mem.valid_pointer m b (Ptrofs.unsigned ofs) = true.
Proof.
  cbn [Mem.loadv]. destruct (zle _ _); try discriminate.
  apply loaded_pointer_valid.
Qed.

Lemma pointer_equality_value m b1 ofs1 b2 ofs2 :
  Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  cmp_ptr m Ceq (Vptr b1 ofs1) (Vptr b2 ofs2) =
    Some (Val.of_bool (address_flag b1 ofs1 b2 ofs2)).
Proof.
  intros VP1 VP2. unfold cmp_ptr, address_flag.
  destruct Archi.ptr64 eqn:ARCH.
  - unfold Val.cmplu_bool. rewrite ARCH; cbn [negb].
    destruct (eq_block b1 b2) as [EQ|NE].
    + subst b2. rewrite VP1, VP2, Pos.eqb_refl; reflexivity.
    + assert (B : Pos.eqb b1 b2 = false) by (apply Pos.eqb_neq; exact NE).
      rewrite VP1, VP2, B; reflexivity.
  - unfold Val.cmpu_bool. rewrite ARCH.
    destruct (eq_block b1 b2) as [EQ|NE].
    + subst b2. rewrite VP1, VP2, Pos.eqb_refl; reflexivity.
    + assert (B : Pos.eqb b1 b2 = false) by (apply Pos.eqb_neq; exact NE).
      rewrite VP1, VP2, B; reflexivity.
Qed.

Definition address_domain p q (s : clight_entry) : Prop :=
  exists b1 ofs1 b2 ofs2,
    (entry_temps s) ! p = Some (Vptr b1 ofs1) /\
    (entry_temps s) ! q = Some (Vptr b2 ofs2) /\
    Mem.valid_pointer (entry_memory s) b1 (Ptrofs.unsigned ofs1) = true /\
    Mem.valid_pointer (entry_memory s) b2 (Ptrofs.unsigned ofs2) = true.

Definition address_accept p q (s : clight_entry) : bool :=
  match (entry_temps s) ! p, (entry_temps s) ! q with
  | Some (Vptr b1 ofs1), Some (Vptr b2 ofs2) => address_flag b1 ofs1 b2 ofs2
  | _, _ => false end.

Definition addresses_equal p q (_ : unit) (s : clight_entry) : Prop :=
  exists v, (entry_temps s) ! p = Some v /\ (entry_temps s) ! q = Some v.

Lemma address_accept_sound p q s : address_accept p q s = true -> addresses_equal p q tt s.
Proof.
  unfold address_accept. destruct ((entry_temps s) ! p) as [v|] eqn:P; try discriminate;
    destruct v; try discriminate.
  destruct ((entry_temps s) ! q) as [v|] eqn:Q; try discriminate; destruct v; try discriminate.
  unfold address_flag. rewrite andb_true_iff. intros [BLOCK OFFSET].
  apply Pos.eqb_eq in BLOCK; subst. apply Ptrofs.same_if_eq in OFFSET; subst.
  eexists; split; [exact P | exact Q].
Qed.

Lemma source_address_domain p q s : source_defined (same_load_source p q) s -> address_domain p q s.
Proof.
  intros [v SOURCE]. apply scalar_binary_inv in SOURCE.
  destruct SOURCE as [left [right [LEFT [RIGHT OP]]]].
  apply word_load_inv in LEFT, RIGHT.
  destruct LEFT as [b1 [ofs1 [P LP]]], RIGHT as [b2 [ofs2 [Q LQ]]].
  exists b1, ofs1, b2, ofs2; repeat split; auto; eapply loaded_address_valid; eauto.
Qed.

Lemma address_guard_correct p q s result : address_domain p q s ->
  (expression_test (same_address_guard p q) s result <-> result = address_accept p q s).
Proof.
  intros [b1 [ofs1 [b2 [ofs2 [P [Q [VP1 VP2]]]]]]].
  assert (CHECK : expression_test (same_address_guard p q) s (address_accept p q s)).
  { unfold expression_test, address_accept. rewrite P, Q.
    exists (Val.of_bool (address_flag b1 ofs1 b2 ofs2)); split.
    - eapply eval_Ebinop; [constructor; exact P | constructor; exact Q |].
      change (cmp_ptr (entry_memory s) Ceq (Vptr b1 ofs1) (Vptr b2 ofs2) =
        Some (Val.of_bool (address_flag b1 ofs1 b2 ofs2))).
      apply pointer_equality_value; assumption.
    - destruct (address_flag b1 ofs1 b2 ofs2); reflexivity. }
  split.
  - intro RUN. eapply pure_test_determinate;
      [constructor; constructor | exact RUN | exact CHECK].
  - intro EQ; subst; exact CHECK.
Qed.

Definition address_dimension p q :=
  @positive_dimension clight_entry unit (address_domain p q) (addresses_equal p q)
    (fun _ => address_accept p q) (fun _ s _ ACCEPT => address_accept_sound p q s ACCEPT).

Lemma constant_one_test s result :
  expression_test (Econst_int Int.one type_int32s) s result <-> result = true.
Proof.
  split.
  - intros [v [EV BOOL]]. apply scalar_const_inv in EV; subst.
    change (Some true = Some result) in BOOL; congruence.
  - intro EQ; subst; exists (Vint Int.one); split; [constructor | reflexivity].
Qed.

Definition address_primitives p q :
  check_primitives decision_language (address_domain p q) (decide_atom (address_dimension p q)).
Proof.
  refine (@CheckPrimitives clight_entry unit decision_language (address_domain p q)
    (decide_atom (address_dimension p q)) (fun _ => same_address_guard p q)
    (fun _ => Econst_int Int.one type_int32s) _ _).
  - intros [] s result DOMAIN. cbn [decision_language].
    rewrite address_guard_correct by exact DOMAIN.
    unfold address_dimension; cbn [positive_dimension decide_atom].
    destruct (address_accept p q s); reflexivity.
  - intros [] s result expected DOMAIN CHECK. cbn [decision_language]. rewrite constant_one_test.
    unfold address_dimension in CHECK; cbn [positive_dimension decide_atom] in CHECK.
    destruct (address_accept p q s); try discriminate; inversion CHECK; reflexivity.
Defined.

Lemma same_load_local p q s v :
  eval_expr (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s) (same_load_source p q) v ->
  addresses_equal p q tt s ->
  eval_expr (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s) (same_load_candidate p) v.
Proof.
  intros SOURCE [pointer [P Q]]. apply scalar_binary_inv in SOURCE.
  destruct SOURCE as [left [right [LEFT [RIGHT OP]]]].
  pose proof RIGHT as RLOAD. apply word_load_inv in RLOAD.
  destruct RLOAD as [b [ofs [Q' LOAD]]].
  assert (PTR : pointer = Vptr b ofs) by congruence; subst pointer.
  assert (LEFT' : eval_expr (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s)
    (word_load p) right).
  { eapply eval_Elvalue.
    - apply eval_Ederef. constructor; exact P.
    - eapply deref_loc_value; [reflexivity | exact LOAD]. }
  eapply eval_Ebinop; [exact LEFT | exact LEFT' | exact OP].
Qed.

Definition same_load_rule p q : encoded_tree_rule (same_load_source p q) (same_load_candidate p).
Proof.
  refine {| rule_atoms := unit; rule_domain := address_domain p q;
    rule_dimension := address_dimension p q; rule_primitives := address_primitives p q;
    rule_formula := Fact tt |}.
  - reflexivity.
  - apply source_address_domain.
  - intros s v SOURCE PROPERTY. eapply same_load_local; eauto.
Defined.

Theorem same_load_rule_correct p q :
  ClightTreeRewrite.expression_contract (same_load_source p q)
    (generated_tree (same_load_rule p q)) (same_load_candidate p).
Proof. apply encoded_tree_rule_sound. Qed.

Definition select_same_load (a : expr) : option (decision_tree * expr) :=
  match a with
  | Ebinop Oadd (Ederef (Etempvar p tp) tl) (Ederef (Etempvar q tq) tr) ty =>
      if type_eq tp word_pointer then if type_eq tq word_pointer then
      if type_eq tl type_int32u then if type_eq tr type_int32u then
      if type_eq ty type_int32u then
        Some (generated_tree (same_load_rule p q), same_load_candidate p)
      else None else None else None else None else None
  | _ => None end.

Theorem select_same_load_sound a tree code :
  select_same_load a = Some (tree, code) -> ClightTreeRewrite.expression_contract a tree code.
Proof.
  intro SELECT. unfold select_same_load in SELECT.
  repeat match type of SELECT with
  | context [if ?x then _ else _] => destruct x; cbn beta iota zeta in SELECT; try discriminate
  | context [match ?x with _ => _ end] => destruct x; cbn beta iota zeta in SELECT; try discriminate
  end.
  subst; inversion SELECT; subst; apply same_load_rule_correct.
Qed.

Definition select_memory_root a :=
  match select_same_load a with Some rule => Some rule | None => select_tree_common_root a end.
Definition select_memory_rewrites := select_tree_deep select_memory_root.

Theorem select_memory_rewrites_sound a tree code :
  select_memory_rewrites a = Some (tree, code) -> ClightTreeRewrite.expression_contract a tree code.
Proof.
  apply select_tree_deep_sound. intros original test candidate SELECT.
  unfold select_memory_root in SELECT.
  destruct (select_same_load original) as [[t c]|] eqn:MEMORY.
  - inversion SELECT; subst; eapply select_same_load_sound; eauto.
  - eapply select_tree_common_root_sound; eauto.
Qed.

Print Assumptions same_load_rule_correct.
