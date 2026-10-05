From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From Guard Require Import AbstractGuard SemanticFacts ClightCondition ClightPureExpr ClightNoWrap ClightSameAddress
  ClightDecisionRule ClightPositiveCheck ClightRedundantSet ClightMatrixGuard ClightRectangularGuard ClightCountedLoop.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyTreeSynthesis
  ClightReadonlyCellSwap ClightIndexedLoadBody ClightIndexedLoadDomain.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** No pointer ordering or integer-address conversion is introduced. These
    checks compare actual active word addresses. A static fuel bounds code
    size; a separate runtime count test guarantees complete coverage. *)
Definition indexed_alias_expr out parameter point :=
  Ebinop Oeq (indexed_word_pointer out (Econst_int (Int.repr point) type_int32s))
    (pointer_temp parameter) type_int32s.
Definition indexed_alias_flag out parameter point entry :=
  match (entry_temps entry) ! out, (entry_temps entry) ! parameter with
  | Some (Vptr block base), Some (Vptr q qofs) =>
      address_flag block (indexed_word_offset base (Int.repr point)) q qofs
  | _, _ => false end.
Definition indexed_active_expr bound point :=
  Ebinop Olt (Econst_int (Int.repr point) type_int32s) (Etempvar bound type_int32s) type_int32s.
Definition indexed_active_flag bound point entry := (point <? Int.signed (temp_word bound (entry_temps entry))).
Fixpoint indexed_alias_scan out parameter bound fuel point :=
  match fuel with
  | O => Decision true
  | S rest => Test (indexed_active_expr bound point)
      (Test (indexed_alias_expr out parameter point) (Decision false)
        (indexed_alias_scan out parameter bound rest (point+1))) (Decision true)
  end.
Fixpoint indexed_alias_accept out parameter bound fuel point entry :=
  match fuel with
  | O => true
  | S rest => if indexed_active_flag bound point entry
      then negb (indexed_alias_flag out parameter point entry) &&
        indexed_alias_accept out parameter bound rest (point+1) entry
      else true
  end.

Lemma indexed_active_test bound point entry : signed_range point -> register_domain bound entry ->
  expression_test (indexed_active_expr bound point) entry (indexed_active_flag bound point entry).
Proof.
  intros RANGE [n N]; unfold indexed_active_flag, temp_word; rewrite N.
  exists (Val.of_bool (point <? Int.signed n)); split.
  - eapply eval_Ebinop with (v1 := Vint (Int.repr point)) (v2 := Vint n); [constructor|constructor; exact N|].
    change (Some (Val.of_bool (Int.lt (Int.repr point) n)) = Some (Val.of_bool (point <? Int.signed n))).
    unfold Int.lt; rewrite Int.signed_repr by exact RANGE.
    destruct (zlt point (Int.signed n)) as [LT|GE].
    + assert (B : (point <? Int.signed n) = true) by (apply Z.ltb_lt; exact LT); rewrite B; reflexivity.
    + assert (B : (point <? Int.signed n) = false) by (apply Z.ltb_ge; lia); rewrite B; reflexivity.
  - apply bool_of_bool.
Qed.

Lemma indexed_alias_test out parameter point entry block base q qofs loaded :
  (entry_temps entry) ! out = Some (Vptr block base) ->
  (entry_temps entry) ! parameter = Some (Vptr q qofs) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some loaded ->
  writable_word (entry_memory entry) block (indexed_word_offset base (Int.repr point)) ->
  expression_test (indexed_alias_expr out parameter point) entry (indexed_alias_flag out parameter point entry).
Proof.
  intros OUT PARAMETER READ WORD; exists (Val.of_bool
    (address_flag block (indexed_word_offset base (Int.repr point)) q qofs)); split.
  - eapply eval_Ebinop with (v1 := Vptr block (indexed_word_offset base (Int.repr point))) (v2 := Vptr q qofs).
    + apply indexed_pointer_evaluation; [exact OUT|constructor|reflexivity].
    + constructor; exact PARAMETER.
    + change (cmp_ptr (entry_memory entry) Ceq (Vptr block (indexed_word_offset base (Int.repr point))) (Vptr q qofs) =
        Some (Val.of_bool (address_flag block (indexed_word_offset base (Int.repr point)) q qofs))).
      apply pointer_equality_value; [apply writable_word_valid_pointer; exact WORD|eapply loaded_address_valid; exact READ].
  - unfold indexed_alias_flag; rewrite OUT, PARAMETER; apply bool_of_bool.
Qed.

Theorem indexed_alias_apart out parameter point entry block base q qofs :
  (entry_temps entry) ! out = Some (Vptr block base) -> (entry_temps entry) ! parameter = Some (Vptr q qofs) ->
  indexed_alias_flag out parameter point entry = false ->
  Vptr block (indexed_word_offset base (Int.repr point)) <> Vptr q qofs.
Proof.
  intros OUT PARAMETER APART SAME; inversion SAME; subst.
  unfold indexed_alias_flag, address_flag in APART; rewrite OUT, PARAMETER, Pos.eqb_refl, Ptrofs.eq_true in APART; discriminate.
Qed.

Theorem indexed_alias_scan_run out parameter bound fuel point entry block base q qofs loaded :
  0 <= point -> point + Z.of_nat fuel <= Int.max_signed -> register_domain bound entry ->
  (entry_temps entry) ! out = Some (Vptr block base) -> (entry_temps entry) ! parameter = Some (Vptr q qofs) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some loaded ->
  (forall k, point <= k < Int.signed (temp_word bound (entry_temps entry)) ->
    writable_word (entry_memory entry) block (indexed_word_offset base (Int.repr k))) ->
  decision_run entry (indexed_alias_scan out parameter bound fuel point)
    (indexed_alias_accept out parameter bound fuel point entry).
Proof.
  revert point; induction fuel as [|fuel IH]; intros point LOW HIGH N OUT PARAMETER READ WORDS; cbn; [constructor|].
  eapply run_test.
  - apply indexed_active_test; [unfold signed_range; change Int.min_signed with (-2147483648); rewrite Nat2Z.inj_succ in HIGH; lia|exact N].
  - destruct (indexed_active_flag bound point entry) eqn:ACTIVE; cbn; [|constructor].
    unfold indexed_active_flag in ACTIVE; apply Z.ltb_lt in ACTIVE.
    eapply run_test; [eapply indexed_alias_test; [exact OUT|exact PARAMETER|exact READ|apply WORDS; lia]|].
    destruct (indexed_alias_flag out parameter point entry); cbn; [constructor|].
    apply IH; try assumption; [lia|rewrite Nat2Z.inj_succ in HIGH; lia|].
    intros k RANGE; apply WORDS; lia.
Qed.

Theorem indexed_alias_scan_sound out parameter bound fuel point entry :
  indexed_alias_accept out parameter bound fuel point entry = true ->
  forall k, point <= k < point + Z.of_nat fuel -> k < Int.signed (temp_word bound (entry_temps entry)) ->
    indexed_alias_flag out parameter k entry = false.
Proof.
  revert point; induction fuel as [|fuel IH]; intros point ACCEPT k RANGE ACTIVE;
    cbn [indexed_alias_accept] in ACCEPT; [cbn in RANGE; lia|].
  destruct (indexed_active_flag bound point entry) eqn:POINT.
  - apply andb_true_iff in ACCEPT as [APART TAIL].
    destruct (Z.eq_dec k point); [subst; apply negb_true_iff in APART; exact APART|].
    eapply IH; [exact TAIL|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
  - unfold indexed_active_flag in POINT; apply Z.ltb_ge in POINT; lia.
Qed.
Print Assumptions indexed_alias_apart.
Print Assumptions indexed_alias_scan_run.
Print Assumptions indexed_alias_scan_sound.

Lemma indexed_alias_scan_pure out parameter bound fuel point : pure_tree (indexed_alias_scan out parameter bound fuel point).
Proof. revert point; induction fuel; intro point; cbn; [constructor|]; repeat constructor; apply IHfuel. Qed.
Definition indexed_guard_tree iterator bound out parameter cap :=
  Test (register_guard iterator Int.zero)
    (Test (register_positive_expr bound)
      (Test (register_at_most_expr bound (Z.of_nat cap))
        (indexed_alias_scan out parameter bound cap 0) (Decision false)) (Decision false)) (Decision false).
Definition indexed_guard_accept iterator bound out parameter cap (_ : unit) entry :=
  register_flag iterator Int.zero entry && register_range_flag bound (Z.of_nat cap) entry &&
    indexed_alias_accept out parameter bound cap 0 entry.
Definition indexed_guard_property iterator bound out parameter cap (_ : unit) entry :=
  register_equals iterator Int.zero tt entry /\ register_range bound (Z.of_nat cap) entry /\
  forall k, 0 <= k < Int.signed (temp_word bound (entry_temps entry)) -> indexed_alias_flag out parameter k entry = false.

Lemma indexed_guard_run iterator bound out parameter cap entry : Z.of_nat cap <= Int.max_signed ->
  indexed_load_domain iterator bound out parameter entry ->
  decision_run entry (indexed_guard_tree iterator bound out parameter cap)
    (indexed_guard_accept iterator bound out parameter cap tt entry).
Proof.
  intros CAP [I [N SOURCE]]; unfold indexed_guard_tree, indexed_guard_accept, register_range_flag.
  eapply run_test; [apply register_expression_test; exact I|].
  destruct (register_flag iterator Int.zero entry) eqn:ZERO; cbn; [|constructor].
  eapply run_test; [apply register_positive_test; exact N|].
  destruct (register_positive bound entry) eqn:POS; cbn; [|constructor].
  eapply run_test; [apply register_at_most_test; exact N|].
  destruct (register_at_most bound (Z.of_nat cap) entry); cbn; [|constructor].
  destruct (SOURCE (register_flag_evidence Int.zero I ZERO) (@register_positive_sound bound entry POS))
    as [block [base [q [qofs [loaded [OUT [PARAMETER [READ WORDS]]]]]]]].
  eapply indexed_alias_scan_run; [lia|cbn; exact CAP|exact N|exact OUT|exact PARAMETER|exact READ|].
  exact WORDS.
Qed.

Lemma indexed_guard_sound iterator bound out parameter cap : Z.of_nat cap <= Int.max_signed -> forall a entry,
  indexed_load_domain iterator bound out parameter entry ->
  indexed_guard_accept iterator bound out parameter cap a entry = true ->
  indexed_guard_property iterator bound out parameter cap a entry.
Proof.
  intros CAP [] entry [I [N SOURCE]] ACCEPT; unfold indexed_guard_accept in ACCEPT.
  repeat rewrite andb_true_iff in ACCEPT; destruct ACCEPT as [[ZERO RANGE] SCAN].
  pose proof (@register_range_sound bound (Z.of_nat cap) entry
    ltac:(unfold signed_range; change Int.min_signed with (-2147483648); lia) N RANGE) as BOUND.
  unfold indexed_guard_property; split; [apply register_flag_evidence; assumption|split; [exact BOUND|]].
  intros k ACTIVE; eapply indexed_alias_scan_sound; [exact SCAN| |exact (proj2 ACTIVE)].
  destruct BOUND as [_ B]; cbn; lia.
Qed.
Definition indexed_guard_primitives iterator bound out parameter cap (CAP : Z.of_nat cap <= Int.max_signed) :=
  @positive_tree_primitives unit (indexed_load_domain iterator bound out parameter)
    (indexed_guard_property iterator bound out parameter cap) (indexed_guard_accept iterator bound out parameter cap)
    (@indexed_guard_sound iterator bound out parameter cap CAP)
    (fun _ => indexed_guard_tree iterator bound out parameter cap)
    (fun _ => ltac:(repeat constructor; apply indexed_alias_scan_pure))
    (fun a entry DOMAIN => match a with tt => @indexed_guard_run iterator bound out parameter cap entry CAP DOMAIN end).
Definition indexed_guard_condition fe O (observe : fragment_observation -> O -> Prop)
  iterator bound out parameter cap (CAP : Z.of_nat cap <= Int.max_signed) :
  readonly_condition (readonly_clight_host fe observe) (indexed_load_domain iterator bound out parameter)
    (indexed_guard_property iterator bound out parameter cap tt)
    (synthesize_decision_tree (@indexed_guard_primitives iterator bound out parameter cap CAP) (Fact tt)).
Proof.
  apply synthesized_scalar_tree_condition with
    (D := @positive_dimension clight_entry unit (indexed_load_domain iterator bound out parameter)
      (indexed_guard_property iterator bound out parameter cap) (indexed_guard_accept iterator bound out parameter cap)
      (@indexed_guard_sound iterator bound out parameter cap CAP)) (premise := Fact tt).
  - intros []; repeat constructor; apply indexed_alias_scan_pure.
  - intros []; constructor.
Defined.
Print Assumptions indexed_guard_condition.
Print Assumptions indexed_guard_sound.
