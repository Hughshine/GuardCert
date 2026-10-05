From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightPureExpr ClightSameAddress ClightCountedLoop
  ClightMatrixGuard ClightRedundantSet ClightLoopSyntax ClightStraightLine.
From GuardInterface Require Import ClightIndexedLoadBody ClightIndexedAliasGuard ClightIndexedBoundSyntax
  ClightIndexedBoundPrefix ClightStableLoadBody ClightReadonlyCellSwap.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition indexed_bound_word bound entry :=
  match (entry_temps entry) ! bound with
  | Some (Vptr q qofs) => match Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) with
    | Some (Vint upper) => upper | _ => Int.zero end
  | _ => Int.zero end.
Definition indexed_bound_active_expr bound point :=
  Ebinop Olt (Econst_int (Int.repr point) type_int32s) (indexed_bound_value bound) type_int32s.
Definition indexed_bound_active_flag bound point entry := (point <? Int.signed (indexed_bound_word bound entry)).
Fixpoint indexed_bound_alias_scan out bound fuel point :=
  match fuel with
  | O => Decision true
  | S rest => Test (indexed_bound_active_expr bound point)
      (Test (indexed_alias_expr out bound point) (Decision false)
        (indexed_bound_alias_scan out bound rest (point+1))) (Decision true)
  end.
Fixpoint indexed_bound_alias_accept out bound fuel point entry :=
  match fuel with
  | O => true
  | S rest => if indexed_bound_active_flag bound point entry
      then negb (indexed_alias_flag out bound point entry) &&
        indexed_bound_alias_accept out bound rest (point+1) entry
      else true
  end.

Lemma indexed_bound_active_test bound point entry q qofs upper : signed_range point ->
  (entry_temps entry) ! bound = Some (Vptr q qofs) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some (Vint upper) ->
  expression_test (indexed_bound_active_expr bound point) entry (indexed_bound_active_flag bound point entry).
Proof.
  intros RANGE BOUND READ; unfold indexed_bound_active_flag, indexed_bound_word; rewrite BOUND, READ.
  exists (Val.of_bool (point <? Int.signed upper)); split.
  - eapply eval_Ebinop with (v1 := Vint (Int.repr point)) (v2 := Vint upper); [constructor| |].
    + eapply indexed_bound_value_evaluation; eassumption.
    + change (Some (Val.of_bool (Int.lt (Int.repr point) upper)) = Some (Val.of_bool (point <? Int.signed upper))).
      unfold Int.lt; rewrite Int.signed_repr by exact RANGE.
      destruct (zlt point (Int.signed upper)) as [LT|GE].
      * assert (B : (point <? Int.signed upper) = true) by (apply Z.ltb_lt; exact LT); rewrite B; reflexivity.
      * assert (B : (point <? Int.signed upper) = false) by (apply Z.ltb_ge; lia); rewrite B; reflexivity.
  - apply bool_of_bool.
Qed.

(** The runtime tree reads only the entry state. Its ghost proof advances a
    source execution after each successful comparison, rather than assuming
    that the entry bound already describes a valid complete write footprint. *)
Theorem indexed_bound_alias_scan_run fe ge locals iterator out bound body fuel point
  initial_temps memory current_temps current_memory after final block base q qofs upper :
  iterator <> out -> iterator <> bound -> flatten_region body = [indexed_bound_body out iterator] ->
  0 <= point -> point + Z.of_nat fuel <= Int.max_signed ->
  initial_temps ! out = Some (Vptr block base) -> initial_temps ! bound = Some (Vptr q qofs) ->
  Mem.loadv Mint32 memory (Vptr q qofs) = Some (Vint upper) ->
  current_temps ! out = Some (Vptr block base) -> current_temps ! bound = Some (Vptr q qofs) ->
  current_temps ! iterator = Some (Vint (Int.repr point)) ->
  Mem.loadv Mint32 current_memory (Vptr q qofs) = Some (Vint upper) ->
  (forall b ofs, writable_word current_memory b ofs -> writable_word memory b ofs) ->
  exec_stmt fe ge locals current_temps current_memory (indexed_bound_loop iterator bound body) E0 after final Out_normal ->
  decision_run (Entry ge locals initial_temps memory) (indexed_bound_alias_scan out bound fuel point)
    (indexed_bound_alias_accept out bound fuel point (Entry ge locals initial_temps memory)).
Proof.
  intros IO IQ FLAT; revert point current_temps current_memory.
  induction fuel as [|fuel IH]; intros point current_temps current_memory LOW HIGH OUT BOUND READ
    CURRENT_OUT CURRENT_BOUND ITER CURRENT_READ PERMISSIONS SOURCE;
    cbn [indexed_bound_alias_scan indexed_bound_alias_accept]; [constructor|].
  eapply run_test.
  - eapply indexed_bound_active_test; [|exact BOUND|exact READ].
    unfold signed_range; change Int.min_signed with (-2147483648); rewrite Nat2Z.inj_succ in HIGH; lia.
  - destruct (indexed_bound_active_flag bound point (Entry ge locals initial_temps memory)) eqn:ACTIVE; cbn; [|constructor].
    unfold indexed_bound_active_flag, indexed_bound_word in ACTIVE; cbn [entry_temps entry_memory] in ACTIVE; rewrite BOUND, READ in ACTIVE;
      apply Z.ltb_lt in ACTIVE.
    destruct (@indexed_bound_source_step fe ge locals iterator bound out body current_temps current_memory
      after final point upper q qofs FLAT ltac:(lia) ITER CURRENT_BOUND CURRENT_READ SOURCE)
      as [other [other_base [value [next_memory [POINTER [STORE TAIL]]]]]].
    assert (SAME : Vptr other other_base = Vptr block base) by congruence; injection SAME; intros; subst.
    destruct (@storev_word_facts _ _ _ _ _ STORE) as [WORD RAW].
    eapply run_test; [eapply indexed_alias_test; [exact OUT|exact BOUND|exact READ|apply PERMISSIONS; exact WORD]|].
    destruct (indexed_alias_flag out bound point (Entry ge locals initial_temps memory)) eqn:ALIAS; cbn; [constructor|].
    assert (NEXT_READ : Mem.loadv Mint32 next_memory (Vptr q qofs) = Some (Vint upper)).
    { eapply mint32_load_survives_apart_store; [exact STORE|exact CURRENT_READ|].
      exact (@indexed_alias_apart out bound point (Entry ge locals initial_temps memory)
        block base q qofs OUT BOUND ALIAS). }
    eapply (IH (point+1) (PTree.set iterator (Vint (Int.repr (point+1))) current_temps) next_memory).
    + lia.
    + rewrite Nat2Z.inj_succ in HIGH; lia.
    + exact OUT.
    + exact BOUND.
    + exact READ.
    + rewrite PTree.gso by congruence; exact CURRENT_OUT.
    + rewrite PTree.gso by congruence; exact CURRENT_BOUND.
    + apply PTree.gss.
    + exact NEXT_READ.
    + intros b ofs [VALID ADDRESS]; apply PERMISSIONS; split; [|exact ADDRESS].
      eapply Mem.store_valid_access_2; [exact RAW|exact VALID].
    + exact TAIL.
Qed.

Theorem indexed_bound_alias_scan_sound out bound fuel point entry :
  indexed_bound_alias_accept out bound fuel point entry = true ->
  forall k, point <= k < point + Z.of_nat fuel -> k < Int.signed (indexed_bound_word bound entry) ->
    indexed_alias_flag out bound k entry = false.
Proof.
  revert point; induction fuel as [|fuel IH]; intros point ACCEPT k RANGE ACTIVE;
    cbn [indexed_bound_alias_accept] in ACCEPT; [cbn in RANGE; lia|].
  destruct (indexed_bound_active_flag bound point entry) eqn:POINT.
  - apply andb_true_iff in ACCEPT as [APART TAIL].
    destruct (Z.eq_dec k point); [subst; apply negb_true_iff in APART; exact APART|].
    eapply IH; [exact TAIL|rewrite Nat2Z.inj_succ in RANGE; lia|exact ACTIVE].
  - unfold indexed_bound_active_flag in POINT; apply Z.ltb_ge in POINT; lia.
Qed.
Print Assumptions indexed_bound_alias_scan_run.
Print Assumptions indexed_bound_alias_scan_sound.
