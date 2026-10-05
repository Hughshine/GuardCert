From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events Globalenvs.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightNoWrap ClightPureExpr ClightRedundantSet ClightMatrixGuard
  ClightSameAddress ClightCountedLoop ClightCountedProtocol ClightFrontendLoopProtocol ClightTempFrame
  ClightMatrixStore ClightMatrixLoops CompCertStoreSchedule ClightRegionProgress ClightStraightLine.
From GuardInterface Require Import GuardedRewrite ClightReadonlyRewrite ClightReadonlyLoadedTreeSynthesis
  ClightReadonlyCellSwap ClightStableLoadBody ClightLoadedBoundSyntax ClightLoadedBoundGuard ClightLoadedMatrixSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition loaded_matrix_upper bound entry :=
  match (entry_temps entry) ! bound with
  | Some (Vptr b ofs) => match Mem.loadv Mint32 (entry_memory entry) (Vptr b ofs) with
    | Some (Vint word) => word | _ => Int.zero end
  | _ => Int.zero end.
Definition loaded_matrix_two_expr bound := Ebinop Oeq (signed_load bound) (matrix_constant 2) type_int32s.
Definition loaded_matrix_two_flag bound entry := Int.eq (loaded_matrix_upper bound entry) (Int.repr 2).
Definition loaded_matrix_block array entry :=
  match (entry_env entry) ! array with
  | Some (block, _) => Some block | None => Genv.find_symbol (entry_ge entry) array end.
Definition loaded_matrix_alias_expr array bound point :=
  Ebinop Oeq (Ebinop Oadd (Evar array matrix_array_type) (matrix_constant point) (Tpointer type_int32s noattr))
    (signed_pointer_temp bound) type_int32s.
Definition loaded_matrix_alias_flag array bound point entry :=
  match loaded_matrix_block array entry, (entry_temps entry) ! bound with
  | Some block, Some (Vptr q qofs) => address_flag block (Ptrofs.repr (4*point)) q qofs
  | _, _ => false end.
Definition loaded_matrix_alias_tree array bound :=
  Test (loaded_matrix_alias_expr array bound 0) (Decision false)
    (Test (loaded_matrix_alias_expr array bound 1) (Decision false)
      (Test (loaded_matrix_alias_expr array bound 2) (Decision false)
        (Test (loaded_matrix_alias_expr array bound 3) (Decision false) (Decision true)))).
Definition loaded_matrix_alias_accept array bound entry :=
  negb (loaded_matrix_alias_flag array bound 0 entry) && negb (loaded_matrix_alias_flag array bound 1 entry) &&
  negb (loaded_matrix_alias_flag array bound 2 entry) && negb (loaded_matrix_alias_flag array bound 3 entry).
Definition loaded_matrix_tree row bound columns array :=
  Test (register_guard row Int.zero)
    (Test (loaded_matrix_two_expr bound)
      (Test (register_guard columns (Int.repr 2)) (loaded_matrix_alias_tree array bound) (Decision false))
      (Decision false)) (Decision false).
Definition loaded_matrix_accept row bound columns array entry :=
  register_flag row Int.zero entry && loaded_matrix_two_flag bound entry &&
    register_flag columns (Int.repr 2) entry && loaded_matrix_alias_accept array bound entry.
Definition loaded_matrix_domain row bound outer_body entry :=
  loaded_bound_entry row bound entry /\ exists after final, forall fe,
    exec_stmt fe (entry_ge entry) (entry_env entry) (entry_temps entry) (entry_memory entry)
      (loaded_matrix_source row bound outer_body) E0 after final Out_normal.
Definition loaded_matrix_property row bound columns array entry :=
  register_equals row Int.zero tt entry /\ loaded_matrix_two_flag bound entry = true /\
    register_equals columns (Int.repr 2) tt entry /\
    forall point, 0 <= point <= 3 -> loaded_matrix_alias_flag array bound point entry = false.

Lemma loaded_matrix_block_known array entry block :
  matrix_array_binding (entry_ge entry) (entry_env entry) array block -> loaded_matrix_block array entry = Some block.
Proof. intros [LOCAL|[ABSENT GLOBAL]]; unfold loaded_matrix_block; [rewrite LOCAL|rewrite ABSENT]; auto. Qed.
Lemma loaded_matrix_two_test row bound entry : loaded_bound_entry row bound entry ->
  expression_test (loaded_matrix_two_expr bound) entry (loaded_matrix_two_flag bound entry).
Proof.
  intros [i [word [q [qofs [ITER [BOUND READ]]]]]].
  unfold loaded_matrix_two_flag, loaded_matrix_upper; rewrite BOUND, READ.
  exists (Val.of_bool (Int.eq word (Int.repr 2))); split; [|apply bool_of_bool].
  eapply eval_Ebinop with (v1 := Vint word) (v2 := Vint (Int.repr 2));
    [|constructor|reflexivity].
  apply eval_Elvalue with (loc := q) (ofs := qofs) (bf := Full).
  - apply eval_Ederef, eval_Etempvar; exact BOUND.
  - apply deref_loc_value with (chunk := Mint32); [reflexivity|exact READ].
Qed.
Lemma loaded_matrix_alias_test array bound point entry block q qofs word :
  0 <= point <= 3 -> matrix_array_binding (entry_ge entry) (entry_env entry) array block ->
  (entry_temps entry) ! bound = Some (Vptr q qofs) ->
  Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some word ->
  writable_word (entry_memory entry) block (Ptrofs.repr (4*point)) ->
  expression_test (loaded_matrix_alias_expr array bound point) entry (loaded_matrix_alias_flag array bound point entry).
Proof.
  intros RANGE ARRAY BOUND READ WORD; exists (Val.of_bool (address_flag block (Ptrofs.repr (4*point)) q qofs)); split.
  - eapply eval_Ebinop with (v1 := Vptr block (Ptrofs.repr (4*point))) (v2 := Vptr q qofs).
    + eapply eval_Ebinop with (v1 := Vptr block Ptrofs.zero) (v2 := Vint (Int.repr point));
        [apply matrix_reference_evaluation; exact ARRAY|constructor|apply matrix_pointer_add; exact RANGE].
    + constructor; exact BOUND.
    + change (cmp_ptr (entry_memory entry) Ceq (Vptr block (Ptrofs.repr (4*point))) (Vptr q qofs) =
        Some (Val.of_bool (address_flag block (Ptrofs.repr (4*point)) q qofs))).
      apply pointer_equality_value; [apply writable_word_valid_pointer; exact WORD|eapply loaded_address_valid; exact READ].
  - unfold loaded_matrix_alias_flag; rewrite (@loaded_matrix_block_known array entry _ ARRAY), BOUND;
      apply bool_of_bool.
Qed.
Lemma loaded_matrix_alias_apart array bound point entry block q qofs :
  matrix_array_binding (entry_ge entry) (entry_env entry) array block ->
  (entry_temps entry) ! bound = Some (Vptr q qofs) ->
  loaded_matrix_alias_flag array bound point entry = false -> Vptr block (Ptrofs.repr (4*point)) <> Vptr q qofs.
Proof.
  intros ARRAY BOUND APART SAME; inversion SAME; subst.
  unfold loaded_matrix_alias_flag, address_flag in APART.
  rewrite (@loaded_matrix_block_known array entry _ ARRAY), BOUND,
    Pos.eqb_refl, Ptrofs.eq_true in APART; discriminate.
Qed.
Lemma loaded_matrix_store_word block point value memory final : 0 <= point <= 3 ->
  store_action_run (matrix_cell block point value) memory final -> writable_word memory block (Ptrofs.repr (4*point)).
Proof.
  intros RANGE STORE; split; rewrite Ptrofs.unsigned_repr by (apply matrix_small_offset_bound; lia).
  - eapply Mem.store_valid_access_3; exact STORE.
  - change (size_chunk Mint32) with 4.
    pose proof (@matrix_small_offset_bound (4*point+4) ltac:(lia)); unfold Ptrofs.max_unsigned in H; lia.
Qed.
Lemma loaded_matrix_storev block point value memory final : 0 <= point <= 3 ->
  store_action_run (matrix_cell block point value) memory final ->
  Mem.storev Mint32 memory (Vptr block (Ptrofs.repr (4*point))) (Vint (Int.repr value)) = Some final.
Proof.
  intros RANGE STORE; apply word_storev_from_store; [eapply loaded_matrix_store_word; eassumption|].
  rewrite Ptrofs.unsigned_repr by (apply matrix_small_offset_bound; lia); exact STORE.
Qed.
Lemma loaded_matrix_permission_back block point value memory final other ofs :
  store_action_run (matrix_cell block point value) memory final ->
  writable_word final other ofs -> writable_word memory other ofs.
Proof. intros STORE [ACCESS END]; split; [eapply Mem.store_valid_access_2; eassumption|exact END]. Qed.

(** Addresses in the second row are justified only after both first-row
    checks succeed. The proof follows the actual source execution, while all
    runtime tests read the original entry. *)
Theorem loaded_matrix_alias_run fe ge locals le memory array row bound column columns body outer_body after final q qofs :
  row <> column -> row <> bound -> column <> bound -> row <> columns -> column <> columns ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  le ! row = Some (Vint (Int.repr 0)) -> le ! columns = Some (Vint (Int.repr 2)) ->
  le ! bound = Some (Vptr q qofs) -> Mem.loadv Mint32 memory (Vptr q qofs) = Some (Vint (Int.repr 2)) ->
  exec_stmt fe ge locals le memory (loaded_matrix_source row bound outer_body) E0 after final Out_normal ->
  decision_run (Entry ge locals le memory) (loaded_matrix_alias_tree array bound)
    (loaded_matrix_alias_accept array bound (Entry ge locals le memory)).
Proof.
  intros RC RQ CQ RM CM BODY OUTER ROW COLS BOUND READ SOURCE.
  destruct (@loaded_matrix_row_step fe ge locals le memory array row bound column columns body outer_body after final 0 q qofs
    RC CM BODY OUTER ltac:(lia) ROW BOUND READ COLS SOURCE)
    as [block [middle [row_memory [ARRAY [FIRST [SECOND TAIL]]]]]].
  change (store_action_run (matrix_cell block 0 1) memory middle) in FIRST.
  change (store_action_run (matrix_cell block 1 2) middle row_memory) in SECOND.
  unfold loaded_matrix_alias_tree, loaded_matrix_alias_accept.
  eapply run_test; [eapply loaded_matrix_alias_test; [lia|exact ARRAY|exact BOUND|exact READ|
    eapply loaded_matrix_store_word; [lia|exact FIRST]]|].
  destruct (loaded_matrix_alias_flag array bound 0 (Entry ge locals le memory)) eqn:A0; cbn; [constructor|].
  assert (READ1 : Mem.loadv Mint32 middle (Vptr q qofs) = Some (Vint (Int.repr 2))).
  { eapply mint32_load_survives_apart_store; [exact (@loaded_matrix_storev block 0 1 memory middle ltac:(lia) FIRST)|exact READ|].
    exact (@loaded_matrix_alias_apart array bound 0 (Entry ge locals le memory) block q qofs ARRAY BOUND A0). }
  eapply run_test; [eapply loaded_matrix_alias_test; [lia|exact ARRAY|exact BOUND|exact READ|
    eapply loaded_matrix_permission_back; [exact FIRST|eapply loaded_matrix_store_word; [lia|exact SECOND]]]|].
  destruct (loaded_matrix_alias_flag array bound 1 (Entry ge locals le memory)) eqn:A1; cbn; [constructor|].
  assert (READ2 : Mem.loadv Mint32 row_memory (Vptr q qofs) = Some (Vint (Int.repr 2))).
  { eapply mint32_load_survives_apart_store; [exact (@loaded_matrix_storev block 1 2 middle row_memory ltac:(lia) SECOND)|exact READ1|].
    exact (@loaded_matrix_alias_apart array bound 1 (Entry ge locals le memory) block q qofs ARRAY BOUND A1). }
  set (next := PTree.set row (Vint (Int.repr 1)) (PTree.set column (Vint (Int.repr 2)) le)).
  assert (Q1 : next ! bound = Some (Vptr q qofs)) by (unfold next; rewrite !PTree.gso by congruence; exact BOUND).
  assert (M1 : next ! columns = Some (Vint (Int.repr 2))).
  { unfold next; rewrite PTree.gso by congruence; destruct (peq columns column); [subst; apply PTree.gss|].
    rewrite PTree.gso by congruence; exact COLS. }
  destruct (@loaded_matrix_row_step fe ge locals next row_memory array row bound column columns body outer_body after final 1 q qofs
    RC CM BODY OUTER ltac:(lia) (PTree.gss _ _ _) Q1 READ2 M1 TAIL)
    as [other [middle2 [last_memory [OTHER_ARRAY [THIRD [FOURTH TAIL2]]]]]].
  assert (SAME : block = other) by (eapply matrix_array_binding_unique; eassumption); subst other.
  change (store_action_run (matrix_cell block 2 11) row_memory middle2) in THIRD.
  change (store_action_run (matrix_cell block 3 12) middle2 last_memory) in FOURTH.
  eapply run_test; [eapply loaded_matrix_alias_test; [lia|exact ARRAY|exact BOUND|exact READ|]|].
  - eapply loaded_matrix_permission_back; [exact FIRST|].
    eapply loaded_matrix_permission_back; [exact SECOND|eapply loaded_matrix_store_word; [lia|exact THIRD]].
  - destruct (loaded_matrix_alias_flag array bound 2 (Entry ge locals le memory)); cbn; [constructor|].
    eapply run_test; [eapply loaded_matrix_alias_test; [lia|exact ARRAY|exact BOUND|exact READ|]|].
    + eapply loaded_matrix_permission_back; [exact FIRST|].
      eapply loaded_matrix_permission_back; [exact SECOND|].
      eapply loaded_matrix_permission_back; [exact THIRD|eapply loaded_matrix_store_word; [lia|exact FOURTH]].
    + destruct (loaded_matrix_alias_flag array bound 3 (Entry ge locals le memory)); constructor.
Qed.

Lemma loaded_matrix_prefix_facts row bound outer_body entry : loaded_matrix_domain row bound outer_body entry ->
  register_flag row Int.zero entry = true -> loaded_matrix_two_flag bound entry = true ->
  exists q qofs, (entry_temps entry) ! row = Some (Vint (Int.repr 0)) /\
    (entry_temps entry) ! bound = Some (Vptr q qofs) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr q qofs) = Some (Vint (Int.repr 2)).
Proof.
  intros [[i [upper [q [qofs [ITER [BOUND READ]]]]]] COMPLETE] ZERO TWO.
  assert (ROW : (entry_temps entry) ! row = Some (Vint Int.zero))
    by (apply register_flag_evidence; [exists i; exact ITER|exact ZERO]).
  unfold loaded_matrix_two_flag, loaded_matrix_upper in TWO; rewrite BOUND, READ in TWO.
  apply Int.same_if_eq in TWO; subst upper; exists q, qofs; repeat split; assumption.
Qed.
Theorem loaded_matrix_guard_run array row bound column columns body outer_body entry :
  row <> column -> row <> bound -> column <> bound -> row <> columns -> column <> columns ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  loaded_matrix_domain row bound outer_body entry ->
  decision_run entry (loaded_matrix_tree row bound columns array) (loaded_matrix_accept row bound columns array entry).
Proof.
  intros RC RQ CQ RM CM BODY OUTER DOMAIN.
  destruct DOMAIN as [ENTRY [after [final COMPLETE]]].
  destruct ENTRY as [i [upper [q [qofs [ITER [BOUND READ]]]]]].
  assert (ENTRY : loaded_bound_entry row bound entry) by (do 4 eexists; repeat split; eassumption).
  assert (DOMAIN : loaded_matrix_domain row bound outer_body entry) by (split; [exact ENTRY|eauto]).
  assert (ITER_DOMAIN : register_domain row entry) by (exists i; exact ITER).
  unfold loaded_matrix_tree, loaded_matrix_accept.
  eapply run_test; [apply register_expression_test; exact ITER_DOMAIN|].
  destruct (register_flag row Int.zero entry) eqn:ZERO; cbn; [|constructor].
  eapply run_test; [eapply loaded_matrix_two_test; exact ENTRY|].
  destruct (loaded_matrix_two_flag bound entry) eqn:TWO; cbn; [|constructor].
  destruct (loaded_matrix_prefix_facts DOMAIN ZERO TWO) as [other [ofs [ROW [PTR LOAD]]]].
  assert (ACTIVE : expression_test (loaded_bound_test row bound) entry true).
  { replace true with (Int.lt (Int.repr 0) (Int.repr 2)) by reflexivity.
    destruct entry; eapply loaded_bound_test_eval; eassumption. }
  assert (M_DOMAIN : register_domain columns entry).
  { destruct entry as [ge locals le memory]; exact (@loaded_matrix_columns_domain (adapter_entry true) ge locals le memory
      array row bound column columns body outer_body after final CM BODY OUTER ACTIVE (COMPLETE (adapter_entry true))). }
  eapply run_test; [apply register_expression_test; exact M_DOMAIN|].
  destruct (register_flag columns (Int.repr 2) entry) eqn:COLS; cbn; [|constructor].
  pose proof (register_flag_evidence (Int.repr 2) M_DOMAIN COLS) as M.
  destruct entry as [ge locals le memory]; cbn in ROW, PTR, LOAD, M, COMPLETE |- *.
  exact (@loaded_matrix_alias_run (adapter_entry true) ge locals le memory array row bound column columns body outer_body
    after final other ofs RC RQ CQ RM CM BODY OUTER ROW M PTR LOAD (COMPLETE (adapter_entry true))).
Qed.
Theorem loaded_matrix_guard_sound array row bound column columns body outer_body entry :
  row <> column -> row <> bound -> column <> bound -> row <> columns -> column <> columns ->
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  loaded_matrix_domain row bound outer_body entry -> loaded_matrix_accept row bound columns array entry = true ->
  loaded_matrix_property row bound columns array entry.
Proof.
  intros RC RQ CQ RM CM BODY OUTER DOMAIN ACCEPT.
  unfold loaded_matrix_accept, loaded_matrix_alias_accept in ACCEPT; repeat rewrite andb_true_iff in ACCEPT.
  destruct ACCEPT as [[[ZERO TWO] COLS] [[[A0 A1] A2] A3]].
  destruct DOMAIN as [ENTRY COMPLETE].
  assert (D : loaded_matrix_domain row bound outer_body entry) by (split; assumption).
  destruct ENTRY as [i [upper [q [qofs [ITER REST]]]]].
  assert (I_DOMAIN : register_domain row entry) by (exists i; exact ITER).
  destruct (loaded_matrix_prefix_facts D ZERO TWO) as [other [ofs [ROW [PTR LOAD]]]].
  assert (ACTIVE : expression_test (loaded_bound_test row bound) entry true).
  { replace true with (Int.lt (Int.repr 0) (Int.repr 2)) by reflexivity.
    destruct entry; eapply loaded_bound_test_eval; eassumption. }
  destruct COMPLETE as [after [final SOURCE]].
  assert (M_DOMAIN : register_domain columns entry).
  { destruct entry as [ge locals le memory]; exact (@loaded_matrix_columns_domain (adapter_entry true) ge locals le memory
      array row bound column columns body outer_body after final CM BODY OUTER ACTIVE (SOURCE (adapter_entry true))). }
  unfold loaded_matrix_property; split; [apply register_flag_evidence; assumption|split; [exact TWO|split]].
  - apply register_flag_evidence; assumption.
  - apply negb_true_iff in A0, A1, A2, A3.
    intros point RANGE; assert (point = 0 \/ point = 1 \/ point = 2 \/ point = 3) by lia;
      destruct H as [H|[H|[H|H]]]; subst point; assumption.
Qed.
Definition loaded_matrix_condition fe O (observe : fragment_observation -> O -> Prop)
  array row bound column columns body outer_body
  (RC : row <> column) (RQ : row <> bound) (CQ : column <> bound) (RM : row <> columns) (CM : column <> columns)
  (BODY : flatten_region body = [matrix_store array row column])
  (OUTER : flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body]) :
  readonly_condition (readonly_clight_host fe observe) (loaded_matrix_domain row bound outer_body)
    (loaded_matrix_property row bound columns array) (loaded_matrix_tree row bound columns array).
Proof.
  constructor.
  - intros entry DOMAIN; eapply readonly_decision_run_safe.
    exact (@loaded_matrix_guard_run array row bound column columns body outer_body entry RC RQ CQ RM CM BODY OUTER DOMAIN).
  - intros entry DOMAIN; exists (loaded_matrix_accept row bound columns array entry), entry; split; [|reflexivity].
    exact (@loaded_matrix_guard_run array row bound column columns body outer_body entry RC RQ CQ RM CM BODY OUTER DOMAIN).
  - intros entry answer checked DOMAIN [RUN SAME]; split; [exact SAME|intro ACCEPT; subst answer].
    assert (VALUE : loaded_matrix_accept row bound columns array entry = true).
    { symmetry; eapply readonly_decision_determinate; [exact RUN|].
      exact (@loaded_matrix_guard_run array row bound column columns body outer_body entry RC RQ CQ RM CM BODY OUTER DOMAIN). }
    exact (@loaded_matrix_guard_sound array row bound column columns body outer_body entry RC RQ CQ RM CM BODY OUTER DOMAIN VALUE).
Defined.
Theorem loaded_matrix_domain_from_source fe ge locals le memory array row bound column columns body outer_body after final :
  flatten_region body = [matrix_store array row column] ->
  flatten_region outer_body = [matrix_reset column; frontend_counted_loop column columns body] ->
  exec_stmt fe ge locals le memory (loaded_matrix_source row bound outer_body) E0 after final Out_normal ->
  loaded_matrix_domain row bound outer_body (Entry ge locals le memory).
Proof.
  intros BODY OUTER SOURCE; split.
  - destruct (loaded_matrix_entry_test SOURCE) as [flag TEST].
    destruct (loaded_bound_test_facts TEST) as [i [upper [q [qofs [ITER [BOUND [READ FLAG]]]]]]].
    exists i, upper, q, qofs; repeat split; assumption.
  - exists after, final; intro other_fe.
    eapply quiet_execution_preserved; [split; [reflexivity|intros; reflexivity]|exact SOURCE|].
    exact (@loaded_matrix_source_quiet array row bound column columns body outer_body BODY OUTER).
Qed.
Print Assumptions loaded_matrix_alias_run.
Print Assumptions loaded_matrix_condition.
Print Assumptions loaded_matrix_domain_from_source.
