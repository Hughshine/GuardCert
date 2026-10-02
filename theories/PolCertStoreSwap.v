From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Globalenvs Events Smallstep Errors.
From compcert.cfrontend Require Import Ctypes Csem Clight ClightBigstep.
From polcert.src Require Import PolyBase CTy CState CInstr.
From polcert.lib Require Import Linalg.
From Guard Require Import CompCertMemoryEquivalence PolCertMemoryModel PolCertStoreRegion
  ClightGuard ClightRegionRewrite.
From Guard Require Import ClightSyntaxEquality ClightRegionRewriteProof RegionCompiler
  ClightNoWrap ClightSignedCancel ClightStraightLine.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

Module PolCertStoreSwap (Names : C_INSTR_NAMES).
Module B := PolCertStoreRegion Names.
Module R := B.R.
Module I := B.I.

Definition empty_globals : Csem.genv :=
  let '(ge, _, _) := CState.dummy_state in ge.
Definition array_locals id count b : Csem.env :=
  PTree.set id (b, B.A.array_type count) (PTree.empty (block * type)).
Definition array_state id count b (m : mem) : CState.t :=
  (empty_globals, array_locals id count b, m).
Definition cell id index := {| arr_id := id; arr_index := [index] |}.
Definition instruction id index value :=
  I.Iassign (I.Aarr id (I.MAsingleton (I.MAval index)) CTy.int32s)
    (I.Eval (Vint value) CTy.int32s).

Lemma projected_nonalias id count b m : I.NonAlias (array_state id count b m).
Proof.
  unfold I.NonAlias, CState.non_alias, array_state, CState.get_var_loc_type.
  intros first second bf bs tf ts FIRST SECOND DISTINCT.
  unfold array_locals in FIRST, SECOND.
  rewrite !PTree.gsspec in FIRST, SECOND.
  destruct (peq first id), (peq second id); subst;
    cbn [empty_globals CState.dummy_state CState.mkState
      Genv.find_var_info Genv.empty_genv PMap.get] in FIRST, SECOND;
    rewrite ?PTree.gempty in FIRST, SECOND; try discriminate; contradiction.
Qed.

Lemma singleton_offset_run count index : 0 < count -> 0 <= index < count ->
  CState.calc_offset (CTy.arr_type_intro CTy.int32s [count]) [index] = Some (4 * index).
Proof.
  intros POS RANGE.
  change ((if ((count >? 0) && true) && ((index >=? 0) && true)
    then if count <=? index then None else Some (4 * index) else None) = Some (4 * index)).
  assert (COUNT : (count >? 0) = true) by (apply Z.gtb_lt; lia).
  assert (INDEX : (index >=? 0) = true) by (apply Z.geb_le; lia).
  assert (BOUND : (count <=? index) = false) by (apply Z.leb_gt; lia).
  rewrite COUNT, INDEX, BOUND; reflexivity.
Qed.

Lemma instruction_from_store id count index value b m m' :
  0 < count -> 0 <= index < count ->
  Mem.store Mint32 m b (4 * index) (Vint value) = Some m' ->
  I.instr_semantics (instruction id index value) [] [cell id index] []
    (array_state id count b m) (array_state id count b m').
Proof.
  intros POS RANGE STORE.
  eapply I.IassignSem with (v := Vint value).
  - eapply I.AccessArr; [reflexivity | constructor; constructor].
  - constructor.
  - eapply CState.write_cell_intro with (ge := empty_globals)
      (e := array_locals id count b) (m := m) (m' := m') (b := b)
      (ty := B.A.array_type count) (ty' := CTy.arr_type_intro CTy.int32s [count])
      (ofs := 4 * index) (chunk := Mint32);
      try apply CState.eq_refl; try reflexivity; try exact STORE.
    + cbn [array_state CState.get_var_loc_type];
        unfold array_locals; rewrite PTree.gss; reflexivity.
    + apply singleton_offset_run; assumption.
Qed.

Lemma instruction_to_store id count index value b m source target :
  concrete_memory_view empty_globals (array_locals id count b) source m ->
  I.instr_semantics (instruction id index value) [] [cell id index] [] source target ->
  exists m', Mem.store Mint32 m b (4 * index) (Vint value) = Some m' /\
    concrete_memory_view empty_globals (array_locals id count b) target m'.
Proof.
  intros VIEW RUN; inversion RUN; subst.
  match goal with EVAL : I.eval_expr _ _ _ _ _ |- _ => inversion EVAL; subst end.
  assert (WRITE : CState.write_cell (cell id index) CTy.int32s (Vint value)
    (array_state id count b m) target).
  { eapply CState.write_cell_stable_under_eq; [exact VIEW | apply CState.eq_refl | eassumption]. }
  destruct (@concrete_write_normalize empty_globals (array_locals id count b) m target
    (cell id index) CTy.int32s (Vint value) WRITE)
    as [m' [block [ty [arrayty [offset [chunk
      [LOOKUP [ARRAY [BASE [OFFSET [MODE [STORE RESULT]]]]]]]]]]]].
  cbn [CState.get_var_loc_type cell] in LOOKUP.
  unfold array_locals in LOOKUP.
  rewrite PTree.gss in LOOKUP; inversion LOOKUP; subst block ty.
  change (Some (CTy.arr_type_intro CTy.int32s [count]) = Some arrayty) in ARRAY.
  inversion ARRAY; subst arrayty.
  cbn in MODE; inversion MODE; subst chunk.
  cbn [cell] in OFFSET.
  destruct (@B.A.singleton_offset count index offset OFFSET) as [_ [_ SAME]]. subst offset.
  exists m'; split; assumption.
Qed.

Theorem actual_cinstr_store_swap (id : ident) count first second left right b m middle final :
  0 < count -> 0 <= first < count -> 0 <= second < count -> first <> second ->
  Mem.store Mint32 m b (4 * first) (Vint left) = Some middle ->
  Mem.store Mint32 middle b (4 * second) (Vint right) = Some final ->
  exists swapped_middle swapped_final,
    Mem.store Mint32 m b (4 * second) (Vint right) = Some swapped_middle /\
    Mem.store Mint32 swapped_middle b (4 * first) (Vint left) = Some swapped_final /\
    memory_equivalent final swapped_final.
Proof.
  intros POS FIRST SECOND DISTINCT LEFT RIGHT.
  pose proof (@instruction_from_store id count first left b m middle POS FIRST LEFT) as RUN_LEFT.
  pose proof (@instruction_from_store id count second right b middle final POS SECOND RIGHT) as RUN_RIGHT.
  assert (DIFFERENT : cell_neq (cell id first) (cell id second)).
  { right; cbn [cell]; intro EQ; rewrite <- is_eq_veq in EQ.
    change ((first =? second) && true = true) in EQ.
    apply andb_true_iff in EQ as [EQ _]; apply Z.eqb_eq in EQ; contradiction. }
  assert (BC :
    Forall (fun wc2 => Forall (fun wc1 => cell_neq wc1 wc2) [cell id first]) [cell id second] /\
    Forall (fun rc2 => Forall (fun wc1 => cell_neq wc1 rc2) [cell id first]) [] /\
    Forall (fun wc2 => Forall (fun rc1 => cell_neq rc1 wc2) []) [cell id second]).
  { split; [constructor; [constructor; [exact DIFFERENT | constructor] | constructor] |].
    split; repeat constructor. }
  destruct (@I.bc_condition_implie_permutbility
    (instruction id first left) [] [cell id first] []
    (array_state id count b m) (array_state id count b middle) (array_state id count b final)
    (instruction id second right) [] [cell id second] []
    (projected_nonalias id count b m) (conj RUN_LEFT RUN_RIGHT) BC)
    as [swapped_state [swapped_final_state [RUN_RIGHT' [RUN_LEFT' EQ]]]].
  destruct (@instruction_to_store id count second right b m
    (array_state id count b m) swapped_state
    (memory_view_refl empty_globals (array_locals id count b) m) RUN_RIGHT')
    as [swapped_middle [RIGHT' VIEW]].
  destruct (@instruction_to_store id count first left b swapped_middle swapped_state swapped_final_state
    VIEW RUN_LEFT') as [swapped_final [LEFT' FINAL_VIEW]].
  exists swapped_middle, swapped_final; split; [exact RIGHT' | split; [exact LEFT' |]].
  exact (@R.memory_views_related empty_globals (array_locals id count b)
    (array_state id count b final) swapped_final_state final swapped_final EQ
    (memory_view_refl empty_globals (array_locals id count b) final) FINAL_VIEW).
Qed.

Definition store_pair id count first second left right :=
  Ssequence (B.constant_store id count first left) (B.constant_store id count second right).

Lemma store_pair_decode fe ge e le m id count first second left right le' final :
  0 <= first < count -> 0 <= second < count -> B.A.array_bound_ok count = true ->
  exec_stmt fe ge e le m (store_pair id count first second left right) E0 le' final Out_normal ->
  exists b middle, B.array_base ge e id count b /\ le' = le /\
    Mem.store Mint32 m b (4 * first) (Vint left) = Some middle /\
    Mem.store Mint32 middle b (4 * second) (Vint right) = Some final.
Proof.
  intros FIRST SECOND BOUND RUN; inversion RUN; subst; [|contradiction].
  match goal with HEAD : exec_stmt _ _ _ _ _ (B.constant_store _ _ first _) _ _ _ _ |- _ =>
    destruct (B.constant_store_silent HEAD) as [TRACE _]; subst;
    destruct (B.constant_store_inv FIRST BOUND HEAD) as [bf [BASE [TEMPS STORE]]]; subst end.
  match goal with TAIL : exec_stmt _ _ _ _ _ (B.constant_store _ _ second _) _ _ _ _ |- _ =>
    destruct (B.constant_store_silent TAIL) as [TRACE _]; subst;
    destruct (B.constant_store_inv SECOND BOUND TAIL) as [bs [BASE' [TEMPS' STORE']]]; subst end.
  assert (SAME : bf = bs) by (eapply B.array_base_unique; eauto). subst bs.
  exists bf; eexists; split; [exact BASE | split; [reflexivity | split; eassumption]].
Qed.

Theorem store_pair_endpoint fe ge e le m id count first second left right le' final :
  0 <= first < count -> 0 <= second < count -> first <> second -> B.A.array_bound_ok count = true ->
  exec_stmt fe ge e le m (store_pair id count first second left right) E0 le' final Out_normal ->
  exists swapped_final,
    exec_stmt fe ge e le m (store_pair id count second first right left) E0 le' swapped_final Out_normal /\
    memory_equivalent final swapped_final.
Proof.
  intros FIRST SECOND DISTINCT BOUND RUN.
  destruct (store_pair_decode FIRST SECOND BOUND RUN) as [b [middle [BASE [TEMPS [LEFT RIGHT]]]]].
  subst le'.
  destruct (B.A.array_bound_ok_sound count BOUND) as [POS _].
  destruct (@actual_cinstr_store_swap id count first second left right b m middle final
    POS FIRST SECOND DISTINCT LEFT RIGHT) as [swapped_middle [swapped_final [RIGHT' [LEFT' EQ]]]].
  exists swapped_final; split; [|exact EQ].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := swapped_middle) (le1 := le);
    eapply B.constant_store_run; eauto.
Qed.

Theorem store_pair_region_contract id count first second left right :
  0 <= first < count -> 0 <= second < count -> first <> second -> B.A.array_bound_ok count = true ->
  region_contract (store_pair id count first second left right) (store_pair id count second first right left).
Proof.
  intros FIRST SECOND DISTINCT BOUND temps p e le m le' final SOURCE f k.
  destruct (store_pair_endpoint FIRST SECOND DISTINCT BOUND SOURCE) as [target_memory [RUN EQ]].
  destruct (exec_stmt_steps (adapter_entry temps) p _ _ _ _ _ _ _ _ RUN f k)
    as [next [STEPS EXIT]]. inversion EXIT; subst next.
  exists target_memory; split; assumption.
Qed.

Definition pair_parameters_ok count first second :=
  B.A.array_bound_ok count && (0 <=? first) && (first <? count) &&
    (0 <=? second) && (second <? count) && negb (first =? second).

Lemma pair_parameters_ok_sound count first second : pair_parameters_ok count first second = true ->
  0 <= first < count /\ 0 <= second < count /\ first <> second /\ B.A.array_bound_ok count = true.
Proof.
  unfold pair_parameters_ok; rewrite !andb_true_iff, negb_true_iff,
    Z.eqb_neq, !Z.leb_le, !Z.ltb_lt; tauto.
Qed.

(** A concrete manual-candidate interface: check parameters, then bind the
    certificate to the exact source syntax, including all type attributes. *)
Theorem store_pair_flat_contract source id count first second left right :
  flatten_region source = [B.constant_store id count first left; B.constant_store id count second right] ->
  0 <= first < count -> 0 <= second < count -> first <> second -> B.A.array_bound_ok count = true ->
  region_contract source (store_pair id count second first right left).
Proof.
  intros FLAT FIRST SECOND DISTINCT BOUND temps p e le m le' final SOURCE f k.
  pose proof (@store_pair_region_contract id count first second left right FIRST SECOND DISTINCT BOUND)
    as CONTRACT.
  eapply CONTRACT; eapply flattened_pair_execution; eauto.
Qed.

Definition select_store_pair id count first second left right source : option statement :=
  if pair_parameters_ok count first second then
    match flatten_region source with
    | [head; tail] =>
        if statement_eq (Ssequence head tail) (store_pair id count first second left right)
        then Some (store_pair id count second first right left) else None
    | _ => None end
  else None.

Theorem select_store_pair_sound id count first second left right source target :
  select_store_pair id count first second left right source = Some target -> region_contract source target.
Proof.
  unfold select_store_pair; destruct (pair_parameters_ok count first second) eqn:OK;
    try discriminate.
  destruct (flatten_region source) as [|head [|tail [|extra rest]]] eqn:FLAT; try discriminate.
  destruct (statement_eq (Ssequence head tail) (store_pair id count first second left right)) as [EQ|];
    try discriminate.
  intro SELECT; inversion SELECT; subst.
  inversion EQ; subst head tail.
  destruct (@pair_parameters_ok_sound count first second OK) as [FIRST [SECOND [DISTINCT BOUND]]].
  eapply store_pair_flat_contract; eauto.
Qed.

Theorem store_pair_program_correct id count first second left right p :
  forward_simulation (semantics2 p)
    (semantics2 (ClightRegionRewrite.transform_program
      (select_store_pair id count first second left right) p)).
Proof. apply ClightRegionRewriteProof.transform_program_correct2, select_store_pair_sound. Qed.

Definition compile_store_pair id count first second left right :=
  compile_with_regions select_no_wrap select_signed_memory_rewrites
    (select_store_pair id count first second left right).

Theorem compile_store_pair_correct id count first second left right p target :
  compile_store_pair id count first second left right p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof.
  unfold compile_store_pair; apply compile_with_regions_correct.
  - exact select_no_wrap_sound.
  - exact (select_store_pair_sound id count first second left right).
  - exact select_signed_memory_rewrites_sound.
Qed.

Example distinct_stores_selected :
  select_store_pair 1%positive 2 0 1 (Int.repr 7) (Int.repr 8)
    (store_pair 1%positive 2 0 1 (Int.repr 7) (Int.repr 8)) =
  Some (store_pair 1%positive 2 1 0 (Int.repr 8) (Int.repr 7)).
Proof. vm_compute; reflexivity. Qed.
Example overlapping_stores_refused :
  select_store_pair 1%positive 2 0 0 (Int.repr 7) (Int.repr 8)
    (store_pair 1%positive 2 0 0 (Int.repr 7) (Int.repr 8)) = None.
Proof. vm_compute; reflexivity. Qed.
Example out_of_bounds_store_refused :
  select_store_pair 1%positive 2 0 2 (Int.repr 7) (Int.repr 8)
    (store_pair 1%positive 2 0 2 (Int.repr 7) (Int.repr 8)) = None.
Proof. vm_compute; reflexivity. Qed.
Example mismatched_source_refused :
  select_store_pair 1%positive 2 0 1 (Int.repr 7) (Int.repr 8)
    (store_pair 1%positive 2 0 1 (Int.repr 9) (Int.repr 8)) = None.
Proof. vm_compute; reflexivity. Qed.
Example frontend_association_selected :
  select_store_pair 1%positive 2 0 1 (Int.repr 7) (Int.repr 8)
    (Ssequence (Ssequence Sskip (B.constant_store 1%positive 2 0 (Int.repr 7)))
      (B.constant_store 1%positive 2 1 (Int.repr 8))) =
  Some (store_pair 1%positive 2 1 0 (Int.repr 8) (Int.repr 7)).
Proof. vm_compute; reflexivity. Qed.

Example allocated_store_pair_and_candidate_run
  (fe : Clight.genv -> Clight.function -> list val -> mem -> Clight.env -> temp_env -> mem -> Prop)
  (ge : Clight.genv) :
  exists b e le memory original candidate,
    exec_stmt fe ge e le memory (store_pair 1%positive 2 0 1 (Int.repr 7) (Int.repr 8))
      E0 le original Out_normal /\
    exec_stmt fe ge e le memory (store_pair 1%positive 2 1 0 (Int.repr 8) (Int.repr 7))
      E0 le candidate Out_normal /\
    Mem.load Mint32 candidate b 0 = Some (Vint (Int.repr 7)) /\
    Mem.load Mint32 candidate b 4 = Some (Vint (Int.repr 8)).
Proof.
  destruct (Mem.alloc Mem.empty 0 8) as [memory b] eqn:ALLOC.
  assert (VALID0 : Mem.valid_access memory Mint32 b 0 Writable).
  { apply Mem.valid_access_freeable_any.
    eapply Mem.valid_access_alloc_same; [exact ALLOC | lia | cbn; lia | exists 0; reflexivity]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vint (Int.repr 7)) VALID0) as [middle LEFT].
  assert (VALID4 : Mem.valid_access middle Mint32 b 4 Writable).
  { eapply Mem.store_valid_access_1; [exact LEFT |].
    apply Mem.valid_access_freeable_any.
    eapply Mem.valid_access_alloc_same; [exact ALLOC | lia | cbn; lia | exists 1; reflexivity]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vint (Int.repr 8)) VALID4) as [original RIGHT].
  pose (e := array_locals 1%positive 2 b).
  pose (le := PTree.empty val).
  assert (BASE : B.array_base ge e 1%positive 2 b).
  { left; unfold e, array_locals; apply PTree.gss. }
  assert (SOURCE : exec_stmt fe ge e le memory
    (store_pair 1%positive 2 0 1 (Int.repr 7) (Int.repr 8)) E0 le original Out_normal).
  { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := middle) (le1 := le);
      eapply B.constant_store_run; try exact BASE; try exact LEFT; try exact RIGHT;
      try (split; lia); vm_compute; reflexivity. }
  destruct (@store_pair_endpoint fe ge e le memory 1%positive 2 0 1
    (Int.repr 7) (Int.repr 8) le original ltac:(split; lia) ltac:(split; lia)
    ltac:(lia) ltac:(vm_compute; reflexivity) SOURCE) as [candidate [RUN EQ]].
  exists b, e, le, memory, original, candidate; split; [exact SOURCE | split; [exact RUN | split]].
  - eapply memory_equivalent_load; [exact EQ |].
    rewrite (@Mem.load_store_other Mint32 middle b 4 (Vint (Int.repr 8)) original RIGHT
      Mint32 b 0 ltac:(right; left; cbn; lia)).
    exact (Mem.load_store_same _ _ _ _ _ _ LEFT).
  - eapply memory_equivalent_load; [exact EQ | exact (Mem.load_store_same _ _ _ _ _ _ RIGHT)].
Qed.

Print Assumptions projected_nonalias.
Print Assumptions instruction_from_store.
Print Assumptions instruction_to_store.
Print Assumptions actual_cinstr_store_swap.
Print Assumptions store_pair_region_contract.
Goal True. idtac "GUARDCERT_STORE_SWAP_BASELINE_BEGIN". exact Logic.I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "GUARDCERT_STORE_SWAP_ADAPTER_BEGIN". exact Logic.I. Qed.
Print Assumptions compile_store_pair_correct.
Goal True. idtac "GUARDCERT_STORE_SWAP_ASSUMPTIONS_END". exact Logic.I. Qed.
End PolCertStoreSwap.
