From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs Smallstep Errors.
From compcert.cfrontend Require Import Ctypes Cop Csem Clight ClightBigstep.
From polcert.src Require Import PolyBase CState CInstr.
From polcert.lib Require Import Linalg.
From Guard Require Import AbstractGuard SemanticFacts AbstractSchedule DomainRestriction
  ClightGuard ClightCondition ClightPureExpr ClightIndexGuard ClightSyntaxEquality
  ClightStraightLine PolCertMemoryModel PolCertDynamicStore.
Import ListNotations.
Open Scope Z_scope.
Set Implicit Arguments.

Module PolCertStorePackage (Names : C_INSTR_NAMES).
Module Dynamic := PolCertDynamicStore Names.
Module Stores := Dynamic.Stores.
Module B := Stores.B.
Module R := B.R.
Module Scheduling := R.S.

Definition projected_locals id count s : Csem.env :=
  match (entry_env s) ! id with
  | Some (b, _) => Stores.array_locals id count b
  | None => match Genv.find_symbol (entry_ge s) id with
            | Some b => Stores.array_locals id count b
            | None => PTree.empty (block * type) end end.

Lemma projected_locals_base id count s b :
  B.array_base (entry_ge s) (entry_env s) id count b ->
  projected_locals id count s = Stores.array_locals id count b.
Proof. unfold projected_locals, B.array_base; intros [LOCAL|[LOCAL GLOBAL]];
  rewrite LOCAL, ?GLOBAL; reflexivity. Qed.

Definition array_domain id count first second s : Prop :=
  (exists b, B.array_base (entry_ge s) (entry_env s) id count b) /\ index_domain first second s.

Lemma array_domain_indices id count first second s :
  array_domain id count first second s -> index_domain first second s.
Proof. intros [_ DOMAIN]; exact DOMAIN. Qed.

Definition array_assumption count first second s :=
  exists x y, (entry_temps s) ! first = Some (Vint x) /\
    (entry_temps s) ! second = Some (Vint y) /\
    0 <= Int.signed x < count /\ 0 <= Int.signed y < count /\ Int.signed x <> Int.signed y.

Definition runtime_index index s :=
  match (entry_temps s) ! index with Some (Vint x) => Int.signed x | _ => 0 end.

Definition store_invocation id index value : Scheduling.invocation :=
  {| Scheduling.operation := Stores.instruction id index value;
     Scheduling.arguments := []; Scheduling.writes := [Stores.cell id index]; Scheduling.reads := [] |}.

Definition source_operations id first second left right s :=
  [store_invocation id (runtime_index first s) left; store_invocation id (runtime_index second s) right].
Definition candidate_operations id first second left right s :=
  [store_invocation id (runtime_index second s) right; store_invocation id (runtime_index first s) left].

Lemma variable_store_base fe ge e le m id count index value trace le' m' outcome :
  exec_stmt fe ge e le m (Dynamic.variable_store id count index value) trace le' m' outcome ->
  exists b, B.array_base ge e id count b.
Proof.
  intro RUN; inversion RUN; subst.
  match goal with LV : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion LV; subst end.
  match goal with ADD : eval_expr _ _ _ _ (Ebinop _ _ _ _) _ |- _ =>
    apply scalar_binary_inv in ADD as [base [operand [BASE [INDEX OP]]]] end.
  destruct (B.array_value_inv BASE) as [b [VALUE ADDRESS]]; eauto.
Qed.

Lemma variable_pair_base fe ge e le m id count first second left right le' m' :
  exec_stmt fe ge e le m (Dynamic.variable_pair id count first second left right) E0 le' m' Out_normal ->
  exists b, B.array_base ge e id count b.
Proof.
  intro RUN; inversion RUN; subst; [|contradiction].
  eapply variable_store_base; eassumption.
Qed.

Definition dynamic_bridge id count first second left right source
  (BOUND : B.A.array_bound_ok count = true)
  (FLAT : flatten_region source = [Dynamic.variable_store id count first left;
                                  Dynamic.variable_store id count second right]) :
  R.schedule_bridge source (Dynamic.variable_pair id count second first right left).
Proof.
  refine {| R.bridge_domain := array_domain id count first second;
    R.bridge_assumption := array_assumption count first second;
    R.bridge_globalenv := Stores.empty_globals;
    R.bridge_locals := projected_locals id count;
    R.bridge_source := source_operations id first second left right;
    R.bridge_candidate := candidate_operations id first second left right |}.
  - intros temps p e le m le' m' SOURCE.
    assert (RUN : exec_stmt (adapter_entry temps) (globalenv p) e le m
      (Dynamic.variable_pair id count first second left right) E0 le' m' Out_normal).
    { eapply flattened_pair_execution; eauto. }
    split; [eapply variable_pair_base; exact RUN |].
    exact (proj1 (Dynamic.variable_pair_domain RUN)).
  - intros temps p e le m le' m' SOURCE [x [y [X [Y [RX [RY NE]]]]]].
    cbn [entry_temps] in X, Y.
    assert (RUN : exec_stmt (adapter_entry temps) (globalenv p) e le m
      (Dynamic.variable_pair id count first second left right) E0 le' m' Out_normal).
    { eapply flattened_pair_execution; eauto. }
    apply (proj1 (@Dynamic.variable_pair_constant (adapter_entry temps) (globalenv p) e le m
      id count first second left right x y le' m' X Y)) in RUN.
    destruct (Stores.store_pair_decode RX RY BOUND RUN) as [b [middle [BASE [TEMPS [LEFT RIGHT]]]]].
    split; [exact TEMPS |].
    exists (Stores.array_state id count b m').
    rewrite (@projected_locals_base id count (Entry (globalenv p) e le m) b BASE).
    unfold source_operations, runtime_index; cbn [entry_temps]; rewrite X, Y.
    split; [|apply memory_view_refl].
    destruct (B.A.array_bound_ok_sound count BOUND) as [POS _].
    eapply schedule_cons with (t := Stores.array_state id count b middle).
    + exact (@Stores.instruction_from_store id count (Int.signed x) left b m middle POS RX LEFT).
    + eapply schedule_cons; [exact (@Stores.instruction_from_store id count (Int.signed y) right b middle m' POS RY RIGHT) |constructor].
  - intros temps p e le m post [[b BASE] DOMAIN] [x [y [X [Y [RX [RY NE]]]]]] RUN.
    cbn [entry_temps] in X, Y.
    rewrite (@projected_locals_base id count (Entry (globalenv p) e le m) b BASE) in RUN |- *.
    unfold candidate_operations, runtime_index in RUN; cbn [entry_temps] in RUN; rewrite X, Y in RUN.
    inversion RUN; subst.
    match goal with TAIL : schedule_run _ [_] _ _ |- _ => inversion TAIL; subst end.
    match goal with DONE : schedule_run _ [] _ _ |- _ => inversion DONE; subst end.
    match goal with HEAD : instruction_run _ (store_invocation id (Int.signed y) right) _ ?middle |- _ =>
      destruct (@Stores.instruction_to_store id count (Int.signed y) right b m
        (Stores.array_state id count b m) middle
        (memory_view_refl Stores.empty_globals (Stores.array_locals id count b) m) HEAD)
        as [middle_memory [RIGHT VIEW]] end.
    match goal with HEAD : instruction_run _ (store_invocation id (Int.signed x) left) _ post |- _ =>
      destruct (@Stores.instruction_to_store id count (Int.signed x) left b middle_memory _ post VIEW HEAD)
        as [final_memory [LEFT FINAL_VIEW]] end.
    exists final_memory; split; [|exact FINAL_VIEW].
    apply (proj2 (@Dynamic.variable_pair_constant (adapter_entry temps) (globalenv p) e le m
      id count second first right left y x le final_memory Y X)).
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := middle_memory);
      eapply B.constant_store_run; eauto.
Defined.

Lemma independent_store_invocations id first second left right : first <> second ->
  independent Scheduling.model (store_invocation id first left) (store_invocation id second right).
Proof.
  intro DISTINCT.
  assert (DIFFERENT : cell_neq (Stores.cell id first) (Stores.cell id second)).
  { right; cbn [Stores.cell]; intro EQ; rewrite <- is_eq_veq in EQ.
    change ((first =? second) && true = true) in EQ.
    apply andb_true_iff in EQ as [EQ _]; apply Z.eqb_eq in EQ; contradiction. }
  change (Forall (fun wc2 => Forall (fun wc1 => cell_neq wc1 wc2) [Stores.cell id first]) [Stores.cell id second] /\
    Forall (fun rc2 => Forall (fun wc1 => cell_neq wc1 rc2) [Stores.cell id first]) [] /\
    Forall (fun wc2 => Forall (fun rc1 => cell_neq rc1 wc2) []) [Stores.cell id second]).
  split; [constructor; [constructor; [exact DIFFERENT |constructor] |constructor] |].
  split; repeat constructor.
Qed.

Definition dynamic_package id count first second left right source
  (BOUND : B.A.array_bound_ok count = true)
  (FLAT : flatten_region source = [Dynamic.variable_store id count first left;
                                  Dynamic.variable_store id count second right]) : R.schedule_region_package source.
Proof.
  assert (COUNT : Int.min_signed <= count <= Int.max_signed).
  { destruct (B.A.array_bound_ok_sound count BOUND) as [POS [UP _]].
    change (count <= 2147483647) in UP; change (-2147483648 <= count <= 2147483647); lia. }
  refine {| R.package_candidate := Dynamic.variable_pair id count second first right left;
    R.package_bridge := @dynamic_bridge id count first second left right source BOUND FLAT;
    R.package_atoms := index_atom;
    R.package_dimension := restrict_dimension (@array_domain_indices id count first second)
      (index_dimension count first second);
    R.package_primitives := restrict_primitives (@array_domain_indices id count first second)
      (index_dimension count first second) (index_primitives first second COUNT);
    R.package_formula := independent_indices |}.
  intros s [[b BASE] DOMAIN] PROPERTY.
  change (formula_property (index_property count first second) independent_indices s) in PROPERTY.
  destruct (independent_indices_property PROPERTY) as [x [y [X [Y [RX [RY NE]]]]]].
  change (array_assumption count first second s /\
    Stores.I.NonAlias (Stores.empty_globals, projected_locals id count s, entry_memory s) /\
    schedule_certificate Scheduling.model (source_operations id first second left right s)
      (candidate_operations id first second left right s)).
  split; [exists x, y; repeat split; tauto |].
  rewrite (@projected_locals_base id count s b BASE).
  split; [apply Stores.projected_nonalias |].
  unfold source_operations, candidate_operations, runtime_index; rewrite X, Y.
  apply certificate_swap; apply independent_store_invocations; exact NE.
Defined.

Definition propose_dynamic_package id count first second left right source : option (R.schedule_region_package source) :=
  match Bool.bool_dec (B.A.array_bound_ok count) true with
  | left BOUND =>
    match @Stdlib.Lists.List.list_eq_dec statement statement_eq (flatten_region source)
      [Dynamic.variable_store id count first left; Dynamic.variable_store id count second right] with
    | left FLAT => Some (@dynamic_package id count first second left right source BOUND FLAT)
    | right _ => None end
  | right _ => None end.

Definition select_dynamic_package id count first second left right :=
  R.select_schedule_region (propose_dynamic_package id count first second left right).

Theorem select_dynamic_package_sound id count first second left right source target :
  select_dynamic_package id count first second left right source = Some target ->
  ClightRegionRewrite.region_contract source target.
Proof. apply R.select_schedule_region_sound. Qed.

Definition compile_packaged_stores id count first second left right :=
  R.compile_schedule_regions (propose_dynamic_package id count first second left right).

Theorem compile_packaged_stores_correct id count first second left right p target :
  compile_packaged_stores id count first second left right p = OK target ->
  backward_simulation (Csem.semantics p) (Asm.semantics target).
Proof. apply R.compile_schedule_regions_correct. Qed.

Goal True. idtac "GUARDCERT_STORE_PACKAGE_BASELINE_BEGIN". exact Logic.I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "GUARDCERT_STORE_PACKAGE_ADAPTER_BEGIN". exact Logic.I. Qed.
Print Assumptions dynamic_package.
Print Assumptions select_dynamic_package_sound.
Print Assumptions compile_packaged_stores_correct.
Goal True. idtac "GUARDCERT_STORE_PACKAGE_ASSUMPTIONS_END". exact Logic.I. Qed.
End PolCertStorePackage.
