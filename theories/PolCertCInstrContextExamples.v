From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Globalenvs.
From compcert.cfrontend Require Import Ctypes Clight Csem.
From polcert.src Require Import CTy CState CInstr PolyBase.
From Guard Require Import PolCertCInstrContext PolCertCompatibilityAudit
  PolCertArrayExamples PolCertStoreSwap.
Import ListNotations.
Open Scope Z_scope.

Module Snapshot := CInstrContext DecimalNames.
Module C := Snapshot.Context.
Module Physical := Snapshot.Physical.
Module L := Snapshot.L.
Module Stores := PolCertStoreSwap DecimalNames.
Module Legacy := CompatibilityAudit DecimalNames.

Definition one_parameter_temps : temp_env :=
  PTree.set 3%positive (Vint Int.one) (PTree.empty val).
Definition array_declarations := [(1%positive, Physical.Ty.arr_type_intro Physical.Ty.int32s [2])].
Definition context_instruction :=
  Physical.Iassign (Physical.Aarr 1%positive (Physical.MAsingleton (Physical.MAval 0)) Physical.Ty.int32s)
    (Physical.Eval (Vint (Int.repr 7)) Physical.Ty.int32s).
Definition context_cell : MemCell := {| arr_id := 1%positive; arr_index := [0] |}.

Lemma context_instruction_from_store b memory result :
  Mem.store Mint32 memory b 0 (Vint (Int.repr 7)) = Some result ->
  Physical.instr_semantics context_instruction [] [context_cell] []
    (Stores.array_state 1%positive 2 b memory) (Stores.array_state 1%positive 2 b result).
Proof.
  intro STORE; eapply Physical.IassignSem with (v := Vint (Int.repr 7)).
  - eapply Physical.AccessArr; [reflexivity | constructor; constructor].
  - constructor.
  - eapply Physical.State.write_cell_intro with
      (ge := Stores.empty_globals) (e := Stores.array_locals 1%positive 2 b)
      (m := memory) (m' := result) (b := b) (ty := Stores.B.A.array_type 2)
      (ty' := Physical.State.Ty.arr_type_intro Physical.State.Ty.int32s [2])
      (ofs := 0) (chunk := Mint32);
      try reflexivity; try exact STORE; try apply Physical.State.eq_refl.
Qed.

Lemma context_array_nonalias b memory : Physical.NonAlias (Stores.array_state 1%positive 2 b memory).
Proof. exact (@Stores.projected_nonalias 1%positive 2 b memory). Qed.

Definition context_loop : L.t :=
  (L.Loop (L.Constant 0) (L.Var 0)
    (L.Instr context_instruction []),
   [3%positive], array_declarations).

Lemma one_parameter_initializes ge locals memory :
  C.InitEnv [3%positive] [1]
    (Snapshot.context_state ge locals one_parameter_temps memory).
Proof.
  apply Snapshot.defined_context_initializes; constructor; [|constructor].
  exists Int.one; split; [apply PTree.gss | reflexivity].
Qed.

Lemma allocated_array_compatible b memory :
  Mem.range_perm memory b 0 8 Cur Writable ->
  C.Compat array_declarations
    (Snapshot.context_state Stores.empty_globals (Stores.array_locals 1%positive 2 b)
      one_parameter_temps memory).
Proof.
  intro PERMISSIONS; constructor; [|constructor].
  exists b, (Stores.B.A.array_type 2); split.
  - reflexivity.
  - split; [vm_compute; reflexivity | exact PERMISSIONS].
Qed.

(** A real allocated execution with a nonempty array declaration and a scalar
    context obtained from a Clight temporary. No logical parameter cell is
    allocated or stored in the physical memory. *)
Example actual_context_wrapped_loop_runs : exists b memory result,
  L.semantics context_loop
    (Snapshot.context_state Stores.empty_globals (Stores.array_locals 1%positive 2 b)
      one_parameter_temps memory)
    (Snapshot.context_state Stores.empty_globals (Stores.array_locals 1%positive 2 b)
      one_parameter_temps result) /\
  Mem.load Mint32 result b 0 = Some (Vint (Int.repr 7)).
Proof.
  destruct (Mem.alloc Mem.empty 0 8) as [memory b] eqn:ALLOC.
  assert (PERMISSIONS : Mem.range_perm memory b 0 8 Cur Writable).
  { intros offset RANGE; eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; eauto | constructor]. }
  assert (VALID : Mem.valid_access memory Mint32 b 0 Writable).
  { apply Mem.valid_access_freeable_any; eapply Mem.valid_access_alloc_same;
      [exact ALLOC | lia | cbn; lia | exists 0; reflexivity]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vint (Int.repr 7)) VALID) as [result STORE].
  exists b, memory, result; split; [|exact (Mem.load_store_same _ _ _ _ _ _ STORE)].
  eapply L.LSemaIntro with (env := [1]); [reflexivity | | | |].
  - apply allocated_array_compatible; exact PERMISSIONS.
  - apply context_array_nonalias.
  - apply one_parameter_initializes.
  - apply L.LLoop; cbn [L.eval_expr].
    econstructor; [|constructor].
    eapply L.LInstr with (wcs := [context_cell]) (rcs := []).
    split; [intro id; reflexivity |].
    apply context_instruction_from_store; exact STORE.
Qed.

Example legacy_cannot_run_declared_array code context first final :
  ~ Legacy.L.semantics (code, context,
    [(1%positive, Legacy.I.Ty.arr_type_intro Legacy.I.Ty.int32s [2])]) first final.
Proof.
  intro RUN; pose proof (Legacy.legacy_wrapped_loop_requires_empty_variables RUN) as EMPTY.
  discriminate EMPTY.
Qed.

Goal True. idtac "GUARDCERT_CONTEXT_EXAMPLES_BEGIN". exact Logic.I. Qed.
Print Assumptions actual_context_wrapped_loop_runs.
Print Assumptions legacy_cannot_run_declared_array.
Goal True. idtac "GUARDCERT_CONTEXT_EXAMPLES_END". exact Logic.I. Qed.
