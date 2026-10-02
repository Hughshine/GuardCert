From Stdlib Require Import List ZArith NArith String DecimalString Lia.
From compcert.lib Require Import Integers Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight Csem ClightBigstep.
From polcert.src Require Import OpenScop PolyBase CTy CState CInstr.
From Guard Require Import PolCertArrayClight PolCertMemoryModel.
Import ListNotations.
Open Scope Z_scope.

(** Total names for these standalone examples. File-exchange bindings are
    separate from memory semantics; no naming operation implements execution. *)
Module DecimalNames <: C_INSTR_NAMES.
Definition ident_to_varname (id : ident) : varname :=
  NilZero.string_of_uint (Pos.to_uint id).
Definition varname_to_ident (name : varname) : ident :=
  match NilZero.uint_of_string name with
  | Some digits => match Pos.of_uint digits with Npos id => id | N0 => 1%positive end
  | None => 1%positive end.
Definition bind_ident_varname (bindings : list (ident * varname)) : list ident := map fst bindings.
Definition iterator_to_varname (index : nat) : varname :=
  String.append "giter_" (ident_to_varname (Pos.of_succ_nat index)).
End DecimalNames.

Module Array := PolCertArrayClight DecimalNames.
Module I := Array.I.
Module L := Array.L.

Definition sample_arrays := [(1%positive, 64); (2%positive, 64)].
Definition target_access := I.Aarr 1%positive (I.MAsingleton (I.MAvarz 0)) CTy.int32s.
Definition source_access := I.Aarr 2%positive (I.MAsingleton (I.MAvarz 0)) CTy.int32s.
Definition sample_instruction := I.Iassign target_access
  (I.Ebinop Oadd (I.Eaccess source_access CTy.int32s)
    (I.Eval (Vint Int.one) CTy.int32s) CTy.int32s).
Definition sample_loop := L.Loop (L.Constant 0) (L.Constant 64)
  (L.Instr sample_instruction [L.Var 0]).

Example array_update_compiles : exists code,
  Array.lower_instruction sample_arrays sample_instruction [Etempvar 3%positive type_int32s] = Some code.
Proof. vm_compute; eexists; reflexivity. Qed.

Example actual_array_loop_compiles : exists code,
  Array.compile_array_nested sample_arrays [] [] [] [(3%positive, 4%positive)] sample_loop = Some code.
Proof. vm_compute; eexists; reflexivity. Qed.

Definition nested_array_loop := L.Loop (L.Constant 0) (L.Constant 8)
  (L.Loop (L.Constant 0) (L.Sum (L.Var 0) (L.Constant 1))
    (L.Instr sample_instruction [L.Var 0])).

Example actual_nested_array_loop_compiles : exists code,
  Array.compile_array_nested sample_arrays [] [] []
    [(3%positive, 4%positive); (5%positive, 6%positive)] nested_array_loop = Some code.
Proof. vm_compute; eexists; reflexivity. Qed.

Example direct_undefined_copy_refused :
  Array.lower_instruction sample_arrays
    (I.Iassign target_access (I.Eaccess source_access CTy.int32s))
    [Etempvar 3%positive type_int32s] = None.
Proof. reflexivity. Qed.

Example invalid_array_size_refused :
  Array.lower_instruction [(1%positive, 0); (2%positive, 64)] sample_instruction
    [Etempvar 3%positive type_int32s] = None.
Proof. vm_compute; reflexivity. Qed.

Example live_counter_collision_refused :
  Array.compile_array_nested sample_arrays [] [] [3%positive]
    [(3%positive, 4%positive)] sample_loop = None.
Proof. vm_compute; reflexivity. Qed.

Example unsupported_index_tree_refused :
  Array.lower_access sample_arrays []
    (I.Aarr 1%positive (I.MAsingleton
      (I.MAbinop Oadd (I.MAval 1) (I.MAval 2))) CTy.int32s) = None.
Proof. reflexivity. Qed.

Example upstream_scalar_decoder_refuses_int : CTy.of_compcert_arrtype type_int32s = None.
Proof. reflexivity. Qed.

Definition source_globalenv : Csem.genv :=
  let '(ge, _, _) := CState.dummy_state in ge.
Definition zero_cell id := {| arr_id := id; arr_index := [0] |}.
Definition memory_locals destination input :=
  PTree.set 1%positive (destination, Array.array_type 64)
    (PTree.set 2%positive (input, Array.array_type 64) (PTree.empty (block * type))).

Lemma source_instruction_from_real_memory destination input memory memory' :
  Mem.load Mint32 memory input 0 = Some (Vint (Int.repr 7)) ->
  Mem.store Mint32 memory destination 0 (Vint (Int.repr 8)) = Some memory' ->
  I.instr_semantics sample_instruction [0] [zero_cell 1%positive] [zero_cell 2%positive]
    (source_globalenv, memory_locals destination input, memory)
    (source_globalenv, memory_locals destination input, memory').
Proof.
  intros LOAD STORE.
  eapply I.IassignSem with (v := Vint (Int.repr 8)).
  - eapply I.AccessArr; [reflexivity |].
    constructor; constructor; reflexivity.
  - eapply I.eval_binop with (v1 := Vint (Int.repr 7)) (v2 := Vint Int.one)
      (rcs1 := [zero_cell 2%positive]) (rcs2 := [])
      (ge := source_globalenv) (e := memory_locals destination input) (m := memory);
      [reflexivity | | constructor | vm_compute; reflexivity].
    eapply I.eval_access; [eapply I.AccessArr; [reflexivity | constructor; constructor; reflexivity] |].
    eapply CState.read_cell_intro with (b := input) (ty := Array.array_type 64)
      (ge := source_globalenv) (e := memory_locals destination input) (m := memory)
      (ty' := CTy.arr_type_intro CTy.int32s [64]) (ofs := 0) (chunk := Mint32);
      try exact LOAD; vm_compute; reflexivity.
  - eapply CState.write_cell_intro with
      (st := (source_globalenv, memory_locals destination input, memory))
      (st' := (source_globalenv, memory_locals destination input, memory'))
      (ge := source_globalenv) (e := memory_locals destination input)
      (m := memory) (m' := memory') (b := destination) (ty := Array.array_type 64)
      (ty' := CTy.arr_type_intro CTy.int32s [64]) (ofs := 0) (chunk := Mint32);
      try apply CState.eq_refl; try exact STORE; vm_compute; reflexivity.
Qed.

Example actual_source_instruction_runs : exists destination input memory memory',
  I.instr_semantics sample_instruction [0] [zero_cell 1%positive] [zero_cell 2%positive]
    (source_globalenv, memory_locals destination input, memory)
    (source_globalenv, memory_locals destination input, memory') /\
  Mem.load Mint32 memory' destination 0 = Some (Vint (Int.repr 8)).
Proof.
  destruct (Mem.alloc Mem.empty 0 256) as [first destination] eqn:FIRST.
  destruct (Mem.alloc first 0 256) as [second input] eqn:SECOND.
  assert (INPUT : Mem.valid_access second Mint32 input 0 Writable).
  { apply Mem.valid_access_freeable_any.
    eapply Mem.valid_access_alloc_same; [exact SECOND | lia | cbn; lia | exists 0; reflexivity]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vint (Int.repr 7)) INPUT) as [memory STORE_INPUT].
  assert (DESTINATION : Mem.valid_access memory Mint32 destination 0 Writable).
  { eapply Mem.store_valid_access_1; [exact STORE_INPUT |].
    eapply Mem.valid_access_alloc_other; [exact SECOND |].
    apply Mem.valid_access_freeable_any.
    eapply Mem.valid_access_alloc_same; [exact FIRST | lia | cbn; lia | exists 0; reflexivity]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vint (Int.repr 8)) DESTINATION) as [memory' STORE].
  exists destination, input, memory, memory'; split.
  - apply source_instruction_from_real_memory; [|exact STORE].
    exact (Mem.load_store_same _ _ _ _ _ _ STORE_INPUT).
  - exact (Mem.load_store_same _ _ _ _ _ _ STORE).
Qed.

Lemma example_array_environment destination input :
  Array.array_environment sample_arrays (memory_locals destination input).
Proof.
  intros id count COUNT; cbn [sample_arrays Array.array_count] in COUNT.
  destruct (Pos.eqb 1 id) eqn:FIRST.
  - apply Pos.eqb_eq in FIRST; subst id. inversion COUNT; subst count.
    exists destination; vm_compute; reflexivity.
  - destruct (Pos.eqb 2 id) eqn:SECOND; try discriminate.
    apply Pos.eqb_eq in SECOND; subst id. inversion COUNT; subst count.
    exists input; vm_compute; reflexivity.
Qed.

Example actual_clight_instruction_runs
  (function_entry : Clight.genv -> Clight.function -> list val -> mem ->
    Clight.env -> temp_env -> mem -> Prop) (ge : Clight.genv) :
  exists locals le memory memory' code destination,
    exec_stmt function_entry ge locals le memory code E0 le memory' Out_normal /\
    Mem.load Mint32 memory' destination 0 = Some (Vint (Int.repr 8)).
Proof.
  destruct actual_source_instruction_runs as [destination [input [memory [result [RUN LOAD]]]]].
  destruct array_update_compiles as [code CODE].
  pose (locals := memory_locals destination input).
  pose (le := PTree.set 3%positive (Vint Int.zero) (PTree.empty val)).
  assert (OPERANDS : Forall2 (Array.B.operand_view ge locals le memory)
    [Etempvar 3%positive type_int32s] [0]).
  { constructor; [split; [reflexivity | constructor; apply PTree.gss] | constructor]. }
  destruct (@Array.concrete_instruction_execution function_entry source_globalenv ge locals
    sample_arrays (example_array_environment destination input) sample_instruction
    [Etempvar 3%positive type_int32s] [0] code le memory
    (source_globalenv, locals, memory) (source_globalenv, locals, result)
    [zero_cell 1%positive] [zero_cell 2%positive] CODE OPERANDS RUN
    (memory_view_refl source_globalenv locals memory)) as [memory' [VIEW EXEC]].
  exists locals, le, memory, memory', code, destination; split; [exact EXEC |].
  unfold concrete_memory_view, CState.eq in VIEW.
  destruct VIEW as [_ [_ EQUIV]]. eapply memory_eq_load; eauto.
Qed.

Print Assumptions actual_source_instruction_runs.
Print Assumptions actual_clight_instruction_runs.
Print Assumptions Array.compile_array_nested_steps.
