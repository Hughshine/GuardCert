From Stdlib Require Import List Bool ZArith Numbers.DecimalString.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase OpenScop.
From polcert.polygen Require Import StateTy TyTy InstrTy IterSemantics.
From polcert.lib Require Import ImpureAlarmConfig Linalg.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr.
Import ListNotations.
Set Implicit Arguments.

(** The computation depends only on its explicit operands and integer model
    parameters. It does not inspect the mutable memory or registry. *)
Module Type MEMORY_VALUE_CODE.
  Parameter t : Type.
  Parameter eq_dec : forall first second : t, {first = second} + {first <> second}.
  Parameter dummy : t.
  Parameter evaluate : list Z -> list val -> t -> option val.
End MEMORY_VALUE_CODE.

Record memory_value_instruction (code : Type) := MemoryValueInstruction {
  value_instruction_write : AccessFunction;
  value_instruction_reads : list AccessFunction;
  value_instruction_code : code
}.
Arguments MemoryValueInstruction {code}.

Module MakeMemoryValueInstr (Value : MEMORY_VALUE_CODE) <: INSTR.
Module State := GuardMemoryInstr.State.
Module Ty := GuardMemoryInstr.Ty.
Module IterSem := IterSem State.
Module IterSemImpure := IterSem.IterImpureSemantics CoreAlarmed.
Definition t := memory_value_instruction Value.t.
Definition memory_value_instruction_eq_dec : forall first second : t,
  {first = second} + {first <> second}.
Proof.
  intros [write reads expression] [other_write other_reads other_expression].
  destruct (affine_access_eq_dec write other_write) as [WRITE|NE]; [subst|right; congruence].
  destruct (@List.list_eq_dec AccessFunction affine_access_eq_dec reads other_reads) as [READS|NE]; [subst|right; congruence].
  destruct (Value.eq_dec expression other_expression) as [EXPR|NE]; [subst; left; reflexivity|right; congruence].
Defined.
Definition dummy_instr := MemoryValueInstruction (1%positive,[]) [] Value.dummy.
Definition ident := AST.ident.
Definition ident_eqb := Pos.eqb.
Definition ident_eqb_eq := Pos.eqb_eq.
Definition ident_to_openscop_ident (id : ident) := id.
Definition openscop_ident_to_ident (id : AST.ident) := id.
Definition ident_to_varname (id : ident) := NilZero.string_of_uint (Pos.to_uint id).
Definition varname_to_ident (name : varname) := match NilZero.uint_of_string name with
  | Some digits => Pos.of_nat (Nat.of_uint digits) | None => 1%positive end.
Definition bind_ident_varname (names : list (ident * varname)) := map fst names.
Definition iterator_to_varname (n : nat) := NilZero.string_of_uint (Nat.to_uint n).

Definition instr_semantics instruction parameters writes reads before after :=
  writes = [exact_cell (value_instruction_write instruction) parameters] /\
  reads = map (fun access => exact_cell access parameters) (value_instruction_reads instruction) /\
  footprint_run (exact_cell (value_instruction_write instruction) parameters) reads
    (fun values => Value.evaluate parameters values (value_instruction_code instruction)) before after.
Lemma instr_semantics_stable_under_state_eq instruction parameters writes reads before after before' after' :
  State.eq before before' -> State.eq after after' ->
  instr_semantics instruction parameters writes reads before after ->
  instr_semantics instruction parameters writes reads before' after'.
Proof. unfold State.eq; intros BEFORE AFTER RUN; subst before' after'; exact RUN. Qed.
Definition eqb first second := if memory_value_instruction_eq_dec first second then true else false.
Lemma eqb_eq first second : eqb first second = true <-> first = second.
Proof. unfold eqb; destruct (memory_value_instruction_eq_dec first second); intuition congruence. Qed.
Definition NonAlias := State.non_alias.
Definition InitEnv (names : list ident) (values : list Z) (_ : State.t) := length names = length values.
Definition Compat (_ : list (ident * Ty.t)) (_ : State.t) := True.
Lemma init_env_samelen names values state : InitEnv names values state -> length names = length values.
Proof. exact (fun SAME => SAME). Qed.
(** OpenScop export is optional in INSTR. This first instance is fed a checked
    PolyLang proposal directly; it does not export an external scheduler input. *)
Definition to_openscop (_ : t) (_ : list varname) : option OpenScop.ArrayStmt := None.
Definition waccess (instruction : t) := Some [value_instruction_write instruction].
Definition raccess (instruction : t) := Some (value_instruction_reads instruction).
Definition valid_access_function wl rl instruction := forall parameters before after writes reads,
  instr_semantics instruction parameters writes reads before after ->
  valid_access_cells parameters writes wl /\ valid_access_cells parameters reads rl.
Definition check_never_written names (instruction : t) :=
  negb (existsb (Pos.eqb (fst (value_instruction_write instruction))) names).
Definition access_function_checker wl rl (instruction : t) :=
  if @List.list_eq_dec AccessFunction affine_access_eq_dec wl [value_instruction_write instruction] then
    if @List.list_eq_dec AccessFunction affine_access_eq_dec rl (value_instruction_reads instruction) then true else false
  else false.
Lemma access_function_checker_correct wl rl instruction :
  access_function_checker wl rl instruction = true -> valid_access_function wl rl instruction.
Proof.
  unfold access_function_checker; destruct (@List.list_eq_dec AccessFunction affine_access_eq_dec wl [value_instruction_write instruction]) as [WRITE|]; try discriminate.
  destruct (@List.list_eq_dec AccessFunction affine_access_eq_dec rl (value_instruction_reads instruction)) as [READ|]; try discriminate.
  subst wl rl; intros _ parameters before after writes reads [WRITES [READS RUN]]; subst writes reads; split.
  - intros cell MEMBER; cbn in MEMBER; destruct MEMBER as [<-|BAD]; [|contradiction].
    exists (value_instruction_write instruction); split; [cbn; auto|split; [reflexivity|apply veq_refl]].
  - intros cell MEMBER; apply in_map_iff in MEMBER as [access [<- MEMBER]].
    exists access; split; [exact MEMBER|split; [reflexivity|apply veq_refl]].
Qed.
Lemma sema_prsv_nonalias instruction parameters writes reads before after :
  NonAlias before -> instr_semantics instruction parameters writes reads before after -> NonAlias after.
Proof.
  intros NONALIAS [_ [_ [write [read [_ [_ [REG RUN]]]]]]].
  unfold NonAlias, State.non_alias in *; rewrite REG; exact NONALIAS.
Qed.
Lemma bc_condition_implie_permutbility :
  forall first p1 writes1 reads1 before middle after second p2 writes2 reads2,
    NonAlias before ->
    (instr_semantics first p1 writes1 reads1 before middle /\ instr_semantics second p2 writes2 reads2 middle after) ->
    Forall (fun write2 => Forall (fun write1 => cell_neq write1 write2) writes1) writes2 /\
    Forall (fun read2 => Forall (fun write1 => cell_neq write1 read2) writes1) reads2 /\
    Forall (fun write2 => Forall (fun read1 => cell_neq read1 write2) reads1) writes2 ->
    exists swapped final, instr_semantics second p2 writes2 reads2 before swapped /\
      instr_semantics first p1 writes1 reads1 swapped final /\ State.eq after final.
Proof.
  intros first p1 writes1 reads1 before middle after second p2 writes2 reads2 NONALIAS
    [[WRITE1 [READ1 RUN1]] [WRITE2 [READ2 RUN2]]] [WW [WR RW]].
  subst writes1 writes2 reads1 reads2.
  assert (INDEPENDENT : cells_independent (exact_cell (value_instruction_write first) p1)
    (map (fun access => exact_cell access p1) (value_instruction_reads first))
    (exact_cell (value_instruction_write second) p2)
    (map (fun access => exact_cell access p2) (value_instruction_reads second))).
  { split; [exact (Forall_inv (Forall_inv WW))|]; split.
    - eapply Forall_impl; [|exact WR]; intros cell SINGLE; exact (Forall_inv SINGLE).
    - eapply Forall_impl; [|exact (Forall_inv RW)]; intros cell DIFFERENT.
      apply cell_neq_symm; exact DIFFERENT. }
  destruct (independent_footprints_reorder NONALIAS INDEPENDENT RUN1 RUN2) as [swapped [SECOND FIRST]].
  exists swapped,after; repeat split; try assumption; reflexivity.
Qed.
End MakeMemoryValueInstr.
