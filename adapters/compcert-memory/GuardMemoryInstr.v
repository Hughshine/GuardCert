From Stdlib Require Import List Bool ZArith Numbers.DecimalString.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory.
From polcert.src Require Import PolyBase OpenScop.
From polcert.polygen Require Import StateTy TyTy InstrTy IterSemantics.
From polcert.lib Require Import ImpureAlarmConfig Linalg.
From GuardMemory Require Import GuardMemoryRuntime.
Import ListNotations.
Set Implicit Arguments.

Definition affine_term_eq_dec : forall first second : list Z * Z, {first = second} + {first <> second}.
Proof.
  intros [coefficients bias] [other_coefficients other_bias].
  destruct (@List.list_eq_dec Z Z.eq_dec coefficients other_coefficients) as [EQ|NE]; [subst|right; congruence].
  destruct (Z.eq_dec bias other_bias) as [EQ|NE]; [subst; left; reflexivity|right; congruence].
Defined.
Definition affine_access_eq_dec : forall first second : AccessFunction, {first = second} + {first <> second}.
Proof.
  intros [array coordinates] [other_array other_coordinates].
  destruct (Pos.eq_dec array other_array) as [EQ|NE]; [subst|right; congruence].
  destruct (@List.list_eq_dec (list Z * Z)%type affine_term_eq_dec coordinates other_coordinates) as [EQ|NE]; [subst; left; reflexivity|right; congruence].
Defined.
Definition value_expression_eq_dec : forall first second : value_expression, {first = second} + {first <> second}.
Proof. decide equality; try apply Nat.eq_dec; apply Z.eq_dec. Defined.
Record memory_instruction := MemoryInstruction {
  instruction_write : AccessFunction;
  instruction_reads : list AccessFunction;
  instruction_value : value_expression
}.
Definition memory_instruction_eq_dec : forall first second : memory_instruction, {first = second} + {first <> second}.
Proof.
  intros [write reads expression] [other_write other_reads other_expression].
  destruct (affine_access_eq_dec write other_write) as [EQ|NE]; [subst|right; congruence].
  destruct (@List.list_eq_dec AccessFunction affine_access_eq_dec reads other_reads) as [EQ|NE]; [subst|right; congruence].
  destruct (value_expression_eq_dec expression other_expression) as [EQ|NE]; [subst; left; reflexivity|right; congruence].
Defined.

(** This implements the actual PolCert instruction contract with CompCert Mem.
    Every exported property below is proved; no CState.valid premise is used. *)
Module GuardMemoryInstr <: INSTR.
Module State <: STATE.
  Definition t := runtime_state.
  Definition non_alias s := locations_nonalias (runtime_locations s).
  Definition eq : t -> t -> Prop := @Logic.eq t.
  Lemma eq_refl s : eq s s. Proof. reflexivity. Qed.
  Lemma eq_sym first second : eq first second -> eq second first. Proof. intro SAME; symmetry; exact SAME. Qed.
  Lemma eq_trans first middle final : eq first middle -> eq middle final -> eq first final.
  Proof. intros FIRST SECOND; unfold eq in *; congruence. Qed.
  Definition dummy_state := RuntimeState (fun _ => None) Mem.empty.
End State.
Module Ty <: TY.
  Definition t := unit.
  Definition dummy := tt.
  Definition eqb (_ _ : t) := true.
  Lemma eqb_eq first second : eqb first second = true <-> first = second.
  Proof. destruct first,second; split; reflexivity. Qed.
End Ty.
Module IterSem := IterSem State.
Module IterSemImpure := IterSem.IterImpureSemantics CoreAlarmed.
Definition t := memory_instruction.
Definition dummy_instr := MemoryInstruction (1%positive,[]) [] (ConstantValue 0).
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
  writes = [exact_cell (instruction_write instruction) parameters] /\
  reads = map (fun access => exact_cell access parameters) (instruction_reads instruction) /\
  footprint_run (exact_cell (instruction_write instruction) parameters) reads
    (fun values => evaluate_value parameters values (instruction_value instruction)) before after.
Lemma instr_semantics_stable_under_state_eq instruction parameters writes reads before after before' after' :
  State.eq before before' -> State.eq after after' ->
  instr_semantics instruction parameters writes reads before after ->
  instr_semantics instruction parameters writes reads before' after'.
Proof. unfold State.eq; intros BEFORE AFTER RUN; subst before' after'; exact RUN. Qed.
Definition eqb first second := if memory_instruction_eq_dec first second then true else false.
Lemma eqb_eq first second : eqb first second = true <-> first = second.
Proof. unfold eqb; destruct (memory_instruction_eq_dec first second); intuition congruence. Qed.
Definition NonAlias := State.non_alias.
Definition InitEnv (names : list ident) (values : list Z) (_ : State.t) := length names = length values.
Definition Compat (_ : list (ident * Ty.t)) (_ : State.t) := True.
Lemma init_env_samelen names values state : InitEnv names values state -> length names = length values.
Proof. exact (fun SAME => SAME). Qed.
(** OpenScop export is optional in INSTR. This first instance is fed a checked
    PolyLang proposal directly; it does not export an external scheduler input. *)
Definition to_openscop (_ : t) (_ : list varname) : option OpenScop.ArrayStmt := None.
Definition waccess instruction := Some [instruction_write instruction].
Definition raccess instruction := Some (instruction_reads instruction).
Definition valid_access_function wl rl instruction := forall parameters before after writes reads,
  instr_semantics instruction parameters writes reads before after ->
  valid_access_cells parameters writes wl /\ valid_access_cells parameters reads rl.
Definition check_never_written names instruction :=
  negb (existsb (Pos.eqb (fst (instruction_write instruction))) names).
Definition access_function_checker wl rl instruction :=
  if @List.list_eq_dec AccessFunction affine_access_eq_dec wl [instruction_write instruction] then
    if @List.list_eq_dec AccessFunction affine_access_eq_dec rl (instruction_reads instruction) then true else false
  else false.
Lemma access_function_checker_correct wl rl instruction :
  access_function_checker wl rl instruction = true -> valid_access_function wl rl instruction.
Proof.
  unfold access_function_checker; destruct (@List.list_eq_dec AccessFunction affine_access_eq_dec wl [instruction_write instruction]) as [WRITE|]; try discriminate.
  destruct (@List.list_eq_dec AccessFunction affine_access_eq_dec rl (instruction_reads instruction)) as [READ|]; try discriminate.
  subst wl rl; intros _ parameters before after writes reads [WRITES [READS RUN]]; subst writes reads; split.
  - intros cell MEMBER; cbn in MEMBER; destruct MEMBER as [<-|BAD]; [|contradiction].
    exists (instruction_write instruction); split; [cbn; auto|split; [reflexivity|apply veq_refl]].
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
  assert (INDEPENDENT : cells_independent (exact_cell (instruction_write first) p1)
    (map (fun access => exact_cell access p1) (instruction_reads first))
    (exact_cell (instruction_write second) p2)
    (map (fun access => exact_cell access p2) (instruction_reads second))).
  { split; [exact (Forall_inv (Forall_inv WW))|]; split.
    - eapply Forall_impl; [|exact WR]; intros cell SINGLE; exact (Forall_inv SINGLE).
    - eapply Forall_impl; [|exact (Forall_inv RW)]; intros cell DIFFERENT.
      apply cell_neq_symm; exact DIFFERENT. }
  destruct (independent_footprints_reorder NONALIAS INDEPENDENT RUN1 RUN2) as [swapped [SECOND FIRST]].
  exists swapped,after; repeat split; try assumption; reflexivity.
Qed.
End GuardMemoryInstr.
Print Assumptions GuardMemoryInstr.bc_condition_implie_permutbility.
Print Assumptions GuardMemoryInstr.access_function_checker_correct.
