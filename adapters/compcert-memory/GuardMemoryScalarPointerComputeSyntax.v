From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightSyntaxEquality ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceLoop GuardMemoryAffineSourceReifier
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck GuardMemoryNaryCompute
  GuardMemoryFlatArrayBackend GuardMemoryPointerNaryAccess GuardMemoryPointerCompute GuardMemorySourceValueInterface.
From GuardMemory Require Import GuardMemoryPointerComputeSyntax GuardMemoryScalarPointerCompute GuardMemorySourceParameters.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint propose_memory_scalar_pointer_source_value extent layout scalars (next : nat) source : option (list memory_nary_access * value_expression) :=
  match source with
  | Etempvar identifier _ => option_map (fun position => ([],ParameterValue position)) (memory_source_position identifier (layout++scalars))
  | Econst_int value _ => Some ([],ConstantValue (Int.signed value))
  | Eunop Oneg (Econst_int value _) _ => Some ([],ConstantValue (-Int.signed value))
  | Ederef _ _ => option_map (fun access => ([access],LoadedValue next)) (propose_memory_pointer_access extent layout source)
  | Ebinop operation first second _ => match operation with
      | Oadd | Osub | Omul => match propose_memory_scalar_pointer_source_value extent layout scalars next first with
          | Some (reads,lhs) => match propose_memory_scalar_pointer_source_value extent layout scalars (next+length reads)%nat second with
              | Some (other,rhs) => Some (reads++other,
                  match operation with Oadd => AddValue lhs rhs | Osub => SubValue lhs rhs | _ => MulValue lhs rhs end)
              | None => None end
          | None => None end
      | _ => None end
  | _ => None end.
Definition propose_memory_scalar_pointer_compute extent layout scalars source :=
  match source with
  | Sassign lhs rhs => match propose_memory_pointer_access extent layout lhs,propose_memory_scalar_pointer_source_value extent layout scalars 0 rhs with
      | Some write,Some (reads,value) => Some (MemoryNaryCompute write reads value rhs)
      | _,_ => None end
  | _ => None end.
Fixpoint propose_memory_scalar_pointer_computes extent layout scalars sources := match sources with
  | [] => Some []
  | source::sources => match propose_memory_scalar_pointer_compute extent layout scalars source,propose_memory_scalar_pointer_computes extent layout scalars sources with
      | Some operation,Some operations => Some (operation::operations) | _,_ => None end end.
Definition memory_scalar_pointer_compute_check limits layout scalars pointer extent operation :=
  memory_pointer_access_check limits layout pointer extent (memory_nary_compute_write operation) &&
  forallb (memory_pointer_access_check limits layout pointer extent) (memory_nary_compute_reads operation) &&
  match compile_flat_value (memory_pointer_register_codes (layout++scalars)) (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation) with
  | Some code => if expression_eq code (memory_nary_compute_source operation)
      then memory_source_reads_check (map memory_pointer_nary_code (memory_nary_compute_reads operation)) (memory_nary_compute_value operation)
      else false
  | None => false end.
Lemma memory_scalar_pointer_compute_check_sound limits layout scalars pointer extent operation :
  memory_scalar_pointer_compute_check limits layout scalars pointer extent operation = true -> memory_scalar_pointer_compute_valid limits layout scalars pointer extent operation.
Proof.
  unfold memory_scalar_pointer_compute_check; rewrite !andb_true_iff; intros [[WRITE READS] VALUE].
  destruct (compile_flat_value (memory_pointer_register_codes (layout++scalars)) (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation)) as [code|] eqn:COMPILE; [|discriminate].
  destruct (expression_eq code (memory_nary_compute_source operation)) as [SAME|]; [|discriminate].
  split; [apply memory_pointer_access_check_sound; exact WRITE|]; split.
  - apply Forall_forall; intros access MEMBER; apply memory_pointer_access_check_sound.
    apply forallb_forall with (x := access) in READS; assumption.
  - split; [rewrite SAME in COMPILE; exact COMPILE|exact VALUE].
Qed.
Fixpoint memory_pointer_value_registers source := match source with
  | Etempvar identifier _ => [identifier]
  | Ebinop _ first second _ => memory_pointer_value_registers first++memory_pointer_value_registers second
  | _ => [] end.
Definition memory_pointer_statement_registers source := match source with
  | Sassign _ value => memory_pointer_value_registers value | _ => [] end.
Definition propose_memory_pointer_scalars layout sources :=
  nodup peq (filter (fun identifier => negb (existsb (Pos.eqb identifier) layout))
    (flat_map memory_pointer_statement_registers sources)).
Definition memory_scalar_pointer_registers_check layout scalars operations :=
  forallb (fun identifier => match memory_source_position identifier (layout++scalars) with
    | Some position => existsb (fun operation => existsb (Nat.eqb position)
        (memory_source_parameter_positions (memory_nary_compute_value operation))) operations
    | None => false end) scalars.
Lemma memory_source_position_lookup identifier layout position : memory_source_position identifier layout = Some position ->
  nth_error layout position = Some identifier.
Proof.
  revert position; induction layout as [|first rest IH]; intros position LOOKUP; cbn in LOOKUP; [discriminate|].
  destruct (peq identifier first) as [->|OTHER].
  - inversion LOOKUP; reflexivity.
  - destruct (memory_source_position identifier rest) as [index|] eqn:INDEX; cbn in LOOKUP; [|discriminate].
    inversion LOOKUP; subst position; cbn; apply IH; reflexivity.
Qed.
Theorem memory_scalar_pointer_registers_check_sound layout scalars operations :
  memory_scalar_pointer_registers_check layout scalars operations = true ->
  forall identifier, In identifier scalars -> exists operation index,
    In operation operations /\ nth_error (layout++scalars) index = Some identifier /\
    In index (memory_source_parameter_positions (memory_nary_compute_value operation)).
Proof.
  unfold memory_scalar_pointer_registers_check; intros CHECK identifier MEMBER.
  apply forallb_forall with (x := identifier) in CHECK; [|exact MEMBER].
  destruct (memory_source_position identifier (layout++scalars)) as [index|] eqn:POSITION; [|discriminate].
  apply existsb_exists in CHECK as [operation [IN USED]].
  apply existsb_exists in USED as [same [USED SAME]]; apply Nat.eqb_eq in SAME; subst same.
  exists operation,index; split; [exact IN|]; split; [apply memory_source_position_lookup; exact POSITION|exact USED].
Qed.
Print Assumptions memory_scalar_pointer_compute_check_sound.
Print Assumptions memory_scalar_pointer_registers_check_sound.
