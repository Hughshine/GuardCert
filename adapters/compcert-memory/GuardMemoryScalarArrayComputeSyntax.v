From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightSyntaxEquality ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceLoop GuardMemoryAffineSourceReifier
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck GuardMemoryNaryCompute
  GuardMemoryFlatArrayBackend GuardMemoryPointerNaryAccess GuardMemoryPointerCompute GuardMemorySourceValueInterface.
From GuardMemory Require Import GuardMemoryPointerComputeSyntax GuardMemoryScalarArrayCompute GuardMemorySourceParameters GuardMemoryNaryComputeSyntax.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Fixpoint propose_memory_scalar_array_source_value layout scalars (next : nat) source : option (list memory_nary_access * value_expression) :=
  match source with
  | Etempvar identifier _ => option_map (fun position => ([],ParameterValue position)) (memory_source_position identifier (layout++scalars))
  | Econst_int value _ => Some ([],ConstantValue (Int.signed value))
  | Eunop Oneg (Econst_int value _) _ => Some ([],ConstantValue (-Int.signed value))
  | Ederef _ _ => option_map (fun access => ([access],LoadedValue next)) (propose_memory_nary_access layout source)
  | Ebinop operation first second _ => match operation with
      | Oadd | Osub | Omul => match propose_memory_scalar_array_source_value layout scalars next first with
          | Some (reads,lhs) => match propose_memory_scalar_array_source_value layout scalars (next+length reads)%nat second with
              | Some (other,rhs) => Some (reads++other,
                  match operation with Oadd => AddValue lhs rhs | Osub => SubValue lhs rhs | _ => MulValue lhs rhs end)
              | None => None end
          | None => None end
      | _ => None end
  | _ => None end.
Definition propose_memory_scalar_array_compute layout scalars source :=
  match source with
  | Sassign lhs rhs => match propose_memory_nary_access layout lhs,propose_memory_scalar_array_source_value layout scalars 0 rhs with
      | Some write,Some (reads,value) => Some (MemoryNaryCompute write reads value rhs)
      | _,_ => None end
  | _ => None end.
Fixpoint propose_memory_scalar_array_computes layout scalars sources := match sources with
  | [] => Some []
  | source::sources => match propose_memory_scalar_array_compute layout scalars source,propose_memory_scalar_array_computes layout scalars sources with
      | Some operation,Some operations => Some (operation::operations) | _,_ => None end end.
Definition memory_scalar_array_compute_check limits layout scalars operation :=
  memory_nary_access_check limits layout (memory_nary_compute_write operation) &&
  forallb (memory_nary_access_check limits layout) (memory_nary_compute_reads operation) &&
  match compile_flat_value (memory_pointer_register_codes (layout++scalars)) (map memory_nary_access_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation) with
  | Some code => if expression_eq code (memory_nary_compute_source operation)
      then memory_source_reads_check (map memory_nary_access_code (memory_nary_compute_reads operation)) (memory_nary_compute_value operation)
      else false
  | None => false end.
Lemma memory_scalar_array_compute_check_sound limits layout scalars operation :
  memory_scalar_array_compute_check limits layout scalars operation = true -> memory_scalar_array_compute_valid limits layout scalars operation.
Proof.
  unfold memory_scalar_array_compute_check; rewrite !andb_true_iff; intros [[WRITE READS] VALUE].
  destruct (compile_flat_value (memory_pointer_register_codes (layout++scalars)) (map memory_nary_access_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation)) as [code|] eqn:COMPILE; [|discriminate].
  destruct (expression_eq code (memory_nary_compute_source operation)) as [SAME|]; [|discriminate].
  split; [apply memory_nary_access_check_sound; exact WRITE|]; split.
  - apply Forall_forall; intros access MEMBER; apply memory_nary_access_check_sound.
    apply forallb_forall with (x := access) in READS; assumption.
  - split; [rewrite SAME in COMPILE; exact COMPILE|exact VALUE].
Qed.
Print Assumptions memory_scalar_array_compute_check_sound.
