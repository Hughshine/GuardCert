From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightSyntaxEquality ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceLoop GuardMemoryAffineSourceReifier
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck GuardMemoryNaryCompute
  GuardMemoryFlatArrayBackend GuardMemoryPointerNaryAccess GuardMemoryPointerCompute GuardMemorySourceValueInterface.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition propose_memory_pointer_access extent layout source :=
  match source with
  | Ederef (Ebinop Oadd (Etempvar pointer _) index _) _ =>
      match propose_memory_source_affine index with
      | Some expression => match memory_encode_nary_index layout expression with
          | Some term => Some (MemoryNaryAccess pointer (RectangleShape extent 1 0 0) expression term)
          | None => None end
      | None => None end
  | _ => None end.
Fixpoint propose_memory_pointer_source_value extent layout (next : nat) source : option (list memory_nary_access * value_expression) :=
  match source with
  | Etempvar identifier _ => option_map (fun position => ([],ParameterValue position)) (memory_source_position identifier layout)
  | Econst_int value _ => Some ([],ConstantValue (Int.signed value))
  | Eunop Oneg (Econst_int value _) _ => Some ([],ConstantValue (-Int.signed value))
  | Ederef _ _ => option_map (fun access => ([access],LoadedValue next)) (propose_memory_pointer_access extent layout source)
  | Ebinop operation first second _ => match operation with
      | Oadd | Osub | Omul => match propose_memory_pointer_source_value extent layout next first with
          | Some (reads,lhs) => match propose_memory_pointer_source_value extent layout (next+length reads)%nat second with
              | Some (other,rhs) => Some (reads++other,
                  match operation with Oadd => AddValue lhs rhs | Osub => SubValue lhs rhs | _ => MulValue lhs rhs end)
              | None => None end
          | None => None end
      | _ => None end
  | _ => None end.
Definition propose_memory_pointer_compute extent layout source :=
  match source with
  | Sassign lhs rhs => match propose_memory_pointer_access extent layout lhs,propose_memory_pointer_source_value extent layout 0 rhs with
      | Some write,Some (reads,value) => Some (MemoryNaryCompute write reads value rhs)
      | _,_ => None end
  | _ => None end.
Fixpoint propose_memory_pointer_computes extent layout sources := match sources with
  | [] => Some []
  | source::sources => match propose_memory_pointer_compute extent layout source,propose_memory_pointer_computes extent layout sources with
      | Some operation,Some operations => Some (operation::operations) | _,_ => None end end.
Definition memory_pointer_access_check limits layout pointer extent access :=
  memory_nary_access_check limits layout access && Pos.eqb (memory_nary_access_array access) pointer &&
    Z.eqb (rectangle_extent (memory_nary_access_shape access)) extent.
Lemma memory_pointer_access_check_sound limits layout pointer extent access :
  memory_pointer_access_check limits layout pointer extent access = true -> memory_pointer_access_valid limits layout pointer extent access.
Proof.
  unfold memory_pointer_access_check; rewrite !andb_true_iff,Pos.eqb_eq,Z.eqb_eq; intros [[VALID ID] EXTENT].
  split; [apply memory_nary_access_check_sound; exact VALID|split; assumption].
Qed.
Definition memory_pointer_compute_check limits layout pointer extent operation :=
  memory_pointer_access_check limits layout pointer extent (memory_nary_compute_write operation) &&
  forallb (memory_pointer_access_check limits layout pointer extent) (memory_nary_compute_reads operation) &&
  match compile_flat_value (memory_pointer_register_codes layout) (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation) with
  | Some code => if expression_eq code (memory_nary_compute_source operation)
      then memory_source_reads_check (map memory_pointer_nary_code (memory_nary_compute_reads operation)) (memory_nary_compute_value operation)
      else false
  | None => false end.
Lemma memory_pointer_compute_check_sound limits layout pointer extent operation :
  memory_pointer_compute_check limits layout pointer extent operation = true -> memory_pointer_compute_valid limits layout pointer extent operation.
Proof.
  unfold memory_pointer_compute_check; rewrite !andb_true_iff; intros [[WRITE READS] VALUE].
  destruct (compile_flat_value (memory_pointer_register_codes layout) (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation)) as [code|] eqn:COMPILE; [|discriminate].
  destruct (expression_eq code (memory_nary_compute_source operation)) as [SAME|]; [|discriminate].
  split; [apply memory_pointer_access_check_sound; exact WRITE|]; split.
  - apply Forall_forall; intros access MEMBER; apply memory_pointer_access_check_sound.
    apply forallb_forall with (x := access) in READS; assumption.
  - split; [rewrite SAME in COMPILE; exact COMPILE|exact VALUE].
Qed.
Print Assumptions memory_pointer_compute_check_sound.
