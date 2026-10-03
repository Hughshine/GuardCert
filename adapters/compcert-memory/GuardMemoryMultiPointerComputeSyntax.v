From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Coqlib Integers.
From compcert.cfrontend Require Import Clight Ctypes Cop.
From Guard Require Import ClightSyntaxEquality ClightRectangularStore.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryAffineSourceLoop GuardMemoryAffineSourceReifier
  GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryNaryAccessCheck GuardMemoryNaryCompute
  GuardMemoryFlatArrayBackend GuardMemoryPointerNaryAccess GuardMemoryPointerCompute GuardMemorySourceValueInterface.
From GuardMemory Require Import GuardMemoryPointerComputeSyntax GuardMemoryScalarPointerComputeSyntax GuardMemorySourceParameters GuardMemoryMultiPointerAccess GuardMemoryMultiPointerCompute.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_multi_pointer_access_check limits layout extent access :=
  memory_nary_access_check limits layout access && Z.eqb (rectangle_extent (memory_nary_access_shape access)) extent.
Lemma memory_multi_pointer_access_check_sound limits layout extent access :
  memory_multi_pointer_access_check limits layout extent access = true -> memory_multi_pointer_access_valid limits layout extent access.
Proof. unfold memory_multi_pointer_access_check; rewrite andb_true_iff,Z.eqb_eq; intros [ACCESS EXTENT];
  split; [apply memory_nary_access_check_sound; exact ACCESS|exact EXTENT]. Qed.

Definition memory_multi_pointer_compute_check limits layout scalars extent operation :=
  memory_multi_pointer_access_check limits layout extent (memory_nary_compute_write operation) &&
  forallb (memory_multi_pointer_access_check limits layout extent) (memory_nary_compute_reads operation) &&
  match compile_flat_value (memory_pointer_register_codes (layout++scalars)) (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation) with
  | Some code => if expression_eq code (memory_nary_compute_source operation)
      then memory_source_reads_check (map memory_pointer_nary_code (memory_nary_compute_reads operation)) (memory_nary_compute_value operation)
      else false
  | None => false end.
Lemma memory_multi_pointer_compute_check_sound limits layout scalars extent operation :
  memory_multi_pointer_compute_check limits layout scalars extent operation = true -> memory_multi_pointer_compute_valid limits layout scalars extent operation.
Proof.
  unfold memory_multi_pointer_compute_check; rewrite !andb_true_iff; intros [[WRITE READS] VALUE].
  destruct (compile_flat_value (memory_pointer_register_codes (layout++scalars)) (map memory_pointer_nary_code (memory_nary_compute_reads operation))
    (memory_nary_compute_value operation)) as [code|] eqn:COMPILE; [|discriminate].
  destruct (expression_eq code (memory_nary_compute_source operation)) as [SAME|]; [|discriminate].
  split; [apply memory_multi_pointer_access_check_sound; exact WRITE|]; split.
  - apply Forall_forall; intros access MEMBER; apply memory_multi_pointer_access_check_sound.
    apply forallb_forall with (x := access) in READS; assumption.
  - split; [rewrite SAME in COMPILE; exact COMPILE|exact VALUE].
Qed.

Print Assumptions memory_multi_pointer_compute_check_sound.
