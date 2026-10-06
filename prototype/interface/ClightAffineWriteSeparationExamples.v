From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightCondition ClightCountedLoop ClightPureExpr ClightSameAddress.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryAffineAddressSpecialization
  GuardMemoryAffineRowSeparation.
From GuardInterface Require Import ClightWordAddressSeparation ClightReadonlyExpressionScan.
Import ListNotations.
Local Open Scope Z_scope.

(** Actual Clight tests, with symbolic CompCert memory and permissions. These
    are proof fixtures, not frontend or native compiler evidence. Public row
    and column words need not be initialized to evaluate the substituted code. *)
Definition was_row := 1%positive.
Definition was_column := 2%positive.
Definition was_write := 3%positive.
Definition was_bound := 4%positive.
Definition was_index := MemorySourceAdd (MemorySourceConstant 32)
  (MemorySourceAdd (MemorySourceScaleLeft 64 (MemorySourceTemp was_row)) (MemorySourceTemp was_column)).
Definition was_address := memory_affine_address_at was_row was_column 1 1 was_write was_index.
Definition was_probe := word_address_separation was_address was_bound.

Lemma specialized_write_address ge locals temps memory block base :
  temps ! was_write = Some (Vptr block base) ->
  eval_expr ge locals temps memory was_address (Vptr block (Ptrofs.add base (Ptrofs.repr 388))).
Proof.
  intro POINTER.
  change (eval_expr ge locals temps memory was_address
    (Vptr block (Ptrofs.add base (Ptrofs.repr
      (4*memory_source_affine_math (memory_affine_at_value was_row was_column 1 1 (fun _ => 0)) was_index))))).
  eapply memory_affine_address_at_evaluation; [exact POINTER| |].
  - intros identifier MEMBER ROW COLUMN; cbn [was_index memory_source_affine_reads] in MEMBER.
    cbn in MEMBER; destruct MEMBER as [<-|[<-|[]]]; contradiction.
  - change (-2147483648 <= 97 <= 2147483647); lia.
Qed.

Theorem specialized_alias_refuses ge locals temps memory block base loaded :
  temps ! was_write = Some (Vptr block base) ->
  temps ! was_bound = Some (Vptr block (Ptrofs.add base (Ptrofs.repr 388))) ->
  Mem.valid_access memory Mint32 block (Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr 388))) Writable ->
  Mem.loadv Mint32 memory (Vptr block (Ptrofs.add base (Ptrofs.repr 388))) = Some loaded ->
  decision_run (Entry ge locals temps memory) was_probe false.
Proof.
  intros POINTER BOUND ACCESS READ; unfold was_probe,word_address_separation.
  eapply run_test with (b:=true); [|constructor].
  replace true with (address_flag block (Ptrofs.add base (Ptrofs.repr 388))
    block (Ptrofs.add base (Ptrofs.repr 388))) by
    (unfold address_flag; rewrite Pos.eqb_refl,Ptrofs.eq_true; reflexivity).
  eapply word_address_equality_test; [reflexivity|apply specialized_write_address; exact POINTER|
    exact BOUND|exact ACCESS|exact READ].
Qed.

Theorem specialized_separate_blocks_accept ge locals temps memory block base bound offset loaded :
  block <> bound -> temps ! was_write = Some (Vptr block base) ->
  temps ! was_bound = Some (Vptr bound offset) ->
  Mem.valid_access memory Mint32 block (Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr 388))) Writable ->
  Mem.loadv Mint32 memory (Vptr bound offset) = Some loaded ->
  decision_run (Entry ge locals temps memory) was_probe true.
Proof.
  intros DIFFERENT POINTER BOUND ACCESS READ; unfold was_probe,word_address_separation.
  eapply run_test with (b:=false); [|constructor].
  replace false with (address_flag block (Ptrofs.add base (Ptrofs.repr 388)) bound offset) by
    (unfold address_flag; rewrite (proj2 (Pos.eqb_neq _ _) DIFFERENT); reflexivity).
  eapply word_address_equality_test; [reflexivity|apply specialized_write_address; exact POINTER|
    exact BOUND|exact ACCESS|exact READ].
Qed.

(** No remaining test is evaluated after a refused first address. In
    particular, the tail can mention uninitialized pointers or later rows. *)
Theorem specialized_alias_stops_tail ge locals temps memory block base loaded tail :
  temps ! was_write = Some (Vptr block base) ->
  temps ! was_bound = Some (Vptr block (Ptrofs.add base (Ptrofs.repr 388))) ->
  Mem.valid_access memory Mint32 block (Ptrofs.unsigned (Ptrofs.add base (Ptrofs.repr 388))) Writable ->
  Mem.loadv Mint32 memory (Vptr block (Ptrofs.add base (Ptrofs.repr 388))) = Some loaded ->
  decision_run (Entry ge locals temps memory) (decision_bind was_probe tail (Decision false)) false.
Proof.
  intros POINTER BOUND ACCESS READ; eapply decision_bind_run;
    [eapply specialized_alias_refuses; eassumption|constructor].
Qed.

Print Assumptions specialized_write_address.
Print Assumptions specialized_alias_refuses.
Print Assumptions specialized_separate_blocks_accept.
Print Assumptions specialized_alias_stops_tail.
