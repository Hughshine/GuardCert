From Stdlib Require Import ZArith Bool Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Values Memory.
From Guard Require Import Presumption Synthesis.
Open Scope Z_scope.
Module P := Presumption.
Module G := Synthesis.

(** Byte ranges, not pointer inequality: two pointers in the same allocation
    may still denote disjoint accesses, while unequal overlapping pointers do
    not justify hoisting a load.  Offsets here are actual Mem.load/store Zs. *)
Definition byte_disjoint (read_chunk : memory_chunk) (rb : Values.block) (ro : Z)
  (write_chunk : memory_chunk) (wb : Values.block) (wo : Z) : Prop :=
  rb <> wb \/ ro + size_chunk read_chunk <= wo \/ wo + size_chunk write_chunk <= ro.

Definition access_view (rb : Values.block) (ro : Z) (wb : Values.block) (wo : Z) (_ : unit) : P.state :=
  P.State (fun _ => 0)
    (fun i => if Nat.eqb i 0 then P.Pointer (Pos.to_nat rb) ro
              else P.Pointer (Pos.to_nat wb) wo) (fun _ => 0).
Definition access_presumption (r w : memory_chunk) :=
  P.Atomic (P.Disjoint 0 (P.Literal (size_chunk r)) 1 (P.Literal (size_chunk w))).

Lemma access_encoding : forall r rb ro w wb wo,
  @G.presumption_encoding unit Ptrofs.modulus (access_view rb ro wb wo)
    (fun _ => byte_disjoint r rb ro w wb wo).
Proof.
  intros r rb ro w wb wo. refine {| G.encoded_presumption := access_presumption r w |}.
  intro s. change
    ((0 <=? size_chunk r) && (0 <=? size_chunk w) &&
      ((size_chunk r =? 0) || (size_chunk w =? 0) ||
       negb (Nat.eqb (Pos.to_nat rb) (Pos.to_nat wb)) ||
       (ro + size_chunk r <=? wo) || (wo + size_chunk w <=? ro)) = true <->
      byte_disjoint r rb ro w wb wo).
  unfold byte_disjoint.
  pose proof (size_chunk_pos r) as R; pose proof (size_chunk_pos w) as W.
  assert (LR : (0 <=? size_chunk r) = true) by (apply Z.leb_le; lia).
  assert (LW : (0 <=? size_chunk w) = true) by (apply Z.leb_le; lia).
  assert (ZR : (size_chunk r =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (ZW : (size_chunk w =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite LR, LW, ZR, ZW. cbn [andb orb].
  repeat rewrite orb_true_iff. rewrite negb_true_iff, Nat.eqb_neq, ! Z.leb_le.
  assert (BLOCKS : Pos.to_nat rb <> Pos.to_nat wb <-> rb <> wb).
  { split; intros NE EQ; apply NE; [subst; reflexivity|apply Pos2Nat.inj; exact EQ]. }
  rewrite BLOCKS. tauto.
Defined.

Theorem synthesized_disjoint_load_stability : forall r rb ro w wb wo m v m',
  Mem.store w m wb wo v = Some m' ->
  G.execute Ptrofs.modulus (access_view rb ro wb wo tt)
    (G.synthesize (access_presumption r w)) = Some true ->
  Mem.load r m' rb ro = Mem.load r m rb ro.
Proof.
  intros r rb ro w wb wo m v m' STORE CHECK.
  assert (SEP : byte_disjoint r rb ro w wb wo).
  { apply (proj1 (@G.encoded_condition_correct unit Ptrofs.modulus
      (access_view rb ro wb wo) (fun _ => byte_disjoint r rb ro w wb wo)
      (access_encoding r rb ro w wb wo) tt true CHECK)); reflexivity. }
  eapply Mem.load_store_other; eauto.
Qed.

(** A memory plugin can supply this endpoint theorem for a hoisted load.
    STORE is the access/permission obligation; the disjoint guard does not
    imply it.  This file has no Clight reinsertion or whole-program theorem. *)
Theorem checked_load_hoisting_endpoint : forall r rb ro w wb wo m v m' loaded,
  Mem.store w m wb wo v = Some m' -> Mem.load r m' rb ro = Some loaded ->
  G.execute Ptrofs.modulus (access_view rb ro wb wo tt)
    (G.synthesize (access_presumption r w)) = Some true ->
  Mem.load r m rb ro = Some loaded /\ Mem.store w m wb wo v = Some m'.
Proof.
  intros. split; auto.
  rewrite <- (synthesized_disjoint_load_stability r rb ro w wb wo m v m' H H1); exact H0.
Qed.

Example unequal_pointers_can_overlap :
  G.execute Ptrofs.modulus (access_view 1%positive 0 1%positive 1 tt)
    (G.synthesize (access_presumption Mint32 Mint32)) = Some false.
Proof. reflexivity. Qed.
Example adjacent_accesses_do_not_overlap :
  G.execute Ptrofs.modulus (access_view 1%positive 0 1%positive 4 tt)
    (G.synthesize (access_presumption Mint32 Mint32)) = Some true.
Proof. reflexivity. Qed.
Example overflowing_endpoint_is_not_accepted :
  G.execute Ptrofs.modulus (access_view 1%positive (Ptrofs.modulus - 2) 2%positive 0 tt)
    (G.synthesize (access_presumption Mint32 Mint32)) = None.
Proof. reflexivity. Qed.

Print Assumptions checked_load_hoisting_endpoint.
