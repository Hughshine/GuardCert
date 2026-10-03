From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Integers Coqlib.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes.
From polcert.src Require Import PolyBase.
From polcert.lib Require Import Linalg.
From Guard Require Import ClightCondition ClightPureExpr CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryRegistryGuard GuardMemoryFootprintRestriction
  GuardMemoryFiniteFootprint GuardMemoryPointerCellComparison.
Import ListNotations.
Set Implicit Arguments.

(** A language instance gives each selected logical cell a pure address
    expression and derives valid aligned addresses from actual source access.
    The finite guard then needs no knowledge of C allocation lengths. *)
Definition memory_cell_address_binding (code : MemCell -> expr) locations s cell :=
  exists location offset, locations cell = Some location /\ location_chunk location = Mint32 /\
    location_offset location = Ptrofs.unsigned offset /\ pure_scalar (code cell) /\
    typeof (code cell) = Tpointer type_int32s noattr /\
    eval_expr (entry_ge s) (entry_env s) (entry_temps s) (entry_memory s)
      (code cell) (Vptr (location_block location) offset) /\
    Mem.valid_pointer (entry_memory s) (location_block location) (Ptrofs.unsigned offset) = true /\
    (4 | Ptrofs.unsigned offset)%Z.
Lemma memory_pointer_eq_unsigned first second :
  Ptrofs.eq first second = Z.eqb (Ptrofs.unsigned first) (Ptrofs.unsigned second).
Proof.
  unfold Ptrofs.eq; destruct (zeq (Ptrofs.unsigned first) (Ptrofs.unsigned second)) as [SAME|DIFFERENT];
    symmetry; [apply Z.eqb_eq; exact SAME|apply Z.eqb_neq; exact DIFFERENT].
Qed.
Definition memory_cell_pair_address_check locations first second :=
  if memory_cell_identity_dec first second then true else
  match locations first,locations second with
  | Some first_location,Some second_location =>
      negb (Pos.eqb (location_block first_location) (location_block second_location) &&
        Z.eqb (location_offset first_location) (location_offset second_location))
  | _,_ => false end.
Definition memory_cell_pair_address_tree code first second :=
  if memory_cell_identity_dec first second then Decision true else
    Test (memory_pointer_cells_test (code first) (code second)) (Decision true) (Decision false).
Theorem memory_cell_pair_address_exact code locations s first second :
  memory_cell_address_binding code locations s first -> memory_cell_address_binding code locations s second ->
  forall flag, decision_run s (memory_cell_pair_address_tree code first second) flag <->
    flag = memory_cell_pair_address_check locations first second.
Proof.
  intros [first_location [first_offset [FIRST_LOCATION [FIRST_CHUNK [FIRST_OFFSET [FIRST_PURE
    [FIRST_TYPE [FIRST_VALUE [FIRST_VALID FIRST_ALIGN]]]]]]]]]
    [second_location [second_offset [SECOND_LOCATION [SECOND_CHUNK [SECOND_OFFSET [SECOND_PURE
    [SECOND_TYPE [SECOND_VALUE [SECOND_VALID SECOND_ALIGN]]]]]]]]] flag.
  unfold memory_cell_pair_address_tree,memory_cell_pair_address_check.
  destruct memory_cell_identity_dec; [split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor]|].
  rewrite FIRST_LOCATION,SECOND_LOCATION,FIRST_OFFSET,SECOND_OFFSET.
  rewrite <- memory_pointer_eq_unsigned.
  change (decision_run s (Test (memory_pointer_cells_test (code first) (code second))
    (Decision true) (Decision false)) flag <->
    flag = memory_pointer_cells_unequal (location_block first_location) first_offset
      (location_block second_location) second_offset).
  rewrite <- andb_true_r with (b := memory_pointer_cells_unequal (location_block first_location) first_offset
    (location_block second_location) second_offset).
  apply memory_decision_test_exact.
  - intro answer; destruct s as [ge locals temps memory]; cbn in *.
    apply memory_pointer_cells_test_exact; assumption.
  - intro answer; split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
Qed.
Lemma memory_cell_pair_address_separated code locations s first second first_location second_location :
  memory_cell_address_binding code locations s first -> memory_cell_address_binding code locations s second ->
  locations first = Some first_location -> locations second = Some second_location ->
  cell_neq first second -> memory_cell_pair_address_check locations first second = true ->
  location_disjoint first_location second_location.
Proof.
  intros [left_location [first_offset [LEFT [FIRST_CHUNK [FIRST_OFFSET [FIRST_PURE
    [FIRST_TYPE [FIRST_VALUE [FIRST_VALID FIRST_ALIGN]]]]]]]]]
    [right_location [second_offset [RIGHT [SECOND_CHUNK [SECOND_OFFSET [SECOND_PURE
    [SECOND_TYPE [SECOND_VALUE [SECOND_VALID SECOND_ALIGN]]]]]]]]]
    FIRST SECOND DIFFERENT CHECK.
  assert (left_location = first_location) by congruence; subst left_location.
  assert (right_location = second_location) by congruence; subst right_location.
  unfold memory_cell_pair_address_check in CHECK; destruct memory_cell_identity_dec as [SAME|DISTINCT].
  - subst second; unfold cell_neq in DIFFERENT; destruct DIFFERENT as [BAD|BAD];
      [congruence|exfalso; apply BAD; apply veq_refl].
  - rewrite FIRST,SECOND,FIRST_OFFSET,SECOND_OFFSET,<-memory_pointer_eq_unsigned in CHECK.
    pose proof (@memory_pointer_cells_unequal_separated (location_block first_location) first_offset
      (location_block second_location) second_offset FIRST_ALIGN SECOND_ALIGN CHECK) as SEPARATED.
    destruct first_location as [first_chunk first_block first_address].
    destruct second_location as [second_chunk second_block second_address]; cbn in *.
    subst first_chunk second_chunk first_address second_address; exact SEPARATED.
Qed.
Fixpoint memory_cell_tail_address_tree code first rest := match rest with
  | [] => Decision true
  | second::rest => decision_bind (memory_cell_pair_address_tree code first second)
      (memory_cell_tail_address_tree code first rest) (Decision false) end.
Fixpoint memory_finite_address_tree code cells := match cells with
  | [] => Decision true
  | first::rest => decision_bind (memory_cell_tail_address_tree code first rest)
      (memory_finite_address_tree code rest) (Decision false) end.
Fixpoint memory_finite_address_check locations cells := match cells with
  | [] => true
  | first::rest => forallb (memory_cell_pair_address_check locations first) rest &&
      memory_finite_address_check locations rest end.
Lemma memory_cell_tail_address_exact code locations s first cells :
  memory_cell_address_binding code locations s first ->
  Forall (memory_cell_address_binding code locations s) cells ->
  forall flag, decision_run s (memory_cell_tail_address_tree code first cells) flag <->
    flag = forallb (memory_cell_pair_address_check locations first) cells.
Proof.
  intros FIRST CELLS; induction CELLS; intro flag; cbn.
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - apply memory_decision_bind_exact; [apply memory_cell_pair_address_exact; assumption|exact IHCELLS].
Qed.
Theorem memory_finite_address_exact code locations s cells :
  Forall (memory_cell_address_binding code locations s) cells ->
  forall flag, decision_run s (memory_finite_address_tree code cells) flag <->
    flag = memory_finite_address_check locations cells.
Proof.
  intro CELLS; induction CELLS; intro flag; cbn.
  - split; [intro RUN; inversion RUN; reflexivity|intro SAME; subst; constructor].
  - apply memory_decision_bind_exact; [apply memory_cell_tail_address_exact; assumption|exact IHCELLS].
Qed.
Theorem memory_finite_address_separation_sound code locations s cells :
  Forall (memory_cell_address_binding code locations s) cells ->
  memory_finite_address_check locations cells = true ->
  memory_locations_separated_on (memory_footprint_allowed cells) locations.
Proof.
  intro BINDINGS; induction BINDINGS as [|head tail HEAD BINDINGS IH];
    intros CHECK first second first_location second_location FIRST_ALLOWED SECOND_ALLOWED FIRST SECOND DIFFERENT.
  all: apply memory_footprint_allowed_exact in FIRST_ALLOWED,SECOND_ALLOWED.
  - contradiction.
  - cbn [memory_finite_address_check] in CHECK; apply andb_true_iff in CHECK as [HEAD_CHECK TAIL_CHECK].
    destruct FIRST_ALLOWED as [FIRST_HEAD|FIRST_TAIL],SECOND_ALLOWED as [SECOND_HEAD|SECOND_TAIL].
    + subst first second; unfold cell_neq in DIFFERENT; destruct DIFFERENT as [BAD|BAD];
        [congruence|exfalso; apply BAD; apply veq_refl].
    + subst first; apply forallb_forall with (x := second) in HEAD_CHECK; [|exact SECOND_TAIL].
      rewrite Forall_forall in BINDINGS; specialize (BINDINGS second SECOND_TAIL).
      exact (@memory_cell_pair_address_separated code locations s head second first_location second_location
        HEAD BINDINGS FIRST SECOND DIFFERENT HEAD_CHECK).
    + subst second; apply forallb_forall with (x := first) in HEAD_CHECK; [|exact FIRST_TAIL].
      rewrite Forall_forall in BINDINGS; specialize (BINDINGS first FIRST_TAIL).
      apply location_disjoint_symmetric.
      exact (@memory_cell_pair_address_separated code locations s head first second_location first_location
        HEAD BINDINGS SECOND FIRST (proj1 (cell_neq_symm first head) DIFFERENT) HEAD_CHECK).
    + apply (IH TAIL_CHECK first second first_location second_location);
        [apply memory_footprint_allowed_exact; exact FIRST_TAIL|
         apply memory_footprint_allowed_exact; exact SECOND_TAIL|exact FIRST|exact SECOND|exact DIFFERENT].

Qed.
Theorem memory_finite_alias_condition_sound code locations s cells :
  Forall (memory_cell_address_binding code locations s) cells ->
  decision_run s (memory_finite_address_tree code cells) true ->
  locations_nonalias (memory_restrict_locations (memory_footprint_allowed cells) locations).
Proof.
  intros BINDINGS RUN; apply memory_restricted_locations_nonalias.
  apply (@memory_finite_address_separation_sound code locations s cells BINDINGS).
  symmetry; exact (proj1 (@memory_finite_address_exact code locations s cells BINDINGS true) RUN).
Qed.
Print Assumptions memory_finite_address_exact.
Print Assumptions memory_finite_alias_condition_sound.
