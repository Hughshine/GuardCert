From Stdlib Require Import List ZArith Lia Bool.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightNoWrap ClightTempFrame
  ClightCountedLoop ClightFrontendLoopProtocol ClightStraightLine ClightRedundantSet ClightRectangularGuard
  ClightRectangularLoops ClightRectangularStore CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryLoops GuardMemoryNaryCompute
  GuardMemoryNaryRanges GuardMemoryNaryAffineAccess GuardMemoryNaryAffineExpressions GuardMemoryRecursiveSource
  GuardMemoryPointerCompute GuardMemoryMultiPointerCompute GuardMemoryMultiPointerIdentifiers GuardMemoryMultiPointerCells
  GuardMemoryScalarPointerComputeSyntax GuardMemoryMultiPointerComputeSyntax GuardMemorySourceParameters
  GuardMemoryBufferOffsets GuardMemoryObservationStability GuardMemoryObservationExclusion
  GuardMemoryAffinePointerLoadedSource GuardMemoryAffineInnerPointerSyntax GuardMemoryParametricSourceClight.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightAffinePointerGuardExamples.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This source really reloads p[0] at each outer test:
    n = p[0]; for (; i < p[0]; ++i) {
      k=i+1; for (j=0; j<k; ++j) p[32+64*i+j] = q[4096+64*i+j]+a;
    }
    n is an ordinary retained source preload. The first theorem below does
    not require the observed cell to be stable. *)
Definition alp_source := loaded_bound_loop ap_i ap_p ap_outer.
Definition alp_layout := [ap_i;ap_j;ap_n].
Definition alp_limits := [64;64;65].
Definition alp_operations := match propose_memory_scalar_pointer_computes 8192 alp_layout [ap_a] [ap_body] with
  | Some operations => operations | None => [] end.
Definition alp_encoded := L.Sum (L.Var 0) (L.Constant 1).
Definition alp_stable := [ap_p;ap_q]++([ap_n]++[ap_a]).

Lemma alp_body_exact : flatten_region ap_body = map memory_pointer_compute_statement alp_operations.
Proof. vm_compute; reflexivity. Qed.
Lemma alp_operations_valid : Forall (memory_multi_pointer_compute_valid alp_limits alp_layout [ap_a] 8192) alp_operations.
Proof.
  apply Forall_forall; intros operation MEMBER; apply memory_multi_pointer_compute_check_sound.
  assert (CHECK : forallb (memory_multi_pointer_compute_check alp_limits alp_layout [ap_a] 8192) alp_operations = true)
    by (vm_compute; reflexivity).
  apply forallb_forall with (x:=operation) in CHECK; assumption.
Qed.
Lemma alp_outer_exact : flatten_region ap_outer =
  [memory_parametric_setup ap_k ap_header;rectangle_reset ap_j;frontend_counted_loop ap_j ap_k ap_body].
Proof. reflexivity. Qed.
Lemma alp_observation_excluded : memory_writes_exclude_cell alp_limits 8192 ap_p 0 alp_operations = true.
Proof. vm_compute; reflexivity. Qed.
Example alp_written_observation_rejected : memory_writes_exclude_cell alp_limits 8192 ap_p 97 alp_operations = false.
Proof. vm_compute; reflexivity. Qed.
Example alp_other_buffer_rejected : memory_writes_exclude_cell alp_limits 8192 ap_q 0 alp_operations = false.
Proof. vm_compute; reflexivity. Qed.
Example alp_written_observation_is_reached : exists operation, In operation alp_operations /\
  memory_nary_access_array (memory_nary_compute_write operation) = ap_p /\
  memory_nary_index_value (memory_nary_access_index (memory_nary_compute_write operation)) [1;1;3;0] = 97.
Proof.
  vm_compute; eexists; split; [left; reflexivity|split; reflexivity].
Qed.

Lemma alp_header_value ge locals temps memory i :
  temps ! ap_i = Some (Vint (Int.repr i)) ->
  eval_expr ge locals temps memory ap_header (Vint (Int.repr (i+1))).
Proof.
  intro ROW; unfold ap_header,ap_sum,ap_constant.
  replace (Int.repr (i+1)) with (Int.add (Int.repr i) (Int.repr 1)).
  - eapply eval_Ebinop; [constructor; exact ROW|constructor|reflexivity].
  - unfold Int.add; apply Int.eqm_samerepr,Int.eqm_add; apply Int.eqm_sym,Int.eqm_unsigned_repr.
Qed.
Lemma alp_source_active ge locals temps memory block offset N :
  temps ! ap_i = Some (Vint Int.zero) -> temps ! ap_p = Some (Vptr block offset) ->
  Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint (Int.repr N)) ->
  0 < N <= 64 -> expression_test (loaded_bound_test ap_i ap_p) (Entry ge locals temps memory) true.
Proof.
  intros ZERO POINTER READ RANGE.
  replace true with (Int.lt Int.zero (Int.repr N)).
  - apply loaded_bound_test_eval with (b:=block) (ofs:=offset); assumption.
  - unfold Int.lt; rewrite Int.signed_zero,Int.signed_repr by
      (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
    destruct (zlt 0 N); [reflexivity|lia].
Qed.

Theorem alp_loaded_source_scalar_word fe ge locals temps memory block offset N after final :
  temps ! ap_i = Some (Vint Int.zero) -> temps ! ap_p = Some (Vptr block offset) ->
  Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint (Int.repr N)) -> 0 < N <= 64 ->
  exec_stmt fe ge locals temps memory alp_source E0 after final Out_normal ->
  exists word, temps ! ap_a = Some (Vint word).
Proof.
  intros ZERO POINTER READ RANGE SOURCE.
  eapply (@memory_affine_pointer_loaded_first_words fe ge locals temps memory ap_i ap_p ap_j ap_k ap_header
    1 ap_body ap_outer after final [] [ap_a] alp_limits alp_layout 8192 alp_operations);
    [unfold ap_j,ap_k; congruence|unfold ap_header,ap_sum,ap_constant; apply pure_binary; [apply pure_temp|apply pure_int]|
     exact (@alp_source_active ge locals temps memory block offset N ZERO POINTER READ RANGE)|
     exact (@alp_header_value ge locals temps memory 0 ZERO)|lia|change (-2147483648 <= 1 <= 2147483647); lia|
     cbn; intros identifier [<-|[]]; unfold ap_a,ap_j,ap_k; split; congruence|
     exact alp_outer_exact|exact alp_body_exact|exact alp_operations_valid|
     intros identifier BAD; contradiction|
     apply memory_scalar_pointer_registers_check_sound; vm_compute; reflexivity|exact SOURCE|cbn; auto].
Qed.

(** Actual source-to-cache correspondence. All geometric obligations are
    derived from 0<N<=64 and the checked AST; the body-only scalar word is
    derived from the first real source body, before the stability proof. *)
Theorem alp_loaded_source_cached fe ge locals temps memory block offset N after final :
  temps ! ap_i = Some (Vint Int.zero) -> temps ! ap_n = Some (Vint (Int.repr N)) ->
  temps ! ap_p = Some (Vptr block offset) ->
  Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint (Int.repr N)) -> 0 < N <= 64 ->
  exec_stmt fe ge locals temps memory alp_source E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory ap_source E0 after final Out_normal /\
    Mem.loadv Mint32 final (Vptr block offset) = Some (Vint (Int.repr N)).
Proof.
  intros ZERO CACHE POINTER READ RANGE SOURCE.
  destruct (@alp_loaded_source_scalar_word fe ge locals temps memory block offset N after final
    ZERO POINTER READ RANGE SOURCE) as [scalar SCALAR].
  set (rows := Z.to_nat N).
  assert (COUNT : Z.of_nat rows = N) by (unfold rows; apply Z2Nat.id; lia).
  rewrite <-COUNT in CACHE,READ |- *.
  eapply (@memory_affine_pointer_loaded_source_cached fe ge locals ap_i ap_n ap_j ap_k ap_p ap_header alp_encoded ap_body ap_outer
    [] [ap_a] [ap_p;ap_q] [65] 64 64 8192 alp_operations)
    with (rows:=rows) (geometry_values:=[]) (scalar_values:=[Int.signed scalar]) (base:=temps) (block:=block) (offset:=offset);
    [unfold ap_i,ap_j; congruence|unfold ap_i,ap_n; congruence|unfold ap_n,ap_j; congruence|
     unfold ap_i,ap_k; congruence|unfold ap_n,ap_k; congruence|unfold ap_j,ap_k; congruence|
     cbn; intros identifier [<-|[<-|[<-|[<-|[]]]]]; unfold ap_i,ap_n,ap_j,ap_k,ap_p,ap_q,ap_a; repeat split; congruence|
     vm_compute; repeat (apply NoDup_cons; [cbn; intuition congruence|]); apply NoDup_nil|exact alp_operations_valid|
     vm_compute; apply Forall_cons; [split; [left; reflexivity|apply Forall_cons; [right; left; reflexivity|apply Forall_nil]]|
       apply Forall_nil]|exact alp_body_exact|exact alp_outer_exact|
     intro EMPTY; rewrite EMPTY in COUNT; cbn in COUNT; lia|
     unfold signed_range; rewrite COUNT; change Int.min_signed with (-2147483648);
       change Int.max_signed with 2147483647; lia|
     rewrite COUNT; lia|
     change (forall i, 0 <= i < Z.of_nat rows -> (0 <= i+1 <= 64) /\ signed_range (i+1));
       intros i IR; unfold signed_range; rewrite COUNT in IR;
       change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; repeat split; lia|
     apply Forall2_cons; [rewrite COUNT; lia|apply Forall2_nil]|
     apply Forall2_cons; [exact CACHE|apply Forall2_nil]|
     apply Forall2_cons; [rewrite Int.repr_signed; exact SCALAR|apply Forall2_nil]|
     unfold ap_header,ap_sum,ap_constant; apply pure_binary; [apply pure_temp|apply pure_int]|
     intros i current before IR ROW FRAME; cbn [alp_encoded L.eval_expr]; apply alp_header_value; exact ROW|
     cbn; auto|exact POINTER|
     intros i j IR JR;
       pose proof (@memory_writes_exclude_cell_with_scalars alp_limits 8192 ap_p 0 alp_operations temps
         [i;j;Z.of_nat rows] [Int.signed scalar] block offset alp_observation_excluded
         ltac:(change (0 <= j < i+1) in JR; unfold alp_limits,memory_nary_ranges;
           repeat (apply Forall2_cons; [rewrite COUNT in *; lia|]); apply Forall2_nil) POINTER) as APART;
       unfold memory_pointer_buffer_offset,memory_buffer_offset in APART; rewrite Z.mul_0_r,Z.add_0_r,
         Z.mod_small in APART by (pose proof (Ptrofs.unsigned_range offset); lia); exact APART|
     exact ZERO|apply temp_agree_refl|exact READ|exact SOURCE].
Qed.

Print Assumptions alp_observation_excluded.
Print Assumptions alp_written_observation_rejected.
Print Assumptions alp_other_buffer_rejected.
Print Assumptions alp_written_observation_is_reached.
Print Assumptions alp_loaded_source_scalar_word.
Print Assumptions alp_loaded_source_cached.
