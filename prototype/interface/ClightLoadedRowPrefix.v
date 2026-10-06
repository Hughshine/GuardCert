From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightTempFrame ClightRedundantSet ClightNoWrap
  ClightLoopSyntax ClightRegionProgress ClightLoopExecution CompCertMemoryActions.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightStrictIteration
  ClightStrictLoopProgress ClightAffineLoadedBoundTransport ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section ROWS.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variables row cache parameter : ident.
Variable outer_body : statement.
Variable stable : list ident.
Variable ready : clight_entry -> Prop.
Variable upper : clight_entry -> Z -> Z.
Variable point : clight_entry -> Z -> Z -> mem -> mem -> Prop.
Hypotheses (PARAMETER : In parameter stable) (FRESH_ROW : ~ In row stable).
Hypotheses (NORMAL : normal_statement outer_body = true) (QUIET : quiet_statement outer_body = true).

Let count entry := Int.signed (temp_word cache (entry_temps entry)).

(** The domain instance decodes one actual, completed row. It must prove the
    point correspondence and public frame; no later row is assumed reachable. *)
Hypothesis DECODE : forall entry i current memory after final,
  ready entry -> 0 <= i < count entry -> current ! row = Some (Vint (Int.repr i)) ->
  temp_agree stable (entry_temps entry) current ->
  exec_stmt fe (entry_ge entry) (entry_env entry) current memory outer_body E0 after final Out_normal ->
  counted_iterations (point entry i) (Z.to_nat (upper entry i)) 0 memory final /\
    after ! row = current ! row /\ temp_agree stable current after.
Hypothesis WIDTH : forall entry i, ready entry -> 0 <= i < count entry -> 0 <= upper entry i.
Hypothesis PERMISSIONS : forall entry i j before after,
  point entry i j before after -> memory_accesses_back before after.

(** This ghost invariant contains remaining actual source execution. Memory
    equality is deliberately absent: earlier source stores can change values.
    Only their permissions are transported to the original guard entry. *)
Definition loaded_row_prefix i entry :=
  ready entry /\ register_domain cache entry /\ 0 <= i <= count entry /\
  exists block offset current memory after final,
    (entry_temps entry) ! parameter = Some (Vptr block offset) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) =
      Some (Vint (temp_word cache (entry_temps entry))) /\
    current ! row = Some (Vint (Int.repr i)) /\
    temp_agree stable (entry_temps entry) current /\
    Mem.loadv Mint32 memory (Vptr block offset) =
      Some (Vint (temp_word cache (entry_temps entry))) /\
    memory_accesses_back (entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory
      (loaded_bound_loop row parameter outer_body) E0 after final Out_normal.

Definition loaded_row_receipt i entry :=
  exists current memory after final,
    current ! row = Some (Vint (Int.repr i)) /\
    temp_agree stable (entry_temps entry) current /\
    memory_accesses_back (entry_memory entry) memory /\
    exec_stmt fe (entry_ge entry) (entry_env entry) current memory outer_body E0 after final Out_normal /\
    counted_iterations (point entry i) (Z.to_nat (upper entry i)) 0 memory final.

Lemma loaded_row_prefix_test i entry block offset current memory :
  0 <= i < count entry ->
  (entry_temps entry) ! parameter = Some (Vptr block offset) ->
  current ! row = Some (Vint (Int.repr i)) ->
  temp_agree stable (entry_temps entry) current ->
  Mem.loadv Mint32 memory (Vptr block offset) = Some (Vint (temp_word cache (entry_temps entry))) ->
  expression_test (loaded_bound_test row parameter) (Entry (entry_ge entry) (entry_env entry) current memory) true.
Proof.
  intros RANGE POINTER ROW FRAME READ.
  assert (SIGNED : signed_range i) by
    (pose proof (Int.signed_range (temp_word cache (entry_temps entry))); unfold count in RANGE;
     unfold signed_range; change Int.min_signed with (-2147483648) in *; lia).
  assert (LT : Int.lt (Int.repr i) (temp_word cache (entry_temps entry)) = true).
  { unfold Int.lt; rewrite Int.signed_repr by exact SIGNED.
    destruct (zlt i (Int.signed (temp_word cache (entry_temps entry)))); [reflexivity|unfold count in RANGE; lia]. }
  rewrite <- LT; eapply loaded_bound_test_eval; [exact ROW| |exact READ].
  rewrite FRAME by exact PARAMETER; exact POINTER.
Qed.

(** All accesses within a reached row are supported by that actual row, even
    when the row eventually writes the loaded bound. *)
Theorem loaded_row_prefix_receipt i entry :
  loaded_row_prefix i entry -> i < count entry -> loaded_row_receipt i entry.
Proof.
  intros [READY [CACHE [RANGE [block [offset [current [memory [after [final
    [POINTER [INITIAL [ROW [FRAME [READ [BACK SOURCE]]]]]]]]]]]]]]] ACTIVE.
  pose proof (@loaded_row_prefix_test i entry block offset current memory ltac:(lia) POINTER ROW FRAME READ) as TEST.
  destruct (@strict_active_iteration fe (entry_ge entry) (entry_env entry) row
    (loaded_bound_test row parameter) outer_body current memory after final NORMAL QUIET TEST SOURCE)
    as [body_temps [body_memory [next_temps [next_memory [BODY [INC TAIL]]]]]].
  destruct (@DECODE entry i current memory body_temps body_memory READY ltac:(lia) ROW FRAME BODY)
    as [ITER [AFTER_ROW AFTER_FRAME]].
  exists current,memory,body_temps,body_memory;
    split; [exact ROW|split; [exact FRAME|split; [exact BACK|split; [exact BODY|exact ITER]]]].
Qed.

(** Success proves preservation for this row before advancing. A failed
    probe need not establish either this conclusion or another receipt. *)
Theorem loaded_row_prefix_advance i entry :
  loaded_row_prefix i entry -> i < count entry ->
  (forall block offset,
    (entry_temps entry) ! parameter = Some (Vptr block offset) ->
    forall j before after, 0 <= j < upper entry i -> point entry i j before after ->
      location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) after =
      location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) before) ->
  loaded_row_prefix (i+1) entry.
Proof.
  intros [READY [CACHE [RANGE [block [offset [current [memory [after [final
    [POINTER [INITIAL [ROW [FRAME [READ [BACK SOURCE]]]]]]]]]]]]]]] PRESUME PRESERVE.
  pose proof (@loaded_row_prefix_test i entry block offset current memory ltac:(lia) POINTER ROW FRAME READ) as TEST.
  destruct (@strict_active_iteration fe (entry_ge entry) (entry_env entry) row
    (loaded_bound_test row parameter) outer_body current memory after final NORMAL QUIET TEST SOURCE)
    as [body_temps [body_memory [next_temps [next_memory [BODY [INC TAIL]]]]]].
  destruct (@DECODE entry i current memory body_temps body_memory READY ltac:(lia) ROW FRAME BODY)
    as [ITER [AFTER_ROW AFTER_FRAME]].
  assert (BODY_READ : Mem.loadv Mint32 body_memory (Vptr block offset) =
    Some (Vint (temp_word cache (entry_temps entry)))).
  { assert (SAME : location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) body_memory =
      location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) memory).
    { eapply counted_observation_preserved; [|exact ITER].
      intros j JR first last STEP; apply PRESERVE with (j:=j); [exact POINTER| |exact STEP].
      rewrite Z2Nat.id in JR by (apply WIDTH; [exact READY|lia]); lia. }
    cbn [Mem.loadv] in READ |- *.
    destruct (zle (Ptrofs.unsigned offset + size_chunk Mint32) Ptrofs.modulus); [|discriminate READ].
    change (location_load (MemoryLocation Mint32 block (Ptrofs.unsigned offset)) body_memory = Some (Vint (temp_word cache (entry_temps entry))));
      rewrite SAME; exact READ. }
  assert (BODY_ROW : body_temps ! row = Some (Vint (Int.repr i))) by (rewrite AFTER_ROW; exact ROW).
  assert (SIGNED : signed_range i) by
    (pose proof (Int.signed_range (temp_word cache (entry_temps entry))); unfold count in PRESUME;
     unfold signed_range; change Int.min_signed with (-2147483648) in *; lia).
  assert (STRICT : strict_counter_active row body_temps).
  { exists (Int.repr i); split; [exact BODY_ROW|rewrite Int.signed_repr by exact SIGNED;
      pose proof (Int.signed_range (temp_word cache (entry_temps entry))); unfold count in PRESUME; lia]. }
  destruct (@strict_increment_execution_exact fe (entry_ge entry) (entry_env entry) row
    body_temps body_memory E0 next_temps next_memory Out_normal STRICT INC) as [_ [NEXT [MEMORY _]]].
  subst next_temps next_memory; rewrite (@counter_increment_small row body_temps i BODY_ROW) in TAIL.
  split; [exact READY|split; [exact CACHE|split; [lia|]]].
  exists block,offset,(PTree.set row (Vint (Int.repr (i+1))) body_temps),body_memory,after,final.
  split; [exact POINTER|split; [exact INITIAL|split; [apply PTree.gss|split; [|split; [exact BODY_READ|split; [|exact TAIL]]]]]].
  - intros identifier MEMBER; rewrite PTree.gso by (intro SAME; subst identifier; contradiction).
    rewrite AFTER_FRAME by exact MEMBER; exact (FRAME identifier MEMBER).
  - eapply memory_accesses_back_trans; [exact BACK|].
    eapply counted_memory_accesses_back; [|exact ITER].
    intros j first last STEP; eapply PERMISSIONS; exact STEP.
Qed.
End ROWS.

Print Assumptions loaded_row_prefix_test.
Print Assumptions loaded_row_prefix_receipt.
Print Assumptions loaded_row_prefix_advance.
