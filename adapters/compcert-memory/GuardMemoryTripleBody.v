From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFiniteRegion ClightStraightLine ClightRectangularStore ClightRectangularGuard
  ClightFrontendLoopProtocol ClightCountedLoop ClightRectangularLoops.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryLoops GuardMemoryMultipleArrays GuardMemoryLayoutRegistry
  GuardMemoryRegistryBackend GuardMemoryNaryRanges GuardMemoryNaryBodyModel GuardMemoryNaryLoops GuardMemoryNaryLift GuardMemoryTripleSource.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition memory_triple_valuation (row column : ident) (i j k : Z) (identifier : ident) :=
  if peq identifier row then i else if peq identifier column then j else k.
Lemma memory_triple_valuation_values row column depth i j k :
  row <> column -> row <> depth -> column <> depth ->
  map (memory_triple_valuation row column i j k) [row;column;depth] = [i;j;k].
Proof.
  intros RC RD CD; unfold memory_triple_valuation; cbn; repeat destruct peq; congruence.
Qed.
Lemma memory_triple_valuation_words row column depth i j k temps :
  row <> column -> row <> depth -> column <> depth ->
  temps ! row = Some (Vint (Int.repr i)) -> temps ! column = Some (Vint (Int.repr j)) ->
  temps ! depth = Some (Vint (Int.repr k)) ->
  forall identifier, In identifier [row;column;depth] ->
    temps ! identifier = Some (Vint (Int.repr (memory_triple_valuation row column i j k identifier))).
Proof.
  intros RC RD CD ROW COLUMN DEPTH identifier MEMBER; cbn in MEMBER;
    destruct MEMBER as [<-|[<-|[<-|ABSENT]]]; try contradiction;
    unfold memory_triple_valuation; repeat destruct peq; congruence.
Qed.

Theorem memory_triple_body_source_decode fe ge locals row row_bound column column_bound depth depth_bound
  row_limit column_limit depth_limit body middle_body outer_body
  (model : memory_nary_body_model [row_limit;column_limit;depth_limit] [row;column;depth] body)
  rows columns depths temps memory after final :
  row <> column -> row <> depth -> row <> row_bound -> row <> column_bound -> row <> depth_bound ->
  column <> depth -> column <> column_bound -> column <> depth_bound -> column <> row_bound ->
  depth <> depth_bound -> depth <> column_bound -> depth <> row_bound ->
  signed_range (Z.of_nat rows) -> signed_range (Z.of_nat columns) -> signed_range (Z.of_nat depths) ->
  0 < Z.of_nat rows <= row_limit -> 0 < Z.of_nat columns <= column_limit -> 0 < Z.of_nat depths <= depth_limit ->
  flatten_region middle_body = [rectangle_reset depth;frontend_counted_loop depth depth_bound body] ->
  flatten_region outer_body = [rectangle_reset column;frontend_counted_loop column column_bound middle_body] ->
  temps ! row = Some (Vint Int.zero) -> temps ! row_bound = Some (Vint (Int.repr (Z.of_nat rows))) ->
  temps ! column_bound = Some (Vint (Int.repr (Z.of_nat columns))) ->
  temps ! depth_bound = Some (Vint (Int.repr (Z.of_nat depths))) ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop row row_bound outer_body) E0 after final Out_normal ->
  exists entries,
    Forall2 (memory_descriptor_binding ge locals) (nary_body_descriptors model) entries /\
    NoDup (map memory_array_id entries) /\
    Forall (fun entry => Mem.valid_pointer memory (memory_array_block entry) 0 = true) entries /\
    L.loop_semantics (memory_nary_rectangle 0 3 (nary_body_instructions model))
      [Z.of_nat rows;Z.of_nat columns;Z.of_nat depths]
      (RuntimeState (memory_array_registry entries) memory) (RuntimeState (memory_array_registry entries) final) /\
    after = PTree.set row (Vint (Int.repr (Z.of_nat rows)))
      (PTree.set column (Vint (Int.repr (Z.of_nat columns)))
        (PTree.set depth (Vint (Int.repr (Z.of_nat depths))) temps)).
Proof.
  intros RC RD RN RCB RDB CD CC CDB CN DD DC DN RRANGE CRANGE DRANGE RPOS CPOS DPOS
    MIDDLE OUTER ZERO BOUND CBOUND DBOUND SOURCE.
  set (physical := nary_body_point model ge locals).
  assert (POINT : forall i j k le before next target,
    0 <= i < Z.of_nat rows -> 0 <= j < Z.of_nat columns -> 0 <= k < Z.of_nat depths ->
    le ! row = Some (Vint (Int.repr i)) -> le ! column = Some (Vint (Int.repr j)) -> le ! depth = Some (Vint (Int.repr k)) ->
    exec_stmt fe ge locals le before body E0 next target Out_normal -> physical [i;j;k] before target /\ next = le).
  { intros i j k le before next target I J K ROW COLUMN DEPTH RUN.
    pose proof (@memory_triple_valuation_values row column depth i j k RC RD CD) as VALUES.
    rewrite <- VALUES; eapply nary_body_decode.
    - rewrite VALUES; repeat constructor; lia.
    - eapply memory_triple_valuation_words; eassumption.
    - exact RUN. }
  destruct (@memory_triple_source_decode fe ge locals row row_bound column column_bound depth depth_bound body middle_body outer_body
    (fun i j k => physical [i;j;k]) rows columns depths temps memory after final
    RC RD RN RCB RDB CD CC CDB CN DD DC DN (nary_body_normal model) (nary_body_quiet model) (nary_body_writes model)
    RRANGE CRANGE DRANGE ltac:(intro SAME; rewrite SAME in RPOS; cbn in RPOS; lia)
    ltac:(intro SAME; rewrite SAME in CPOS; cbn in CPOS; lia)
    MIDDLE OUTER POINT ZERO BOUND CBOUND DBOUND SOURCE) as [ITER EXIT].
  change (memory_nary_iterations physical [rows;columns;depths] [] memory final) in ITER.
  assert (NONEMPTY : Forall (fun count => count <> O) [rows;columns;depths])
    by (repeat constructor; intro SAME; subst; cbn in *; lia).
  destruct (@memory_nary_first mem physical [rows;columns;depths] NONEMPTY [] memory final ITER) as [first HEAD].
  destruct (@nary_body_registry _ _ _ model ge locals memory first HEAD) as [entries [ARRAYS [UNIQUE POINTERS]]].
  exists entries; split; [exact ARRAYS|]; split; [exact UNIQUE|]; split; [exact POINTERS|]; split; [|exact EXIT].
  apply (proj1 (@memory_nary_rectangle_lift (memory_array_registry entries) (nary_body_instructions model) physical
    [rows;columns;depths] memory final ltac:(
      intros values before target DOMAIN; cbn [memory_nary_domain] in DOMAIN;
      destruct DOMAIN as [i [I [j [J [k [K SAME]]]]]]; cbn in SAME; subst values;
      apply nary_body_correspondence; [exact ARRAYS|exact UNIQUE|repeat constructor; lia]))).
  exact ITER.
Qed.
Print Assumptions memory_triple_body_source_decode.
