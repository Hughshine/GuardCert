From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightPureExpr ClightTempFrame ClightTempFootprint
  ClightNoWrap ClightRedundantSet ClightLoopSyntax ClightFrontendLoopProtocol ClightRegionProgress CompCertMemoryActions.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightExpressionHeaderCapture
  ClightExpressionBodyTransport ClightSignedExpressionProgress ClightStrictLoopProgress
  ClightObservedHeaderPrefix ClightCheckPlanFrame ClightAffineFirstBodyReceipt.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition signed_load_offset pointer (delta : int) :=
  Ebinop Oadd (signed_load pointer) (Econst_int delta type_int32s) type_int32s.
Definition loaded_offset_loop row pointer delta body :=
  strict_frontend_loop row (signed_expression_test row (signed_load_offset pointer delta)) body.

Lemma signed_load_offset_eval ge locals temps memory pointer delta block offset raw :
  temps!pointer=Some(Vptr block offset) -> Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint raw) ->
  eval_expr ge locals temps memory (signed_load_offset pointer delta) (Vint(Int.add raw delta)).
Proof.
  intros POINTER READ; unfold signed_load_offset; eapply eval_Ebinop.
  - eapply eval_Elvalue with (loc:=block) (ofs:=offset) (bf:=Full).
    + apply eval_Ederef,eval_Etempvar; exact POINTER.
    + apply deref_loc_value with (chunk:=Mint32); [reflexivity|exact READ].
  - apply eval_Econst_int.
  - reflexivity.
Qed.

Lemma signed_load_offset_inv ge locals temps memory pointer delta upper :
  eval_expr ge locals temps memory (signed_load_offset pointer delta) (Vint upper) ->
  exists block offset raw, temps!pointer=Some(Vptr block offset) /\
    Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint raw) /\ upper=Int.add raw delta.
Proof.
  intro EVAL; apply scalar_binary_inv in EVAL.
  destruct EVAL as [loaded [constant [LOAD [CONST OP]]]].
  apply scalar_const_inv in CONST; subst constant.
  unfold Cop.sem_binary_operation in OP; cbn [typeof signed_load] in OP.
  destruct loaded; try discriminate OP.
  change (Some(Vint(Int.add i delta))=Some(Vint upper)) in OP; injection OP as RESULT.
  destruct (signed_load_inv LOAD) as [block [offset [POINTER READ]]].
  exists block,offset,i; repeat split; try assumption; congruence.
Qed.

(** A mathematical snapshot of the actual entry observation. There is no
    second runtime load or extra raw-value temporary in this definition. *)
Definition loaded_offset_observations pointer entry : list (memory_location * val) :=
  match (entry_temps entry)!pointer with
  | Some(Vptr block offset) => match Mem.loadv Mint32 (entry_memory entry) (Vptr block offset) with
    | Some value => [(MemoryLocation Mint32 block (Ptrofs.unsigned offset),value)]
    | None => [] end
  | _ => [] end.
Definition loaded_offset_cached_header pointer delta cache entry :=
  exists block offset raw, (entry_temps entry)!pointer=Some(Vptr block offset) /\
    Mem.loadv Mint32 (entry_memory entry) (Vptr block offset)=Some(Vint raw) /\
    (entry_temps entry)!cache=Some(Vint(Int.add raw delta)).

Lemma loaded_offset_initial_observations pointer delta cache entry :
  loaded_offset_cached_header pointer delta cache entry ->
  header_observations_match (loaded_offset_observations pointer entry) (entry_memory entry).
Proof.
  intros [block [offset [raw [POINTER [READ CACHE]]]]].
  unfold loaded_offset_observations; rewrite POINTER,READ.
  unfold header_observations_match; constructor; [|constructor]; cbn [fst snd location_load].
  cbn [Mem.loadv] in READ; destruct (zle _ _); [exact READ|discriminate].
Qed.

Theorem loaded_offset_bound_from_observations pointer delta cache stable entry current memory upper :
  In pointer stable -> loaded_offset_cached_header pointer delta cache entry ->
  (entry_temps entry)!cache=Some(Vint upper) -> temp_agree stable (entry_temps entry) current ->
  header_observations_match (loaded_offset_observations pointer entry) memory ->
  eval_expr (entry_ge entry) (entry_env entry) current memory (signed_load_offset pointer delta) (Vint upper).
Proof.
  intros MEMBER [block [offset [raw [POINTER [INITIAL CACHE]]]]] WORD FRAME OBSERVED.
  assert (UPPER : upper=Int.add raw delta) by congruence; subst upper.
  unfold loaded_offset_observations in OBSERVED; rewrite POINTER,INITIAL in OBSERVED.
  inversion OBSERVED as [|first rest VALUE REST]; subst; cbn [fst snd location_load] in VALUE.
  assert (READ : Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint raw)).
  { cbn [Mem.loadv] in INITIAL |- *; destruct (zle _ _); [exact VALUE|discriminate]. }
  eapply signed_load_offset_eval; [rewrite FRAME by exact MEMBER; exact POINTER|exact READ].
Qed.

Theorem loaded_offset_capture_receipt fe ge locals temps memory row pointer delta body cache live after final :
  normal_statement body=true -> quiet_statement body=true ->
  check_plan_frameable (loaded_offset_loop row pointer delta body)=true ->
  ~In cache (statement_temps (loaded_offset_loop row pointer delta body)++live) ->
  exec_stmt fe ge locals temps memory (loaded_offset_loop row pointer delta body) E0 after final Out_normal ->
  exists upper prepared_after,
    exec_stmt fe ge locals temps memory (Sset cache (signed_load_offset pointer delta))
      E0 (PTree.set cache (Vint upper) temps) memory Out_normal /\
    exec_stmt fe ge locals (PTree.set cache (Vint upper) temps) memory
      (loaded_offset_loop row pointer delta body) E0 prepared_after final Out_normal /\
    temp_agree (statement_temps (loaded_offset_loop row pointer delta body)++live) after prepared_after /\
    affine_first_body_receipt row cache body fe (Entry ge locals (PTree.set cache (Vint upper) temps) memory) /\
    loaded_offset_cached_header pointer delta cache (Entry ge locals (PTree.set cache (Vint upper) temps) memory).
Proof.
  intros NORMAL QUIET FRAMEABLE PRIVATE SOURCE.
  destruct (@signed_expression_capture_receipt fe ge locals temps memory row (signed_load_offset pointer delta)
    body cache live after final eq_refl NORMAL QUIET FRAMEABLE PRIVATE SOURCE)
    as [upper [prepared_after [CAPTURE [PREPARED [PUBLIC [RECEIPT EVAL]]]]]].
  exists upper,prepared_after; split; [exact CAPTURE|split; [exact PREPARED|split; [exact PUBLIC|split; [exact RECEIPT|]]]].
  destruct (signed_load_offset_inv EVAL) as [block [offset [raw [POINTER [READ UPPER]]]]].
  exists block,offset,raw; cbn [entry_temps entry_memory]; split; [|split; [exact READ|rewrite UPPER; apply PTree.gss]].
  rewrite PTree.gso; [exact POINTER|].
  intro SAME; subst cache; apply PRIVATE,in_or_app; left.
  apply (signed_expression_bound_in_scope row (signed_load_offset pointer delta) body).
  change (pointer=pointer \/ False); left; reflexivity.
Qed.

(** The caller supplies preservation of the raw observation under accepted
    store checks. It does not supply execution of the cached source. *)
Theorem loaded_offset_body_initial_cached fe ge locals temps memory row pointer delta cache body stable written after final :
  In pointer stable -> In cache stable -> ~In row stable ->
  normal_statement body=true -> quiet_statement body=true -> writes_only written body ->
  ~In row written -> (forall id, In id stable -> ~In id written) ->
  loaded_offset_cached_header pointer delta cache (Entry ge locals temps memory) ->
  0<=Int.signed(temp_word cache temps) -> temps!row=Some(Vint Int.zero) ->
  (forall i current before exit last,
    0<=i<Int.signed(temp_word cache temps) -> current!row=Some(Vint(Int.repr i)) ->
    temp_agree stable temps current ->
    header_observations_match (loaded_offset_observations pointer (Entry ge locals temps memory)) before ->
    exec_stmt fe ge locals current before body E0 exit last Out_normal ->
    header_observations_match (loaded_offset_observations pointer (Entry ge locals temps memory)) last) ->
  exec_stmt fe ge locals temps memory (loaded_offset_loop row pointer delta body) E0 after final Out_normal ->
  exec_stmt fe ge locals temps memory (frontend_counted_loop row cache body) E0 after final Out_normal.
Proof.
  intros POINTER_MEMBER CACHE_MEMBER ROW_FRESH NORMAL QUIET WRITES ROW_UNWRITTEN STABLE_UNWRITTEN
    SNAPSHOT NONNEGATIVE ROW PRESERVE SOURCE.
  destruct SNAPSHOT as [block [offset [raw [POINTER [READ CACHE]]]]].
  cbn [entry_temps entry_memory] in POINTER,READ,CACHE.
  assert (SNAPSHOT : loaded_offset_cached_header pointer delta cache (Entry ge locals temps memory)).
  { exists block,offset,raw; repeat split; assumption. }
  eapply expression_body_initial_cached with (upper:=Int.add raw delta) (stable:=stable) (written:=written)
    (observations:=loaded_offset_observations pointer (Entry ge locals temps memory));
    try eassumption; try reflexivity.
  - unfold temp_word in NONNEGATIVE; rewrite CACHE in NONNEGATIVE; exact NONNEGATIVE.
  - intros i current before RANGE CURRENT FRAME OBSERVED.
    eapply loaded_offset_bound_from_observations with (entry:=Entry ge locals temps memory) (cache:=cache) (stable:=stable);
      [exact POINTER_MEMBER|exact SNAPSHOT|exact CACHE|exact FRAME|exact OBSERVED].
  - intros i current before exit last RANGE CURRENT FRAME OBSERVED RUN.
    eapply PRESERVE; [|exact CURRENT|exact FRAME|exact OBSERVED|exact RUN].
    unfold temp_word; rewrite CACHE; exact RANGE.
  - apply loaded_offset_initial_observations with (delta:=delta) (cache:=cache); exact SNAPSHOT.
Qed.

Print Assumptions signed_load_offset_eval.
Print Assumptions signed_load_offset_inv.
Print Assumptions loaded_offset_initial_observations.
Print Assumptions loaded_offset_bound_from_observations.
Print Assumptions loaded_offset_capture_receipt.
Print Assumptions loaded_offset_body_initial_cached.
