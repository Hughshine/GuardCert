From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightCountedLoop ClightRedundantSet
  CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestSourceDecode AffineNestGuardPackage
  AffineNestScanNamespace.
From GuardInterface Require Import ClightLoadedAffineNumericGuard ClightLoadedBodyPrefix
  ClightLoadedAffineBodyPrefix ClightLoadedAffineBodyDomain ClightLoadedAffineWriteTest ClightLoadedAffineBodyScan
  ClightShortCircuitPrefixLoop ClightLoadedAffineRootScan ClightLoadedOffsetHeader ClightExpressionBodyPrefix
  ClightLoadedOffsetAffineBody ClightAffineBodyReceipt ClightAffineObservedBodyScan.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Section ROOT.
Variables source : statement.
Variables parameters public : list ident.
Variable proposal : affine_guard_proposal.
Variable package : affine_guard_package source parameters public proposal.
Variable pointer : ident.
Variable delta : int.
Hypothesis NAMES : affine_loaded_body_names_check proposal pointer=true.
Variable fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop.
Variable entry : clight_entry.
Variable code : GuardMemoryLoops.L.stmt.
Hypothesis LOWER : affine_loaded_body_model parameters proposal=Some code.
Variables block : Values.block.
Variable offset : ptrofs.
Hypothesis POINTER : (entry_temps entry)!pointer=Some(Vptr block offset).
Let observation := MemoryLocation Mint32 block(Ptrofs.unsigned offset).
Let prefix index := offset_affine_body_prefix fe parameters proposal pointer delta index entry.
Let count := Int.signed(temp_word(affine_proposed_bound proposal)(entry_temps entry)).
Let test index := affine_loaded_body_check_result proposal index entry observation.

Lemma offset_affine_scan_next_prefix index :
  0<=index<count -> prefix index -> test index=true -> prefix(index+1).
Proof.
  intros RANGE PREFIX CHECK.
  destruct(affine_loaded_numeric_body_properties package) as [NORMAL QUIET].
  destruct(@affine_loaded_body_controls source parameters public proposal package pointer NAMES) as [ROOT PROTECTED].
  assert(STABLE:forall identifier, In identifier(affine_loaded_body_stable parameters proposal pointer) ->
    ~In identifier(affine_nest_controls(affine_proposed_child proposal))).
  { intros identifier MEMBER BAD; apply(PROTECTED identifier MEMBER).
    cbn [affine_nest_mutated affine_proposal_nest]; right; exact BAD. }
  assert(ROW_FRESH:~In(affine_proposed_iterator proposal)(affine_loaded_body_stable parameters proposal pointer)).
  { intro MEMBER; apply(PROTECTED _ MEMBER); cbn [affine_nest_mutated affine_proposal_nest]; left; reflexivity. }
  eapply expression_body_prefix_advance with(written:=affine_nest_controls(affine_proposed_child proposal));
    [reflexivity|exact ROW_FRESH|exact NORMAL|exact QUIET|exact(affine_loaded_body_writes package)|
     exact ROOT|exact STABLE| |apply offset_affine_body_header|exact PREFIX|exact(proj2 RANGE)|].
  - intros ge locals current memory after final RUN; eapply affine_loaded_body_memory_back with(package:=package); exact RUN.
  - exact(@offset_affine_body_check_preserved source parameters public proposal package pointer delta NAMES
      fe entry index code block offset PREFIX (proj2 RANGE) LOWER POINTER CHECK).
Qed.

Theorem offset_affine_root_scan_execution controls flag live
  (names : affine_scan_namespace(affine_proposal_nest proposal) parameters live controls flag) checked :
  prefix 0 -> incl parameters live -> incl(pointer::affine_proposed_pointers proposal) live ->
  In(affine_proposed_bound proposal) live -> temp_agree live(entry_temps entry) checked ->
  exists after,
    exec_stmt fe (entry_ge entry)(entry_env entry) checked(entry_memory entry)
      (affine_loaded_root_scan_statement proposal pointer controls flag) E0 after(entry_memory entry) Out_normal /\
    temp_agree live checked after /\
    after!flag=Some(memory_boolean_word(affine_loaded_root_scan_result proposal entry observation)) /\
    (affine_loaded_root_scan_result proposal entry observation=true ->
      forall index, 0<=index<count -> offset_affine_body_preserved fe parameters proposal pointer index entry).

Proof.
  intros PREFIX PARAM_LIVE POINTER_LIVE CACHE_LIVE FRAME.
  pose proof PREFIX as [READY [CACHE [RANGE REST]]].
  assert(NONNEGATIVE:0<=count) by(unfold count; lia).
  assert(UPPER:signed_range count) by(apply Int.signed_range).
  set(cursor:=controls(affine_proposed_iterator proposal)).
  set(bound:=controls(affine_proposed_bound proposal)).
  assert(DISTINCT:cursor<>bound).
  { pose proof(affine_scan_names_unique names) as UNIQUE;
      cbn [affine_proposal_nest affine_nest_controls map] in UNIQUE.
    apply NoDup_cons_iff in UNIQUE as [PRIVATE REST']. intro SAME; apply PRIVATE; left; symmetry; exact SAME. }
  destruct(affine_scan_names_private names (affine_proposed_iterator proposal) ltac:(cbn; auto)) as [CURSOR_PRIVATE CURSOR_FLAG].
  destruct(affine_scan_names_private names (affine_proposed_bound proposal) ltac:(cbn; auto)) as [BOUND_PRIVATE BOUND_FLAG].
  assert(CURSOR_LIVE:~In cursor live) by(intro BAD; apply CURSOR_PRIVATE,in_or_app; right; exact BAD).
  assert(BOUND_LIVE:~In bound live) by(intro BAD; apply BOUND_PRIVATE,in_or_app; right; exact BAD).
  assert(FLAG_LIVE:~In flag live) by(intro BAD; apply(affine_scan_names_flag_private names),in_or_app; right; exact BAD).
  set(cached:=PTree.set bound(Vint(temp_word(affine_proposed_bound proposal)(entry_temps entry))) checked).
  set(flagged:=PTree.set flag(Vint Int.one) cached).
  set(initialized:=PTree.set cursor(Vint Int.zero) flagged).
  assert(INIT_FRAME:temp_agree live checked initialized).
  { eapply temp_agree_trans with(le1:=cached); [apply temp_agree_set; exact BOUND_LIVE|].
    eapply temp_agree_trans with(le1:=flagged); apply temp_agree_set; assumption. }
  assert(INIT_CURSOR:initialized!cursor=Some(Vint(Int.repr 0))).
  { unfold initialized; apply PTree.gss. }
  assert(INIT_BOUND:initialized!bound=Some(Vint(Int.repr count))).
  { unfold initialized,flagged,cached; rewrite PTree.gso by congruence.
    rewrite PTree.gso by exact BOUND_FLAG; rewrite PTree.gss.
    unfold count; rewrite Int.repr_signed; reflexivity. }
  assert(INIT_FLAG:initialized!flag=Some(memory_boolean_word true)).
  { unfold initialized,flagged; rewrite PTree.gso by(exact(not_eq_sym CURSOR_FLAG)); apply PTree.gss. }
  assert(BODY:forall index current, signed_range index -> 0<=index<count -> prefix index ->
    current!cursor=Some(Vint(Int.repr index)) -> current!bound=Some(Vint(Int.repr count)) ->
    current!flag=Some(memory_boolean_word true) -> temp_agree live(entry_temps entry) current ->
    exists after,
      exec_stmt fe (entry_ge entry)(entry_env entry) current(entry_memory entry)
        (affine_loaded_body_scan_statement proposal pointer controls flag) E0 after(entry_memory entry) Out_normal /\
      temp_agree(cursor::bound::live) current after /\ after!flag=Some(memory_boolean_word(test index))).
  { intros index current INDEX ACTIVE INV ROW BOUND FLAG PUBLIC_FRAME.
    pose proof(@offset_affine_prefix_body_receipt source parameters public proposal package pointer delta
      fe entry index INV (proj2 ACTIVE)) as RECEIPT.
    pose proof(@offset_affine_prefix_observed_read parameters proposal pointer delta fe entry index INV) as OBSERVED.
    destruct(@affine_observed_body_scan_execution source parameters public proposal pointer package controls flag live names
      fe entry index code current true block offset NAMES RECEIPT OBSERVED LOWER PARAM_LIVE POINTER_LIVE PUBLIC_FRAME ROW FLAG POINTER)
      as [after [RUN [AFTER RESULT]]].
    exists after; split; [exact RUN|split; [exact AFTER|]].
    rewrite andb_true_l in RESULT; exact RESULT. }
  destruct(@short_circuit_prefix_loop_execution fe (entry_ge entry)(entry_env entry)(entry_memory entry)
    cursor bound flag (affine_loaded_body_scan_statement proposal pointer controls flag) live(entry_temps entry) 0 count prefix test
    DISTINCT CURSOR_FLAG BOUND_FLAG CURSOR_LIVE UPPER offset_affine_scan_next_prefix BODY (Z.to_nat count) 0 initialized)
    as [after [RUN [AFTER [RESULT ACCEPTED]]]].
  - rewrite Z2Nat.id by exact NONNEGATIVE; lia.
  - lia.
  - unfold signed_range; change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia.
  - exact PREFIX.
  - exact INIT_CURSOR.
  - exact INIT_BOUND.
  - exact INIT_FLAG.
  - eapply temp_agree_trans; eassumption.
  - exists after; split.
    + unfold affine_loaded_root_scan_statement.
      eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=cached)(m1:=entry_memory entry).
      * constructor; constructor.
        destruct CACHE as [word WORD]; cbn [entry_temps] in WORD.
        rewrite FRAME by exact CACHE_LIVE; unfold temp_word; rewrite WORD; reflexivity.
      * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=flagged)(m1:=entry_memory entry); [constructor; constructor|].
        eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(le1:=initialized)(m1:=entry_memory entry); [constructor; constructor|exact RUN].
    + split; [eapply temp_agree_trans; [exact INIT_FRAME|exact AFTER]|split; [exact RESULT|]].
      intros ACCEPT index ACTIVE.
      destruct(ACCEPTED ACCEPT index ACTIVE) as [INV CHECK].
      exact(@offset_affine_body_check_preserved source parameters public proposal package pointer delta NAMES fe entry index code
        block offset INV (proj2 ACTIVE) LOWER POINTER CHECK).
Qed.
End ROOT.

Print Assumptions offset_affine_scan_next_prefix.
Print Assumptions offset_affine_root_scan_execution.
