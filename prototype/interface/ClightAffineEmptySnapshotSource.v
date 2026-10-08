From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightNoWrap ClightCountedLoop ClightLoopSyntax
  ClightRectangularLoops ClightFrontendLoopProtocol ClightRegionProgress ClightCountedProtocol.
From GuardMemory Require Import GuardMemoryArrayBackend GuardMemoryAffineSourceExpressions
  GuardMemoryAffineSourceValuation GuardMemoryAffineSourceContext GuardMemoryParametricSourceDomain GuardMemoryParametricGuard
  GuardMemoryAffineInnerPointerSyntax GuardMemoryAffineInnerPointerSourceDomain
  GuardMemoryAffineInnerPointerRegionSource GuardMemoryPointerSequence.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightAffineSnapshotSyntax ClightAffineSnapshotRows
  ClightAffineSnapshotSourceInputs ClightAffineSnapshotPreparation ClightAffinePreparedState
  ClightAffinePreparedRows ClightAffineZeroSnapshotPreparation ClightAffineZeroSnapshotRows ClightAffineZeroSnapshotPrefix
  ClightWordReadSnapshots ClightAffineHeaderSnapshots ClightAffineEmptyWidth
  ClightAffineEmptyExecution ClightAffineEmptySnapshotCondition ClightQuietDeterminacy ClightStrictLoopProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A language/domain producer: the checked source package and original read
    receipts suffice. No body typing, array validity or separation is added. *)
Section SOURCE.
Variable original : statement.
Variable site : affine_snapshot_source_package original.
Let package:=snapshot_cached_package site.
Let shape:=affine_inner_pointer_shape package.
Let row:=affine_inner_pointer_row shape.
Let bound:=affine_inner_pointer_bound shape.
Let column:=affine_inner_pointer_column shape.
Let inner_bound:=affine_inner_pointer_inner_bound shape.
Let expression:=affine_inner_pointer_expression package.
Let header:=memory_affine_inner_pointer_header shape expression.
Let stable:=affine_snapshot_stable package(snapshot_root site)(snapshot_child site).
Let CERT:=affine_inner_pointer_syntax package.

Lemma affine_empty_snapshot_cached_header :
  snapshot_word_replace(single_snapshot_binding(snapshot_child site)(snapshot_child_cache site))
    (snapshot_original_header site)=memory_source_affine_code expression.
Proof.
  pose proof(affine_inner_pointer_outer_exact CERT)as EXACT.
  fold package shape in EXACT.
  assert(BODY:affine_inner_pointer_outer_body shape=
    affine_snapshot_body package(snapshot_word_replace(single_snapshot_binding(snapshot_child site)
      (snapshot_child_cache site))(snapshot_original_header site)))by exact(snapshot_cached_body_exact site).
  rewrite BODY in EXACT.
  pose proof(f_equal(@hd statement Sskip)EXACT)as FIRST.
  change(Sset inner_bound
    (snapshot_word_replace(single_snapshot_binding(snapshot_child site)(snapshot_child_cache site))
      (snapshot_original_header site))=Sset inner_bound(memory_source_affine_code expression))in FIRST.
  injection FIRST; trivial.
Qed.

Lemma affine_empty_snapshot_header_stable identifier : In identifier header -> In identifier stable.
Proof.
  intro MEMBER; unfold stable,affine_snapshot_stable,affine_prepared_stable,affine_prepared_body_stable.
  right; right; apply in_or_app; right.
  unfold memory_affine_inner_pointer_region_context,memory_affine_inner_pointer_parameters.
  apply in_or_app; left; apply in_or_app; left; exact MEMBER.
Qed.

Lemma affine_empty_snapshot_controls_private :
  ~In row stable /\ ~In column stable /\ ~In inner_bound stable.
Proof.
  assert(PROTECTED:forall id,In id stable -> id<>row /\ id<>column /\ id<>inner_bound).
  { exact(@affine_snapshot_protected(snapshot_cached_source site)package(snapshot_root site)(snapshot_child site)
      (snapshot_root_protected site)(snapshot_child_protected site)). }
  repeat split; intro MEMBER; specialize(PROTECTED _ MEMBER); tauto.
Qed.

Variable fe : genv->function->list val->mem->env->temp_env->mem->Prop.
Variable entry : clight_entry.
Let valuation:=memory_source_word_valuation(entry_temps entry).
Let count:=valuation bound.
Let upper i:=memory_source_affine_math(memory_source_set_valuation valuation row i)expression.
Let D:=affine_snapshot_original_domain package(snapshot_root site)(snapshot_child site)
  (snapshot_child_cache site)(snapshot_original_header site)fe entry.
Let HEAD:=memory_affine_inner_pointer_header_accept shape(affine_inner_pointer_row_limit package)entry=true.

Lemma affine_empty_snapshot_initial_headers : D -> HEAD ->
  (entry_temps entry)!row=Some(Vint Int.zero) /\ 0<count<=Int.max_signed /\
  forall id,In id header -> (entry_temps entry)!id=Some(Vint(Int.repr(valuation id))).
Proof.
  intros DOMAIN ACCEPT.
  destruct(@affine_snapshot_initial_words(snapshot_cached_source site)package(snapshot_root site)(snapshot_child site)
    (snapshot_child_cache site)(snapshot_original_header site)fe entry DOMAIN)as [ROW BOUND].
  assert(CAP:signed_range(affine_inner_pointer_row_limit package)).
  { pose proof(affine_inner_pointer_control_limits CERT)as CAPS; inversion CAPS; subst; tauto. }
  destruct(@memory_affine_inner_pointer_header_sound shape(affine_inner_pointer_row_limit package)entry
    CAP ROW BOUND ACCEPT)as [ZERO RANGE].
  destruct RANGE as [_ RANGE].
  change(0<Int.signed(temp_word bound(entry_temps entry))<=affine_inner_pointer_row_limit package)in RANGE.
  split; [exact ZERO|split].
  - unfold count,valuation; rewrite memory_source_word_temp; unfold signed_range in CAP; lia.
  - intros id MEMBER.
    destruct(@memory_source_typed_word header(memory_source_parameter_values header entry)(entry_temps entry)id
      (@affine_zero_snapshot_head_view original site fe entry DOMAIN ACCEPT)MEMBER)as [word LOOK].
    unfold valuation,memory_source_word_valuation; rewrite LOOK,Int.repr_signed; reflexivity.
Qed.

Lemma affine_empty_snapshot_root_value : D -> forall (i:Z) temps,
  temp_agree stable(entry_temps entry)temps ->
  eval_expr(entry_ge entry)(entry_env entry)temps(entry_memory entry)(signed_load(snapshot_root site))
    (Vint(Int.repr count)).
Proof.
  intros [ROOT REST]i temps FRAME.
  destruct(@cached_signed_current_read(snapshot_root site)bound stable entry temps(entry_memory entry)
    (or_intror(or_introl eq_refl))
    (@affine_zero_snapshot_root_cache_member(snapshot_cached_source site)package(snapshot_root site)(snapshot_child site))
    ROOT FRAME(cached_signed_initial_observations ROOT))as [word [CACHE READ]].
  destruct ROOT as [block[offset[initial[POINTER[LOOK LOAD]]]]].
  change((entry_temps entry)!bound=Some(Vint initial))in LOOK.
  assert(WORD:word=initial)by(rewrite FRAME in CACHE by
    exact(@affine_zero_snapshot_root_cache_member(snapshot_cached_source site)package(snapshot_root site)(snapshot_child site));
    congruence).
  subst word; unfold count,valuation,memory_source_word_valuation; rewrite LOOK,Int.repr_signed; exact READ.
Qed.

Lemma affine_empty_snapshot_child_value : D -> HEAD -> forall i temps,
  0<=i<count -> temps!row=Some(Vint(Int.repr i)) -> temp_agree stable(entry_temps entry)temps ->
  eval_expr(entry_ge entry)(entry_env entry)temps(entry_memory entry)(snapshot_original_header site)
    (Vint(Int.repr(upper i))).
Proof.
  intros DOMAIN ACCEPT i temps RANGE ROW FRAME.
  destruct(affine_empty_snapshot_initial_headers DOMAIN ACCEPT)as [ZERO[COUNT WORDS]].
  destruct DOMAIN as [ROOT[CHILD COMPLETE]].
  assert(ACTIVE:Int.lt(temp_word row(entry_temps entry))(temp_word bound(entry_temps entry))=true).
  { apply affine_snapshot_zero_active; [|exact ZERO|].
    - destruct ROOT as [block[offset[word[POINTER[CACHE READ]]]]]; exists word; exact CACHE.
    - rewrite <-memory_source_word_temp; exact(proj1 COUNT). }
  specialize(CHILD ACTIVE).
  apply(proj2(@snapshot_word_replacement_evaluation(snapshot_original_header site)(snapshot_header_word site)
    (single_snapshot_binding(snapshot_child site)(snapshot_child_cache site))
    (entry_ge entry)(entry_env entry)temps(entry_memory entry)(Vint(Int.repr(upper i)))
    (@single_snapshot_receipts(snapshot_original_header site)(snapshot_child site)(snapshot_child_cache site)
      stable entry temps(entry_memory entry)(or_introl eq_refl)(snapshot_cache_member site)CHILD FRAME
      (cached_signed_initial_observations CHILD)))).
  rewrite affine_empty_snapshot_cached_header; unfold upper.
  eapply memory_source_affine_iteration_value with(base:=entry_temps entry)(valuation:=valuation)(value:=i).
  - exact ROW.
  - intros id MEMBER; apply memory_source_affine_parameter_member in MEMBER.
    apply WORDS,memory_source_context_read; tauto.
  - eapply temp_agree_weaken; [|exact FRAME].
    intros id MEMBER; apply affine_empty_snapshot_header_stable,memory_source_context_read;
      apply memory_source_affine_parameter_member in MEMBER; tauto.
Qed.

Definition affine_empty_snapshot_exit:=PTree.set row(Vint(Int.repr count))
  (affine_empty_settle column inner_bound upper(count-1)(entry_temps entry)).

Theorem affine_empty_snapshot_source_complete : D -> HEAD ->
  affine_empty_snapshot_width_fact site entry ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)original E0
    affine_empty_snapshot_exit(entry_memory entry)Out_normal.
Proof.
  intros DOMAIN ACCEPT WIDTH.
  destruct(affine_empty_snapshot_initial_headers DOMAIN ACCEPT)as [ZERO[COUNT WORDS]].
  assert(ROOT:forall i temps,0<=i<=count ->temps!row=Some(Vint(Int.repr i)) ->
    temp_agree stable(entry_temps entry)temps ->
    eval_expr(entry_ge entry)(entry_env entry)temps(entry_memory entry)(signed_load(snapshot_root site))
      (Vint(Int.repr count))).
  { intros i temps I ROW FRAME; exact(@affine_empty_snapshot_root_value DOMAIN i temps FRAME). }
  assert(HEADER:forall i temps,0<=i<count ->temps!row=Some(Vint(Int.repr i)) ->
    temp_agree stable(entry_temps entry)temps ->
    eval_expr(entry_ge entry)(entry_env entry)temps(entry_memory entry)(snapshot_original_header site)
      (Vint(Int.repr(upper i)))).
  { exact(affine_empty_snapshot_child_value DOMAIN ACCEPT). }
  assert(EMPTY:forall i,0<=i<count ->Int.lt Int.zero(Int.repr(upper i))=false).
  { exact(@affine_empty_width_word_facts expression valuation row bound WIDTH). }
  pose proof(@affine_empty_loop_execution fe(entry_ge entry)(entry_env entry)(entry_memory entry)
    row column inner_bound(signed_load(snapshot_root site))(snapshot_original_header site)
    (affine_inner_pointer_body shape)stable(entry_temps entry)upper count
    (conj(affine_inner_pointer_rc CERT)(conj(affine_inner_pointer_rk CERT)(affine_inner_pointer_ck CERT)))
    affine_empty_snapshot_controls_private eq_refl ltac:(lia)ROOT HEADER EMPTY
    (Z.to_nat count)0(entry_temps entry)ltac:(rewrite Z2Nat.id; lia)ltac:(lia)ZERO(temp_agree_refl _ _))as RUN.
  rewrite(snapshot_source_exact site); change(exec_stmt fe(entry_ge entry)(entry_env entry)
    (entry_temps entry)(entry_memory entry)(affine_setup_source row
    (signed_load(snapshot_root site))column inner_bound(snapshot_original_header site)(affine_inner_pointer_body shape))
    E0 affine_empty_snapshot_exit(entry_memory entry)Out_normal).
  remember(Z.to_nat count)as n eqn:NAT; destruct n as [|n];
    [pose proof(Z2Nat.id count ltac:(lia)); rewrite <-NAT in H; cbn in H; lia|].
  rewrite affine_empty_counter_exit in RUN by
    (first[exact(affine_inner_pointer_rc CERT)|exact(affine_inner_pointer_rk CERT)|exact(affine_inner_pointer_ck CERT)]).
  assert(SIZE:Z.of_nat(S n)=count)by(rewrite NAT; apply Z2Nat.id; lia).
  assert(LAST:Z.of_nat n=count-1)by(rewrite Nat2Z.inj_succ in SIZE; lia).
  cbn [Z.add]in RUN; rewrite SIZE,LAST in RUN; exact RUN.
Qed.

Theorem affine_empty_snapshot_source_exit after final : D -> HEAD ->
  affine_empty_snapshot_width_fact site entry ->
  exec_stmt fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)original E0
    after final Out_normal -> after=affine_empty_snapshot_exit /\ final=entry_memory entry.
Proof.
  intros DOMAIN ACCEPT WIDTH RUN.
  assert(QUIET:quiet_statement original=true).
  { rewrite(snapshot_source_exact site); unfold affine_snapshot_source,affine_snapshot_body,affine_setup_child;
    cbn [strict_frontend_loop quiet_statement rectangle_reset frontend_counted_loop counter_increment].
    fold package shape.
    pose proof(@memory_pointer_sequence_quiet _ _ (affine_inner_pointer_body_exact CERT))as LEAF.
    fold package shape in LEAF; rewrite LEAF; reflexivity. }
  pose proof(@quiet_execution_determinate fe(entry_ge entry)(entry_env entry)(entry_temps entry)(entry_memory entry)
    original E0 after final Out_normal RUN QUIET E0 affine_empty_snapshot_exit(entry_memory entry)Out_normal
    (affine_empty_snapshot_source_complete DOMAIN ACCEPT WIDTH))as [TRACE[TEMPS[MEMORY OUT]]].
  split; assumption.
Qed.
End SOURCE.

Print Assumptions affine_empty_snapshot_cached_header.
Print Assumptions affine_empty_snapshot_initial_headers.
Print Assumptions affine_empty_snapshot_child_value.
Print Assumptions affine_empty_snapshot_source_complete.
Print Assumptions affine_empty_snapshot_source_exit.
