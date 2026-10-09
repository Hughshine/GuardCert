From Stdlib Require Import Bool List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightTempFrame ClightTempFootprint ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl GuardMemoryDoubleMatmulNest
  GuardMemoryDoubleMatmulHeaderLicense GuardMemoryLongCapturePath.
From GuardInterface Require Import ClightCheckPlanFrame.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Record double_matmul_captures := DoubleMatmulCaptures {
  matmul_capture_M : ident; matmul_capture_N : ident; matmul_capture_K : ident; matmul_capture_flag : ident
}.
Definition double_matmul_capture_slots captures m_bound n_bound k_bound :=
  [LongCaptureSlot m_bound (matmul_capture_M captures);
   LongCaptureSlot n_bound (matmul_capture_N captures);
   LongCaptureSlot k_bound (matmul_capture_K captures)].
Definition double_matmul_capture_code captures m_bound n_bound k_bound limit :=
  long_capture_path (double_matmul_capture_slots captures m_bound n_bound k_bound)
    (matmul_capture_flag captures) limit.
Definition double_matmul_capture_ids captures :=
  [matmul_capture_flag captures;matmul_capture_M captures;matmul_capture_N captures;matmul_capture_K captures].

Lemma matmul_capture_binding_unique ge locals header first second :
  double_global_binding ge locals header first -> double_global_binding ge locals header second -> first=second.
Proof. intros [_ FIRST] [_ SECOND]; congruence. Qed.

Theorem double_matmul_capture_license ge locals memory captures m_bound n_bound k_bound m_block n_block k_block :
  double_global_binding ge locals m_bound m_block -> double_global_binding ge locals n_bound n_block ->
  double_global_binding ge locals k_bound k_block -> double_matmul_headers_licensed m_block n_block k_block memory ->
  long_capture_path_license ge locals memory (double_matmul_capture_slots captures m_bound n_bound k_bound).
Proof.
  intros MB NB KB [m_word [MLOAD NEXT]].
  exists m_block,m_word; split; [exact MB|split; [exact MLOAD|intro MPOS]].
  destruct (NEXT MPOS) as [n_word [NLOAD LAST]].
  exists n_block,n_word; split; [exact NB|split; [exact NLOAD|intro NPOS]].
  destruct (LAST NPOS) as [k_word KLOAD].
  exists k_block,k_word; split; [exact KB|split; [exact KLOAD|intros; exact I]].
Qed.

Theorem double_matmul_capture_accepted ge locals memory captures m_bound n_bound k_bound
  m_block n_block k_block limit temps :
  double_global_binding ge locals m_bound m_block -> double_global_binding ge locals n_bound n_block ->
  double_global_binding ge locals k_bound k_block ->
  long_capture_acceptance ge locals memory (double_matmul_capture_slots captures m_bound n_bound k_bound) limit temps ->
  exists rows columns depth,
    Z.of_nat rows <= limit /\ Z.of_nat columns <= limit /\ Z.of_nat depth <= limit /\
    temps ! (matmul_capture_M captures)=Some (Vint (Int.repr (Z.of_nat rows))) /\
    temps ! (matmul_capture_N captures)=Some (Vint (Int.repr (Z.of_nat columns))) /\
    temps ! (matmul_capture_K captures)=Some (Vint (Int.repr (Z.of_nat depth))) /\
    matmul_nest_invariant m_block n_block k_block rows columns depth temps memory.
Proof.
  intros MB NB KB [values [CACHES [BOUNDS ENTRY]]].
  pose proof (Forall2_length CACHES) as LENGTH.
  destruct values as [|m [|n [|k [|extra tail]]]]; cbn in LENGTH; try discriminate.
  inversion CACHES as [|sm vm ss vs MCACHE NCACHES]; subst.
  inversion NCACHES as [|sn vn ns nv NCACHE KCACHES]; subst.
  inversion KCACHES as [|sk vk ks kv KCACHE DONE]; subst.
  pose proof (Forall_inv BOUNDS) as MRANGE.
  pose proof (Forall_inv (Forall_inv_tail BOUNDS)) as NRANGE.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail BOUNDS))) as KRANGE.
  assert (MZ : Z.of_nat (Z.to_nat m)=m) by (apply Z2Nat.id; exact (proj1 MRANGE)).
  assert (NZ : Z.of_nat (Z.to_nat n)=n) by (apply Z2Nat.id; exact (proj1 NRANGE)).
  assert (KZ : Z.of_nat (Z.to_nat k)=k) by (apply Z2Nat.id; exact (proj1 KRANGE)).
  exists (Z.to_nat m), (Z.to_nat n), (Z.to_nat k).
  rewrite MZ, NZ, KZ.
  split; [exact (proj2 MRANGE)|split; [exact (proj2 NRANGE)|split; [exact (proj2 KRANGE)|
    split; [exact MCACHE|split; [exact NCACHE|split; [exact KCACHE|]]]]]].
  destruct ENTRY as [m_actual [MA [MLOAD NEXT]]].
  pose proof (matmul_capture_binding_unique MB MA) as M; subst m_actual.
  unfold matmul_nest_invariant; rewrite MZ, NZ, KZ.
  split; [exact MLOAD|split].
  - intro MPOS; destruct (NEXT MPOS) as [n_actual [NA [NLOAD _]]].
    pose proof (matmul_capture_binding_unique NB NA) as N; subst n_actual; exact NLOAD.
  - intros MPOS NPOS; destruct (NEXT MPOS) as [n_actual [NA [NLOAD LAST]]].
    destruct (LAST NPOS) as [k_actual [KA [KLOAD _]]].
    pose proof (matmul_capture_binding_unique KB KA) as K; subst k_actual; exact KLOAD.
Qed.

Theorem double_matmul_source_capture fe ge locals temps memory site captures m_bound n_bound k_bound
  m_block n_block k_block limit source_after source_final :
  double_global_binding ge locals m_bound m_block -> double_global_binding ge locals n_bound n_block ->
  double_global_binding ge locals k_bound k_block -> 0<=limit<=Int.max_signed ->
  NoDup [matmul_capture_M captures;matmul_capture_N captures;matmul_capture_K captures] ->
  ~ In (matmul_capture_flag captures) [matmul_capture_M captures;matmul_capture_N captures;matmul_capture_K captures] ->
  exec_stmt fe ge locals temps memory (double_matmul_source_nest site m_bound n_bound k_bound)
    E0 source_after source_final Out_normal ->
  exists (accepted : bool) prepared,
    exec_stmt fe ge locals temps memory (double_matmul_capture_code captures m_bound n_bound k_bound limit)
      E0 prepared memory Out_normal /\
    prepared ! (matmul_capture_flag captures)=Some (Vint (if accepted then Int.one else Int.zero)) /\
    (accepted=true -> exists rows columns depth,
      Z.of_nat rows<=limit /\ Z.of_nat columns<=limit /\ Z.of_nat depth<=limit /\
      prepared ! (matmul_capture_M captures)=Some (Vint (Int.repr (Z.of_nat rows))) /\
      prepared ! (matmul_capture_N captures)=Some (Vint (Int.repr (Z.of_nat columns))) /\
      prepared ! (matmul_capture_K captures)=Some (Vint (Int.repr (Z.of_nat depth))) /\
      matmul_nest_invariant m_block n_block k_block rows columns depth prepared memory).
Proof.
  intros MB NB KB LIMIT DISTINCT PRIVATE SOURCE.
  pose proof (double_matmul_source_headers_licensed MB NB KB SOURCE) as LICENSE.
  pose proof (@double_matmul_capture_license ge locals memory captures m_bound n_bound k_bound
    m_block n_block k_block MB NB KB LICENSE) as PATH.
  destruct (@long_capture_path_execution fe ge locals memory
    (double_matmul_capture_slots captures m_bound n_bound k_bound) (matmul_capture_flag captures) limit temps
    LIMIT DISTINCT PRIVATE PATH) as [accepted [prepared [RUN [FLAG FACTS]]]].
  exists accepted, prepared; split; [exact RUN|split; [exact FLAG|intro TRUE]].
  eapply double_matmul_capture_accepted; eauto.
Qed.

Theorem double_matmul_capture_public_frame fe ge locals temps memory captures m_bound n_bound k_bound
  limit live trace after final outcome :
  (forall id, In id live -> ~ In id (double_matmul_capture_ids captures)) ->
  exec_stmt fe ge locals temps memory (double_matmul_capture_code captures m_bound n_bound k_bound limit)
    trace after final outcome -> temp_agree live temps after.
Proof.
  intros PRIVATE RUN; eapply structured_temp_frame with (allowed:=double_matmul_capture_ids captures).
  - exact (long_capture_path_writes (double_matmul_capture_slots captures m_bound n_bound k_bound)
      (matmul_capture_flag captures) limit).
  - exact PRIVATE.
  - exact RUN.
Qed.

Theorem double_matmul_capture_source_transport fe ge locals temps memory site captures m_bound n_bound k_bound
  limit live prepared source_after source_final :
  (forall id, In id (statement_temps (double_matmul_source_nest site m_bound n_bound k_bound)++live) ->
    ~ In id (double_matmul_capture_ids captures)) ->
  exec_stmt fe ge locals temps memory (double_matmul_capture_code captures m_bound n_bound k_bound limit)
    E0 prepared memory Out_normal ->
  exec_stmt fe ge locals temps memory (double_matmul_source_nest site m_bound n_bound k_bound)
    E0 source_after source_final Out_normal ->
  exists prepared_after,
    exec_stmt fe ge locals prepared memory (double_matmul_source_nest site m_bound n_bound k_bound)
      E0 prepared_after source_final Out_normal /\ temp_agree live source_after prepared_after.
Proof.
  intros PRIVATE CAPTURE SOURCE.
  pose (code := double_matmul_source_nest site m_bound n_bound k_bound).
  pose (scope := statement_temps code ++ live).
  assert (FRAME : temp_agree scope temps prepared) by (eapply double_matmul_capture_public_frame; eauto).
  assert (FRAMEABLE : check_plan_frameable code=true) by reflexivity.
  destruct (@structured_execution_temp_transport fe ge locals temps memory code E0 source_after source_final
    Out_normal SOURCE scope prepared (statement_temps code) (@check_plan_frameable_writes code FRAMEABLE)
    ltac:(unfold statement_scope,scope; intros id IN; apply in_or_app; left; exact IN) FRAME)
    as [prepared_after [RUN PUBLIC]].
  exists prepared_after; split; [exact RUN|].
  eapply temp_agree_weaken; [intros id IN; apply in_or_app; right; exact IN|exact PUBLIC].
Qed.

Print Assumptions double_matmul_capture_license.
Print Assumptions double_matmul_capture_accepted.
Print Assumptions double_matmul_source_capture.
Print Assumptions double_matmul_capture_public_frame.
Print Assumptions double_matmul_capture_source_transport.
