From compcert.common Require Import Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightFrontendRegion.
From GuardInterface Require Import ClightStrictLoopProgress ClightLoopBodyTransport.
Set Implicit Arguments.

Definition statement_execution_equivalent first second := forall fe ge locals temps memory trace after final outcome,
  exec_stmt fe ge locals temps memory first trace after final outcome <->
  exec_stmt fe ge locals temps memory second trace after final outcome.

Lemma statement_skip_prefix_equivalent code : statement_execution_equivalent(Ssequence Sskip code)code.
Proof.
  intros fe ge locals temps memory trace after final outcome; split; [apply skip_prefix_exec|intro RUN].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=trace); [constructor|exact RUN].
Qed.

Lemma statement_sequence_equivalent first second next last :
  statement_execution_equivalent first second -> statement_execution_equivalent next last ->
  statement_execution_equivalent(Ssequence first next)(Ssequence second last).
Proof.
  intros FIRST NEXT fe ge locals temps memory trace after final outcome; split; intro RUN; inversion RUN; subst.
  - eapply exec_Sseq_1; [apply(proj1(FIRST _ _ _ _ _ _ _ _ _))|apply(proj1(NEXT _ _ _ _ _ _ _ _ _))]; eassumption.
  - eapply exec_Sseq_2; [apply(proj1(FIRST _ _ _ _ _ _ _ _ _)); eassumption|assumption].
  - eapply exec_Sseq_1; [apply(proj2(FIRST _ _ _ _ _ _ _ _ _))|apply(proj2(NEXT _ _ _ _ _ _ _ _ _))]; eassumption.
  - eapply exec_Sseq_2; [apply(proj2(FIRST _ _ _ _ _ _ _ _ _)); eassumption|assumption].
Qed.

Lemma statement_strict_body_equivalent iterator condition first second :
  statement_execution_equivalent first second ->
  statement_execution_equivalent(strict_frontend_loop iterator condition first)(strict_frontend_loop iterator condition second).
Proof.
  intros BODY fe ge locals temps memory trace after final outcome; split; intro RUN.
  - exact(proj1(@strict_loop_body_transport fe ge locals iterator condition first second(fun _ _=>True)
      (fun le m tr after last out _ SOURCE=>conj(proj1(BODY _ _ _ _ _ _ _ _ _) SOURCE)I)
      (fun _ _ _ _ _ _ _ _=>I) _ _ _ _ _ _ RUN I)).
  - exact(proj1(@strict_loop_body_transport fe ge locals iterator condition second first(fun _ _=>True)
      (fun le m tr after last out _ SOURCE=>conj(proj2(BODY _ _ _ _ _ _ _ _ _) SOURCE)I)
      (fun _ _ _ _ _ _ _ _=>I) _ _ _ _ _ _ RUN I)).
Qed.

Print Assumptions statement_skip_prefix_equivalent.
Print Assumptions statement_sequence_equivalent.
Print Assumptions statement_strict_body_equivalent.
