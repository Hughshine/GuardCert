From Stdlib Require Import List Bool.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep Ctypes Cop.
From Guard Require Import ClightCondition ClightGuard ClightTempFrame CompCertMemoryEquivalence StatefulGuard ClightTempFootprint ClightProjectedExecution.
From GuardMemory Require Import GuardMemoryStatefulLanguage.
Set Implicit Arguments.
Definition affine_flag_test := (statement*expr)%type.
Definition affine_flag_test_run fe (test:affine_flag_test) s accepted checked :=
  exists after value,
    exec_stmt fe (entry_ge s)(entry_env s)(entry_temps s)(entry_memory s)(fst test) E0 after (entry_memory s) Out_normal /\
    eval_expr (entry_ge s)(entry_env s) after (entry_memory s)(snd test) value /\
    bool_val value (typeof(snd test))(entry_memory s)=Some accepted /\
    checked=Entry(entry_ge s)(entry_env s) after(entry_memory s).
Definition affine_flag_conditional (test:affine_flag_test) yes no :=
  Ssequence(fst test)(Sifthenelse(snd test) yes no).
Definition affine_flag_language
  (fe:genv->function->list val->mem->env->temp_env->mem->Prop) (ge:genv) (live:list ident) : stateful_language clight_entry.
Proof.
  refine {| stateful_command:=statement; stateful_test:=affine_flag_test;
    stateful_observation:=memory_stateful_observation;
    stateful_command_run:=fun code s observed=>entry_ge s=ge /\ memory_stateful_command_run fe live code s observed;
    stateful_test_run:=affine_flag_test_run fe; stateful_conditional:=affine_flag_conditional |}.
  intros [check condition] yes no s observed accepted checked [middle [value [CHECK [EVAL [BOOL ->]]]]]
    [GLOBAL [after [final [RUN [FRAME MEMORY]]]]].
  split; [exact GLOBAL|]; exists after,final; split; [|exact(conj FRAME MEMORY)].
  destruct s as[globals locals temps memory]; cbn in *.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [exact CHECK|].
  eapply exec_Sifthenelse with(v1:=value)(b:=accepted); eassumption.
Defined.
Print Assumptions affine_flag_language.

Theorem affine_flag_guard_preservation fe ge live domain presumption source candidate writes
  (encoding:projected_guard_encoding(affine_flag_language fe ge live) domain presumption(memory_stateful_public_frame live)) :
  statement_scope live source -> writes_only writes source ->
  (forall s observed, stateful_command_run(affine_flag_language fe ge live) source s observed -> domain s) ->
  (forall checked observed, presumption checked ->
    stateful_command_run(affine_flag_language fe ge live) source checked observed ->
    stateful_command_run(affine_flag_language fe ge live) candidate checked observed) ->
  forall s observed, stateful_command_run(affine_flag_language fe ge live) source s observed ->
    stateful_command_run(affine_flag_language fe ge live)
      (stateful_conditional(affine_flag_language fe ge live)(projected_guard_test encoding) candidate source) s observed.
Proof.
  intros SCOPE WRITES DOMAIN LOCAL.
  apply stateful_guard_preservation; [exact DOMAIN| |exact LOCAL].
  intros state checked observed [GE [ENV [MEM FRAME]]] [GLOBAL [after [final [RUN [PUBLIC MEMORY]]]]].
  destruct state as[globals locals temps memory],checked as[next_ge next_locals next_temps next_memory];
    cbn in GE,ENV,MEM,FRAME,GLOBAL,RUN,PUBLIC,MEMORY |- *; subst next_ge next_locals next_memory.
  split; [exact GLOBAL|].
  destruct(@structured_execution_temp_transport fe globals locals temps memory source E0 after final Out_normal
    RUN live next_temps writes WRITES SCOPE FRAME) as[next [EXEC AGREE]].
  exists next,final; split; [exact EXEC|split; [eapply temp_agree_trans; eassumption|exact MEMORY]].
Qed.
Print Assumptions affine_flag_guard_preservation.
