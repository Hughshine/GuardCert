From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From GuardInterface Require Import CompCertWordObservation.
Import ListNotations.
Set Implicit Arguments.

(** This language service classifies actual structured control, including
    finite loop executions. It makes no termination or binding-frame claim. *)
Fixpoint check_constant_word_control (word : int) (code : statement) : bool :=
  match code with
  | Ssequence first second | Sloop first second =>
      check_constant_word_control word first && check_constant_word_control word second
  | Sifthenelse _ yes no =>
      check_constant_word_control word yes && check_constant_word_control word no
  | Sbreak | Scontinue => true
  | _ => check_constant_word_statement word code
  end.

Theorem check_constant_word_statement_control word code :
  check_constant_word_statement word code = true ->
  check_constant_word_control word code = true.
Proof.
  induction code; cbn [check_constant_word_statement check_constant_word_control];
    intro CHECK; try discriminate; try exact CHECK.
  all: apply andb_true_iff in CHECK as [FIRST SECOND];
    rewrite (IHcode1 FIRST), (IHcode2 SECOND); reflexivity.
Qed.

Theorem checked_constant_word_control_execution word
  fe ge locals before memory code trace after final outcome :
  exec_stmt fe ge locals before memory code trace after final outcome ->
  check_constant_word_control word code = true ->
  constant_word_stores word memory final.
Proof.
  intro RUN; induction RUN; cbn [check_constant_word_control]; intro CHECK;
    try discriminate;
    try solve [constructor];
    try solve [eapply constant_word_statement_execution with (fe:=fe);
      [eapply check_constant_word_statement_sound; exact CHECK|econstructor; eassumption]].
  all: try (apply andb_true_iff in CHECK as [FIRST SECOND]).
  all: try solve [eauto using constant_word_stores_trans].
  - destruct b; cbn in *; eauto.
  - eapply constant_word_stores_trans; [apply IHRUN1; exact FIRST|].
    eapply constant_word_stores_trans; [apply IHRUN2; exact SECOND|].
    apply IHRUN3; cbn [check_constant_word_control]; rewrite FIRST, SECOND; reflexivity.
Qed.

Theorem checked_constant_word_control_preserves_observation word
  fe ge locals before memory code trace after final outcome block offset :
  check_constant_word_control word code = true ->
  Mem.load Mint32 memory block offset = Some (Vint word) ->
  exec_stmt fe ge locals before memory code trace after final outcome ->
  Mem.load Mint32 final block offset = Some (Vint word).
Proof.
  intros CHECK LOAD RUN; eapply constant_word_stores_preserve_observation; [|exact LOAD].
  eapply checked_constant_word_control_execution; eassumption.
Qed.

Print Assumptions check_constant_word_statement_control.
Print Assumptions checked_constant_word_control_execution.
Print Assumptions checked_constant_word_control_preserves_observation.
