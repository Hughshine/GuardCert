(** A Clight condition service above the semantic kernel.  Its proof is supplied
    once by the service author; ordinary source/candidate proposers do not supply
    an execution callback.  Private temporaries may change. *)
From Stdlib Require Import List Bool.
From compcert.lib Require Import Maps.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint.
From GuardInterface Require Import ClightStagedCheck.
From GuardMemory Require Import GuardMemoryBooleanScan.
Import ListNotations.
Set Implicit Arguments.

Record source_licensed_scan (source : statement) (ports public : list ident)
    (ready accepted_fact : clight_entry -> Prop) : Type := {
  licensed_scan_statement : statement;
  licensed_scan_result : ident;
  licensed_scan_execution : forall fe ge locals original current memory source_after final,
    exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
    ready (Entry ge locals original memory) ->
    temp_agree ports original current ->
    exists checked answer,
      exec_stmt fe ge locals current memory licensed_scan_statement E0 checked memory Out_normal /\
      temp_agree (statement_temps source++public) current checked /\
      temp_agree ports current checked /\
      checked!licensed_scan_result = Some (memory_boolean_word answer) /\
      (answer=true -> accepted_fact (Entry ge locals original memory))
}.

(** Local choice consumes the scan boundary and transformation-specific branch
    proofs.  Context installation and source progress are separate host duties. *)
Theorem licensed_scan_choice_execution source ports public ready accepted_fact
    (scan : source_licensed_scan source ports public ready accepted_fact)
    fe ge locals original current memory source_after final yes no outcome
    (post : temp_env -> Prop) :
  exec_stmt fe ge locals original memory source E0 source_after final Out_normal ->
  ready (Entry ge locals original memory) -> temp_agree ports original current ->
  (forall checked answer,
    temp_agree (statement_temps source++public) current checked ->
    temp_agree ports current checked ->
    (answer=true -> accepted_fact (Entry ge locals original memory)) ->
    exists after, exec_stmt fe ge locals checked memory (if answer then yes else no)
      E0 after final outcome /\ post after) ->
  exists after,
    exec_stmt fe ge locals current memory
      (Ssequence (licensed_scan_statement scan)
        (Sifthenelse (ClightSharedGuard.shared_guard_choice (licensed_scan_result scan)) yes no))
      E0 after final outcome /\ post after.
Proof.
  intros SOURCE READY PORTS BRANCH.
  destruct (licensed_scan_execution scan SOURCE READY PORTS)
    as [checked [answer [RUN [PUBLIC [FRAME [FLAG FACT]]]]]].
  destruct (BRANCH checked answer PUBLIC FRAME FACT) as [after [NEXT POST]].
  exists after; split; [|exact POST].
  eapply check_result_gate_execution; [exact RUN|exact FLAG|exact NEXT].
Qed.

Print Assumptions licensed_scan_choice_execution.
