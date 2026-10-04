From Stdlib Require Import List Bool.
From compcert.common Require Import AST Events Memory.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightGuard ClightCondition ClightPrivateRegion.
From GuardMemory Require Import GuardMemorySequentialCondition GuardMemoryProjectedCondition.
Set Implicit Arguments.

Fixpoint memory_check_tree_parse (code : statement) : option decision_tree :=
  match code with
  | Sskip => Some (Decision true)
  | Sbreak => Some (Decision false)
  | Sifthenelse condition first second =>
      match memory_check_tree_parse first,memory_check_tree_parse second with
      | Some left_tree,Some right_tree => Some (Test condition left_tree right_tree)
      | _,_ => None end
  | _ => None end.

Lemma memory_check_tree_parse_sound code tree :
  memory_check_tree_parse code = Some tree -> code = tree_statement tree Sskip Sbreak.
Proof.
  revert tree; induction code; intros tree PARSE; cbn in PARSE; try discriminate.
  - inversion PARSE; reflexivity.
  - destruct (memory_check_tree_parse code1) as [left|] eqn:LEFT;
      destruct (memory_check_tree_parse code2) as [right|] eqn:RIGHT; try discriminate.
    inversion PARSE; subst tree; cbn; rewrite (IHcode1 left eq_refl),(IHcode2 right eq_refl); reflexivity.
  - inversion PARSE; reflexivity.
Qed.

Lemma memory_check_tree_decode fe ge locals temps memory tree :
  forall trace after final out,
  exec_stmt fe ge locals temps memory (tree_statement tree Sskip Sbreak) trace after final out ->
  exists accepted, after=temps /\ final=memory /\ trace=E0 /\
    out=memory_check_outcome accepted /\ decision_run (Entry ge locals temps memory) tree accepted.
Proof.
  induction tree as [accepted|condition first LEFT second RIGHT]; intros trace after final out RUN.
  - destruct accepted; cbn in RUN; inversion RUN; subst.
    + exists true; repeat split; constructor.
    + exists false; repeat split; constructor.
  - cbn in RUN; inversion RUN; subst.
    match goal with
    | BODY : exec_stmt _ _ _ _ _ (if ?b then _ else _) _ _ _ _ |- _ => destruct b; cbn in BODY
    end.
    + match goal with BODY : exec_stmt _ _ _ _ _ (tree_statement first Sskip Sbreak) _ _ _ _ |- _ =>
        destruct (LEFT _ _ _ _ BODY) as [accepted [TEMPS [MEMORY [TRACE [OUT SELECTED]]]]]
      end.
      subst after final trace out; exists accepted; repeat split; try reflexivity.
      eapply run_test with (b:=true); [eexists; split; eassumption|exact SELECTED].
    + match goal with BODY : exec_stmt _ _ _ _ _ (tree_statement second Sskip Sbreak) _ _ _ _ |- _ =>
        destruct (RIGHT _ _ _ _ BODY) as [accepted [TEMPS [MEMORY [TRACE [OUT SELECTED]]]]]
      end.
      subst after final trace out; exists accepted; repeat split; try reflexivity.
      eapply run_test with (b:=false); [eexists; split; eassumption|exact SELECTED].
Qed.
Print Assumptions memory_check_tree_decode.

Lemma memory_projected_tree_prefix fe state live header rest tree accepted checked :
  memory_check_tree_parse header = Some tree ->
  memory_projected_check_execution fe state live (Ssequence header rest) accepted checked ->
  exists result, memory_projected_check_execution fe state live header result (entry_temps state).
Proof.
  intros PARSE [EXEC FRAME]; pose proof (@memory_check_tree_parse_sound header tree PARSE) as SAME.
  destruct state as [ge locals temps memory]; cbn in EXEC |- *.
  rewrite SAME in EXEC; inversion EXEC; subst.
  all: match goal with
  | HEAD : exec_stmt ?entry ?globals ?environment ?registers ?heap
      (tree_statement ?prefix Sskip Sbreak) ?trace ?after ?final ?out |- _ =>
      destruct (@memory_check_tree_decode entry globals environment registers heap prefix trace after final out HEAD)
        as [result [_ [_ [_ [_ SELECTED]]]]]
  end.
  all: exists result; apply memory_projected_check_from_exact;
    apply memory_decision_check_statement; exact SELECTED.
Qed.
Print Assumptions memory_projected_tree_prefix.
