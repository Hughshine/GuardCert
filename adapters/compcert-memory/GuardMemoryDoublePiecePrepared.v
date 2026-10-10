From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From polcert.polygen Require Import Result.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral
  GuardMemoryDoubleTreePrepared GuardMemoryDoubleRetainedPhase
  GuardMemoryDoublePieceExecution GuardMemoryDoublePieceModel GuardMemoryDoublePieceLoops.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition double_piece_groups := list (list DoublePieceSequence.Single.piece_item).
Definition double_piece_coverage := list DoublePieceSequence.Single.S.F.D.cover_witness.
Definition double_piece_proposal := (double_piece_groups*double_piece_coverage)%type.

(** The proposer returns only data. The actual source and candidate are
    extracted inside this checker. Parameter facts come from the proved Loop
    guard/extractor encoding, including the reversal of the parameter vector. *)
Definition checked_double_piece_prepared_loop phase
  (adapt : list (Z*Z) -> DBL.t -> DBL.t -> result DBL.t)
  (propose : DoubleAssignmentIRs.PolyLang.t -> DoubleAssignmentIRs.PolyLang.t -> option double_piece_proposal)
  intervals (source : DBL.t) :=
  let '(body,context,vars) := source in
  match DoubleAssignmentExtractor.extractor (double_tree_assumed_loop intervals body,context,vars) with
  | Err _=>pure None
  | Okk before=>
    BIND retained <- checked_double_retained_phase phase before -;
    match retained with
    | None=>pure None
    | Some (raw,model,_)=>match adapt intervals source raw with
      | Err _=>pure None
      | Okk candidate=>
        let candidate_body := fst (fst candidate) in
        match DoubleAssignmentExtractor.extractor
          (double_tree_assumed_loop intervals candidate_body,context,vars) with
        | Err _=>pure None
        | Okk after=>match propose model after with
          | None=>pure None
          | Some (groups,coverage)=>
            BIND accepted <- check_double_piece_model [] model after groups coverage -;
            if accepted then pure (Some (candidate_body,context,vars)) else pure None
          end
        end
      end
    end
  end.

Theorem checked_double_piece_prepared_loop_at phase adapt propose intervals source generated
  parameters initial final :
  mayReturn (checked_double_piece_prepared_loop phase adapt propose intervals source) (Some generated) ->
  length (snd (fst source))=length parameters -> DoubleAssignmentInstr.NonAlias initial ->
  Forall2 (fun interval value=>fst interval<=value<=snd interval) intervals parameters ->
  DBL.loop_semantics (fst (fst source)) parameters initial final ->
  DBL.loop_semantics (fst (fst generated)) parameters initial final.
Proof.
  destruct source as [[body context] vars].
  intros RUN LENGTH NONALIAS RANGES SOURCE.
  unfold checked_double_piece_prepared_loop in RUN.
  destruct (DoubleAssignmentExtractor.extractor (double_tree_assumed_loop intervals body,context,vars))
    as [before|message] eqn:EXTRACT_SOURCE; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN retained PHASE.
  destruct retained as [[[raw model] witnesses]|]; [|apply mayReturn_pure in RUN; discriminate].
  destruct (adapt intervals (body,context,vars) raw) as [[[candidate candidate_context] candidate_vars]|message];
    [|apply mayReturn_pure in RUN; discriminate].
  cbn [fst snd] in RUN.
  destruct (DoubleAssignmentExtractor.extractor (double_tree_assumed_loop intervals candidate,context,vars))
    as [after|message] eqn:EXTRACT_CANDIDATE; [|apply mayReturn_pure in RUN; discriminate].
  destruct (propose model after) as [[groups coverage]|]; [|apply mayReturn_pure in RUN; discriminate].
  bind_imp_destruct RUN accepted CHECK; destruct accepted; [|apply mayReturn_pure in RUN; discriminate].
  apply mayReturn_pure in RUN; inversion RUN; subst generated; cbn [fst snd] in *.
  destruct (@DoubleAssignmentExtractor.extractor_success_inv _ _ _ _ EXTRACT_SOURCE)
    as [source_instructions [_ [_ SOURCE_PROGRAM]]].
  destruct (@DoubleAssignmentExtractor.extractor_success_inv _ _ _ _ EXTRACT_CANDIDATE)
    as [candidate_instructions [_ [_ CANDIDATE_PROGRAM]]].
  subst before after.
  assert (GUARDED_SOURCE : DBL.loop_semantics (double_tree_assumed_loop intervals body) parameters initial final).
  { apply (proj2 (@double_tree_assumed_execution intervals parameters initial final body RANGES)); exact SOURCE. }
  pose proof (@checked_double_piece_actual_loops_forward_at phase []
    (double_tree_assumed_loop intervals body) (double_tree_assumed_loop intervals candidate) context vars
    source_instructions candidate_instructions raw model witnesses groups coverage
    (rev parameters) initial final EXTRACT_SOURCE EXTRACT_CANDIDATE PHASE CHECK
    ltac:(rewrite length_rev; symmetry; exact LENGTH) ltac:(constructor) eq_refl NONALIAS
    ltac:(rewrite rev_involutive; exact GUARDED_SOURCE)) as TARGET.
  rewrite rev_involutive in TARGET.
  apply (proj1 (@double_tree_assumed_execution intervals parameters initial final candidate RANGES)); exact TARGET.
Qed.
Print Assumptions checked_double_piece_prepared_loop_at.
