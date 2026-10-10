From Stdlib Require Import List Bool ZArith Lia.
From polcert.lib Require Import Linalg ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardMemory Require Import GuardMemoryDoublePieceExecution GuardMemoryDoublePieceParameterDomains
  GuardMemoryDoubleAssignment GuardMemoryDoublePolyhedral.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Check actual source/candidate models under established parameter facts.
    Groups and coverage witnesses are untrusted data. This is a model-level
    conditional equivalence, not a Loop or whole-program installation theorem. *)
Definition check_double_piece_model guards source candidate groups witnesses :=
  let '((sources,context),variables) := source in
  let '((candidates,target_context),target_variables) := candidate in
  let count := List.length context in
  if Nat.eqb count (List.length target_context) then
    let restricted_sources := DoublePieceParameterDomains.piece_restrict_program count guards sources in
    let restricted_candidates := DoublePieceParameterDomains.piece_restrict_program count guards candidates in
    BIND pieces <- DoublePieceSequence.check_sequence_families count restricted_sources groups witnesses -;
    if pieces then validate_double_equivalence
      (DoublePieceSequence.sequence_target restricted_sources groups,context,variables)
      (restricted_candidates,target_context,target_variables)
    else pure false
  else pure false.
Theorem checked_double_piece_model_equivalence_at guards source candidate groups witnesses parameters initial final :
  List.length (snd (fst source))=List.length parameters ->
  Forall (fun row=>(List.length (fst row)<=List.length parameters)%nat) guards ->
  in_poly parameters guards=true -> DoubleAssignmentInstr.NonAlias initial ->
  mayReturn (check_double_piece_model guards source candidate groups witnesses) true ->
  (DoubleAssignmentIRs.PolyLang.poly_instance_list_semantics parameters source initial final <->
   DoubleAssignmentIRs.PolyLang.poly_instance_list_semantics parameters candidate initial final).
Proof.
  destruct source as [[sources context] variables],candidate as [[candidates target_context] target_variables].
  intros LENGTH WIDTH ACCEPT NONALIAS CHECK; cbn in LENGTH.
  unfold check_double_piece_model in CHECK.
  destruct (Nat.eqb (List.length context) (List.length target_context)) eqn:COUNTS;
    [|apply mayReturn_pure in CHECK; discriminate].
  apply Nat.eqb_eq in COUNTS.
  bind_imp_destruct CHECK pieces PIECES; destruct pieces;
    [|apply mayReturn_pure in CHECK; discriminate].
  rewrite LENGTH in PIECES,CHECK.
  assert (TARGET_LENGTH : List.length target_context=List.length parameters) by lia.
  pose proof (@DoublePieceParameterDomains.piece_restriction_execution parameters guards sources
    context variables initial final LENGTH WIDTH ACCEPT) as SOURCE.
  pose proof (@DoublePieceSequence.checked_sequence_families_execution parameters
    (DoublePieceParameterDomains.piece_restrict_program (List.length parameters) guards sources)
    groups witnesses context variables initial final LENGTH PIECES) as REPRESENTATION.
  pose proof (@validated_double_equivalence_at
    (DoublePieceSequence.sequence_target
      (DoublePieceParameterDomains.piece_restrict_program (List.length parameters) guards sources) groups,context,variables)
    (DoublePieceParameterDomains.piece_restrict_program (List.length parameters) guards candidates,target_context,target_variables)
    parameters initial final LENGTH TARGET_LENGTH NONALIAS CHECK) as ORDER.
  pose proof (@DoublePieceParameterDomains.piece_restriction_execution parameters guards candidates
    target_context target_variables initial final TARGET_LENGTH WIDTH ACCEPT) as TARGET.
  eapply iff_trans; [exact SOURCE|]; eapply iff_trans; [exact REPRESENTATION|].
  eapply iff_trans; [exact ORDER|]; symmetry; exact TARGET.
Qed.
Print Assumptions checked_double_piece_model_equivalence_at.
