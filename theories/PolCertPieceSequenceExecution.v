From Stdlib Require Import List Bool ZArith.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.polygen Require Import PolIRs.
From Vpl Require Import Impure.
From Guard Require Import PolCertPieceSingleExecution PolCertPointSequenceAppend.
Import ListNotations CoreAlarmed.
Set Implicit Arguments.

(** Grouped one-to-many correspondence for an entire instruction list. A
    subsequent validator handles the actual schedules. The source list is an
    explicit checker input, not an optimizer-supplied semantic callback. *)
Module PolCertPieceSequenceExecutionFor (IRs : POLIRS).
Module Single := PolCertPieceSingleExecutionFor IRs.
Module Append := PolCertPointSequenceAppendFor IRs.
Import Single.A.
Definition sequence_to_append_iso parameters source target
  (iso : C.memory_point_isomorphism parameters source target) :
  Append.C.memory_point_isomorphism parameters source target :=
  {| Append.C.point_forward:=C.point_forward iso; Append.C.point_backward:=C.point_backward iso;
     Append.C.point_forward_valid:=C.point_forward_valid iso; Append.C.point_backward_valid:=C.point_backward_valid iso;
     Append.C.point_forward_inverse:=C.point_forward_inverse iso; Append.C.point_backward_inverse:=C.point_backward_inverse iso;
     Append.C.point_forward_time:=C.point_forward_time iso; Append.C.point_backward_time:=C.point_backward_time iso;
     Append.C.point_forward_execution:=C.point_forward_execution iso;
     Append.C.point_backward_execution:=C.point_backward_execution iso |}.
Definition sequence_from_append_iso parameters source target
  (iso : Append.C.memory_point_isomorphism parameters source target) :
  C.memory_point_isomorphism parameters source target :=
  {| C.point_forward:=Append.C.point_forward iso; C.point_backward:=Append.C.point_backward iso;
     C.point_forward_valid:=Append.C.point_forward_valid iso; C.point_backward_valid:=Append.C.point_backward_valid iso;
     C.point_forward_inverse:=Append.C.point_forward_inverse iso; C.point_backward_inverse:=Append.C.point_backward_inverse iso;
     C.point_forward_time:=Append.C.point_forward_time iso; C.point_backward_time:=Append.C.point_backward_time iso;
     C.point_forward_execution:=Append.C.point_forward_execution iso;
     C.point_backward_execution:=Append.C.point_backward_execution iso |}.
Fixpoint sequence_target sources groups := match sources,groups with
  | source::rest,group::remaining=>Single.single_target source group ++ sequence_target rest remaining
  | _,_=>[] end.
Fixpoint check_sequence_families count sources groups witnesses := match sources,groups,witnesses with
  | [],[],[]=>pure true
  | source::rest,group::remaining,witness::proofs=>
    BIND accepted <- Single.check_single_family count source group witness -;
    if accepted then check_sequence_families count rest remaining proofs else pure false
  | _,_,_=>pure false end.
Theorem check_sequence_families_sound count sources groups witnesses :
  mayReturn (check_sequence_families count sources groups witnesses) true ->
  Forall2 (Single.single_certificate count) sources groups.
Proof.
  revert groups witnesses; induction sources as [|source rest IH]; intros [|group remaining] [|witness proofs];
    cbn; intro CHECK; try (apply mayReturn_pure in CHECK; discriminate); [constructor|].
  bind_imp_destruct CHECK accepted ACCEPTED; destruct accepted;
    [|apply mayReturn_pure in CHECK; discriminate].
  constructor; [eapply Single.check_single_family_sound; exact ACCEPTED|eapply IH; exact CHECK].
Qed.
Lemma sequence_has_isomorphism parameters sources groups :
  Forall2 (Single.single_certificate (length parameters)) sources groups ->
  exists iso : C.memory_point_isomorphism parameters sources (sequence_target sources groups), True.
Proof.
  intro CERTIFICATES; induction CERTIFICATES as [|source group rest remaining HEAD TAIL IH].
  - assert (IDENTITY : C.memory_point_isomorphism parameters [] []).
    { refine {| C.point_forward:=fun point=>point; C.point_backward:=fun point=>point |};
        intros; try reflexivity; assumption. }
    exists IDENTITY; exact I.
  - destruct IH as [REST _].
    exists (sequence_from_append_iso (@Append.append_isomorphism parameters [source] rest
      (Single.single_target source group) (sequence_target rest remaining)
      (sequence_to_append_iso (@Single.single_isomorphism parameters source group HEAD))
      (sequence_to_append_iso REST))); exact I.
Qed.
Theorem checked_sequence_families_execution parameters sources groups witnesses context vars initial final :
  length context=length parameters ->
  mayReturn (check_sequence_families (length parameters) sources groups witnesses) true ->
  (PL.poly_instance_list_semantics parameters (sources,context,vars) initial final <->
   PL.poly_instance_list_semantics parameters (sequence_target sources groups,context,vars) initial final).
Proof.
  intros LENGTH CHECK.
  destruct (@sequence_has_isomorphism parameters sources groups
    (@check_sequence_families_sound (length parameters) sources groups witnesses CHECK)) as [ISO _].
  exact (@C.memory_point_isomorphism_execution parameters sources (sequence_target sources groups)
    context vars initial final ISO LENGTH).
Qed.
End PolCertPieceSequenceExecutionFor.
