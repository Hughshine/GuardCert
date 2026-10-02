From Stdlib Require Import List Bool Arith Lia.
From compcert.lib Require Import Coqlib.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Clight.
From Guard Require Import SilentRegionProtocol ClightFiniteRegion ClightSyntaxEquality
  ClightCountedLoop ClightRegionProgress ClightProgressClassifier ClightFrontendLoopProtocol
  ClightFrontendRegion ClightFragmentProgress ClightSequenceProgress ClightNestedProgress
  ClightNestedFrontendProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope nat_scope.

Record loop_description := LoopDescription {
  described_iterator : ident;
  described_bound : ident;
  described_body : statement;
  described_frontend : bool
}.
Definition described_loop d :=
  if described_frontend d then frontend_counted_loop (described_iterator d) (described_bound d) (described_body d)
  else counted_loop (described_iterator d) (described_bound d) (described_body d).
Definition propose_structured_loop source :=
  match propose_frontend_shape source with
  | Some (iterator, bound, body) => Some (LoopDescription iterator bound body true)
  | None => match propose_counted_shape source with
    | Some (iterator, bound, body) => Some (LoopDescription iterator bound body false)
    | None => None end end.
Definition checked_structured_loop source :=
  match propose_structured_loop source with
  | Some d => if statement_eq source (described_loop d) then Some d else None
  | None => None end.
Lemma checked_structured_loop_binds source d : checked_structured_loop source = Some d ->
  source = described_loop d.
Proof.
  unfold checked_structured_loop; destruct (propose_structured_loop source) as [proposed|]; try discriminate.
  destruct (statement_eq source (described_loop proposed)) as [EQ|NE]; try discriminate.
  intro SELECT; inversion SELECT; subst; reflexivity.
Qed.
Definition sequence_parts source := match source with
  | Ssequence first second => Some (first, second) | _ => None end.
Lemma sequence_parts_binds source first second : sequence_parts source = Some (first,second) ->
  source = Ssequence first second.
Proof. destruct source; cbn [sequence_parts]; try discriminate; intro EQ; inversion EQ; reflexivity. Qed.

(** Fuel bounds certificate construction, not execution. Entry fuel is the
    source AST size; unsupported control forms are conservatively rejected. *)
Fixpoint structured_framed_supported (fuel : nat) protected source : bool :=
  match fuel with
  | 0 => false
  | S rest =>
    if frame_statement protected source then true else
    match sequence_parts source with
    | Some (first,second) => structured_framed_supported rest protected first &&
        structured_framed_supported rest protected second
    | None => match checked_structured_loop source with
      | Some d =>
        if peq (described_iterator d) (described_bound d) then false else
        if in_dec peq (described_iterator d) protected then false else
        structured_framed_supported rest
          (described_iterator d :: described_bound d :: protected) (described_body d)
      | None => false end end end.

Theorem structured_framed_supported_sound fuel protected source :
  structured_framed_supported fuel protected source = true ->
  exists MODEL : framed_progress source protected, True.
Proof.
  revert protected source; induction fuel as [|fuel IH]; intros protected source; [discriminate|].
  cbn [structured_framed_supported].
  destruct (frame_statement protected source) eqn:FINITE.
  - intros _; exists (finite_framed_progress protected source FINITE); exact I.
  - destruct (sequence_parts source) as [[first second]|] eqn:PARTS.
    + rewrite andb_true_iff; intros [LEFT RIGHT].
      destruct (IH protected first LEFT) as [F _], (IH protected second RIGHT) as [G _].
      apply sequence_parts_binds in PARTS; subst source.
      exists (sequence_framed_progress F G); exact I.
    + destruct (checked_structured_loop source) as [d|] eqn:LOOP; try discriminate.
      destruct (peq (described_iterator d) (described_bound d)) as [EQ|DISTINCT]; try discriminate.
      destruct (in_dec peq (described_iterator d) protected) as [IN|NOT_WRITTEN]; try discriminate.
      intro BODY; destruct (IH _ _ BODY) as [F _].
      apply checked_structured_loop_binds in LOOP; subst source.
      destruct d as [iterator bound body frontend]; cbn in DISTINCT, NOT_WRITTEN, F |- *.
      unfold described_loop; cbn; destruct frontend.
      * exists (@frontend_framed_progress iterator bound DISTINCT protected NOT_WRITTEN body F); exact I.
      * exists (@counted_framed_progress iterator bound DISTINCT protected NOT_WRITTEN body F); exact I.
Qed.

Fixpoint progress_syntax_size source : nat :=
  match source with
  | Ssequence first second | Sifthenelse _ first second | Sloop first second =>
      S (progress_syntax_size first + progress_syntax_size second)
  | _ => 1 end.
Definition structured_progress_supported source :=
  match checked_structured_loop source with
  | Some d => if peq (described_iterator d) (described_bound d) then false else
      structured_framed_supported (progress_syntax_size source)
        [described_iterator d; described_bound d] (described_body d)
  | None => frontend_progress_supported source end.

Theorem structured_progress_supported_sound source : structured_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  unfold structured_progress_supported; destruct (checked_structured_loop source) as [d|] eqn:LOOP.
  - destruct (peq (described_iterator d) (described_bound d)) as [EQ|DISTINCT]; try discriminate.
    intro BODY. destruct (structured_framed_supported_sound _ _ _ BODY) as [F _].
    apply checked_structured_loop_binds in LOOP; subst source.
    destruct d as [iterator bound body frontend]; cbn in DISTINCT, F |- *.
    unfold described_loop; cbn; destruct frontend.
    + exists (@frontend_nested_region_progress iterator bound DISTINCT [] (fun IN => IN) body F); exact I.
    + exists (framed_region_progress (@counted_framed_progress iterator bound DISTINCT []
        (fun IN => IN) body F) (fun temps ge fn outside locals input => eq_refl)); exact I.
  - apply frontend_progress_supported_sound.
Qed.

Print Assumptions structured_progress_supported_sound.
