From Stdlib Require Import List Bool.
From compcert.cfrontend Require Import Clight.
From Guard Require Import ClightStructuredProgress ClightRegionProgress ClightSequenceProgress.
Import ListNotations.
Set Implicit Arguments.

(** The old public selector classified a loop at the region root. An observed
    region additionally retains a prefix and suffix. Compose their established
    framed protocols instead of mistaking a completed-run contract for source
    progress. The sequence's first administrative step is always active. *)
Definition sequence_progress_supported source :=
  match source with
  | Ssequence first second =>
    structured_framed_supported (progress_syntax_size source) [] first &&
    structured_framed_supported (progress_syntax_size source) [] second
  | _ => structured_progress_supported source end.

Theorem sequence_progress_supported_sound source : sequence_progress_supported source = true ->
  exists MODEL : region_progress source, True.
Proof.
  destruct source; cbn [sequence_progress_supported]; try apply structured_progress_supported_sound.
  rewrite andb_true_iff; intros [FIRST SECOND].
  destruct (structured_framed_supported_sound _ _ _ FIRST) as [LEFT _].
  destruct (structured_framed_supported_sound _ _ _ SECOND) as [RIGHT _].
  exists (sequence_region_progress LEFT RIGHT); exact I.
Qed.

Print Assumptions sequence_progress_supported_sound.
