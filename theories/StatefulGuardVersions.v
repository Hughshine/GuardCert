From Stdlib Require Import List Bool.
From Guard Require Import StatefulGuard.
Import ListNotations.
Set Implicit Arguments.

(** A language instance discharges its own source domain, preservation frame,
    check encoding, and candidate rule. Different versions may use different
    properties and frames; the common interface is source observations. *)
Record stateful_verified_version {S} (language : stateful_language S)
  (source : stateful_command language) := StatefulVerifiedVersion {
  version_domain : S -> Prop;
  version_presumption : S -> Prop;
  version_frame : S -> S -> Prop;
  version_encoding : projected_guard_encoding language version_domain version_presumption version_frame;
  version_candidate : stateful_command language;
  version_source_domain : forall state observed,
    stateful_command_run language source state observed -> version_domain state;
  version_source_transport : forall state checked observed,
    version_frame state checked -> stateful_command_run language source state observed ->
    stateful_command_run language source checked observed;
  version_candidate_preservation : forall checked observed,
    version_presumption checked -> stateful_command_run language source checked observed ->
    stateful_command_run language version_candidate checked observed
}.

Fixpoint stateful_versioned_command {S} (language : stateful_language S)
  source (versions : list (stateful_verified_version language source)) : stateful_command language :=
  match versions with
  | [] => source
  | version::rest => stateful_conditional language (projected_guard_test (version_encoding version))
      (version_candidate version) (@stateful_versioned_command S language source rest)
  end.

Theorem stateful_versions_preservation S (language : stateful_language S) source
  (versions : list (stateful_verified_version language source)) :
  forall state observed, stateful_command_run language source state observed ->
    stateful_command_run language (@stateful_versioned_command S language source versions) state observed.
Proof.
  induction versions as [|version rest IH]; intros state observed SOURCE; cbn.
  - exact SOURCE.
  - destruct (@projected_guard_execution S language (version_domain version) (version_presumption version)
      (version_frame version) (version_encoding version) state (@version_source_domain S language source version state observed SOURCE))
      as [accepted [checked [CHECK [FRAME PROPERTY]]]].
    pose proof (@version_source_transport S language source version state checked observed FRAME SOURCE) as PRESERVED.
    eapply stateful_conditional_intro; [exact CHECK|].
    destruct accepted.
    + apply (@version_candidate_preservation S language source version checked observed); [apply PROPERTY; reflexivity|exact PRESERVED].
    + apply IH; exact PRESERVED.
Qed.
Print Assumptions stateful_versions_preservation.
