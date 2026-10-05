From Stdlib Require Import List ZArith.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint CompCertMemoryEquivalence.
From GuardInterface Require Import ClightReadonlyRewrite.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** This interface separates entry values, stable parameters, public exits,
    ordinary writes, and fresh private temporaries. Byte footprints are tied
    to the entry; a loop model separately proves coverage of its actual reads.
    No runtime operation queries this ghost footprint. *)
Record clight_region_ports := ClightRegionPorts {
  region_inputs : list ident;
  region_stable : list ident;
  region_live_out : list ident;
  region_written : list ident;
  region_private : list ident;
  region_write_bytes : clight_entry -> block -> Z -> Prop
}.

Definition boundary_observe ports (actual visible : fragment_observation) :=
  fragment_trace actual = fragment_trace visible /\
  fragment_outcome actual = fragment_outcome visible /\
  temp_agree (region_live_out ports) (fragment_temps visible) (fragment_temps actual) /\
  memory_equivalent (fragment_memory visible) (fragment_memory actual).

Lemma boundary_observe_refl ports observed : boundary_observe ports observed observed.
Proof.
  unfold boundary_observe; split; [reflexivity|split; [reflexivity|split]].
  - apply temp_agree_refl.
  - apply memory_equivalent_refl.
Qed.

Lemma boundary_observe_trans ports first middle last :
  boundary_observe ports first middle -> boundary_observe ports middle last ->
  boundary_observe ports first last.
Proof.
  intros [TRACE1 [EXIT1 [TEMPS1 MEMORY1]]] [TRACE2 [EXIT2 [TEMPS2 MEMORY2]]].
  unfold boundary_observe; split; [congruence|split; [congruence|split]].
  - eapply temp_agree_trans; [exact TEMPS2|exact TEMPS1].
  - eapply memory_equivalent_trans; [exact MEMORY2|exact MEMORY1].
Qed.

Definition outside_region_writes ports entry b offset := ~ region_write_bytes ports entry b offset.

(** A write-frame certificate is not a full read-effect analysis or a global
    context theorem. Actual read coverage belongs to the localization bridge;
    memory and exit compatibility with continuations belong to the host. *)
Record clight_write_frame ports (domain : clight_entry -> Prop) (body : statement) := ClightWriteFrame {
  region_scope : statement_scope
    (region_inputs ports ++ region_written ports ++ region_private ports) body;
  region_temp_writes : writes_only (region_written ports ++ region_private ports) body;
  stable_inputs_declared : incl (region_stable ports) (region_inputs ports);
  stable_inputs_protected : forall id, In id (region_stable ports) ->
    ~ In id (region_written ports ++ region_private ports);
  private_not_public : forall id, In id (region_private ports) -> ~ In id (region_live_out ports);
  region_memory_frame : forall fe entry observed, domain entry ->
    clight_fragment_run fe body entry observed ->
    Mem.unchanged_on (outside_region_writes ports entry) (entry_memory entry) (fragment_memory observed);
  region_allocation_neutral : forall fe entry observed, domain entry ->
    clight_fragment_run fe body entry observed ->
    Mem.nextblock (fragment_memory observed) = Mem.nextblock (entry_memory entry)
}.

Theorem write_frame_preserves_stable_inputs ports domain body
  (FRAME : clight_write_frame ports domain body) fe entry observed :
  clight_fragment_run fe body entry observed ->
  temp_agree (region_stable ports) (entry_temps entry) (fragment_temps observed).
Proof.
  intro RUN; eapply structured_temp_frame.
  - exact (region_temp_writes FRAME).
  - exact (stable_inputs_protected FRAME).
  - exact RUN.
Qed.

Lemma store_write_frame (writes : block -> Z -> Prop) chunk before b offset value after :
  Mem.store chunk before b offset value = Some after ->
  (forall byte, offset <= byte < offset + size_chunk chunk -> writes b byte) ->
  Mem.unchanged_on (fun block byte => ~ writes block byte) before after.
Proof.
  intros STORE COVER; eapply Mem.store_unchanged_on; [exact STORE|].
  intros byte RANGE OUTSIDE; apply OUTSIDE, COVER; exact RANGE.
Qed.

Lemma load_outside_write_frame (writes : block -> Z -> Prop) before after chunk b offset value :
  Mem.unchanged_on (fun block byte => ~ writes block byte) before after ->
  (forall byte, offset <= byte < offset + size_chunk chunk -> ~ writes b byte) ->
  Mem.load chunk before b offset = Some value -> Mem.load chunk after b offset = Some value.
Proof. intros FRAME OUTSIDE LOAD; eapply Mem.load_unchanged_on; eassumption. Qed.

Lemma write_frames_compose (writes : block -> Z -> Prop) first middle last :
  Mem.unchanged_on (fun block byte => ~ writes block byte) first middle ->
  Mem.unchanged_on (fun block byte => ~ writes block byte) middle last ->
  Mem.unchanged_on (fun block byte => ~ writes block byte) first last.
Proof. intros FIRST SECOND; eapply Mem.unchanged_on_trans; eassumption. Qed.

Print Assumptions boundary_observe_refl.
Print Assumptions boundary_observe_trans.
Print Assumptions write_frame_preserves_stable_inputs.
Print Assumptions store_write_frame.
Print Assumptions load_outside_write_frame.
Print Assumptions write_frames_compose.
