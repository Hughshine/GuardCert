From Stdlib Require Import List ZArith.
From compcert.lib Require Import Maps.
From compcert.common Require Import Memory.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightSameAddress.
From GuardInterface Require Import ClightReadonlyRewrite ClightRegionBoundary ClightReadonlyCellSwap.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Footprints are specifications of actual entry pointers. Guard code never
    queries block identifiers or these ghost byte sets. *)
Definition cell_pair_bytes p q entry block byte := exists pointer offset,
  In pointer [p;q] /\ (entry_temps entry) ! pointer = Some (Values.Vptr block offset) /\
  Integers.Ptrofs.unsigned offset <= byte < Integers.Ptrofs.unsigned offset + 4.

Definition cell_pair_ports p q live_out :=
  {| region_inputs := [p;q]; region_stable := [p;q]; region_live_out := live_out;
     region_written := []; region_private := []; region_write_bytes := cell_pair_bytes p q |}.

Definition cell_pair_write_frame p q first second live_out :
  clight_write_frame (cell_pair_ports p q live_out) (cell_pair_domain p q) (cell_pair p q first second).
Proof.
  constructor.
  - cbn [cell_pair_ports region_inputs region_written region_private app].
    unfold statement_scope; cbn [cell_pair cell_store word_load pointer_temp statement_temps expression_temps].
    intros id IN; exact IN.
  - cbn [cell_pair_ports region_written region_private app]; unfold cell_pair, cell_store; repeat constructor.
  - apply incl_refl.
  - intros id _ BAD; exact BAD.
  - intros id BAD; contradiction.
  - intros fe entry observed DOMAIN RUN.
    destruct (cell_pair_decode RUN) as [b1 [ofs1 [b2 [ofs2 [middle [P [Q [EXIT [FIRST SECOND]]]]]]]]].
    destruct (@storev_word_facts _ _ _ _ _ FIRST) as [_ STORE1].
    destruct (@storev_word_facts _ _ _ _ _ SECOND) as [_ STORE2].
    unfold outside_region_writes; cbn [cell_pair_ports region_write_bytes].
    eapply write_frames_compose.
    + eapply store_write_frame; [exact STORE1|].
      intros byte RANGE; exists p, ofs1; split; [cbn; auto|split; [exact P|exact RANGE]].
    + eapply store_write_frame; [exact STORE2|].
      intros byte RANGE; exists q, ofs2; split; [cbn; auto|split; [exact Q|exact RANGE]].
  - intros fe entry observed DOMAIN RUN.
    destruct (cell_pair_decode RUN) as [b1 [ofs1 [b2 [ofs2 [middle [P [Q [EXIT [FIRST SECOND]]]]]]]]].
    destruct (@storev_word_facts _ _ _ _ _ FIRST) as [_ STORE1].
    destruct (@storev_word_facts _ _ _ _ _ SECOND) as [_ STORE2].
    rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE2), (Mem.nextblock_store _ _ _ _ _ _ STORE1); reflexivity.
Defined.

Theorem cell_pair_stable_parameters p q first second fe entry observed :
  ClightReadonlyRewrite.clight_fragment_run fe (cell_pair p q first second) entry observed ->
  temp_agree [p;q] (entry_temps entry) (fragment_temps observed).
Proof.
  intro RUN; exact (write_frame_preserves_stable_inputs (cell_pair_write_frame p q first second [p;q]) RUN).
Qed.

Print Assumptions cell_pair_write_frame.
Print Assumptions cell_pair_stable_parameters.
