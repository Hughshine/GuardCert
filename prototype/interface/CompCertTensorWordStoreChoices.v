From Stdlib Require Import ZArith Lia.
From compcert.lib Require Import Coqlib Integers.
From compcert.common Require Import AST Values Memory.
From GuardInterface Require Import CompCertWordObservation.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Successful full-word stores preserve permissions and cannot change a
    loaded word to a third value. This is useful for constructing original
    source executions whose loaded bounds change on an aliasing store. *)
Lemma tensor_mint32_store_observation_choices before after old word block offset observed_block observed_offset :
  Mem.load Mint32 before observed_block observed_offset=Some(Vint old) ->
  Mem.store Mint32 before block offset(Vint word)=Some after ->
  Mem.load Mint32 after observed_block observed_offset=Some(Vint old) \/
  Mem.load Mint32 after observed_block observed_offset=Some(Vint word).
Proof.
  intros LOAD STORE.
  destruct(peq observed_block block)as [SAME_BLOCK|OTHER_BLOCK].
  - subst observed_block; destruct(Z.eq_dec observed_offset offset)as [SAME_OFFSET|OTHER_OFFSET].
    + subst observed_offset; right; change(Some(Vint word))with(Some(Val.load_result Mint32(Vint word))).
      eapply Mem.load_store_same; exact STORE.
    + left; pose proof(Mem.load_valid_access _ _ _ _ _ LOAD)as LOAD_ACCESS.
      pose proof(Mem.store_valid_access_3 _ _ _ _ _ _ STORE)as STORE_ACCESS.
      destruct LOAD_ACCESS as [_ [read_multiple READ_ALIGN]];
        destruct STORE_ACCESS as [_ [write_multiple WRITE_ALIGN]].
      cbn [align_chunk]in READ_ALIGN,WRITE_ALIGN.
      erewrite Mem.load_store_other; [exact LOAD|exact STORE|cbn [size_chunk]; right; lia].
  - left; erewrite Mem.load_store_other; [exact LOAD|exact STORE|left; exact OTHER_BLOCK].
Qed.

Theorem tensor_constant_word_stores_observation_choices word before after old block offset :
  constant_word_stores word before after -> Mem.load Mint32 before block offset=Some(Vint old) ->
  Mem.load Mint32 after block offset=Some(Vint old) \/ Mem.load Mint32 after block offset=Some(Vint word).
Proof.
  intros STORES; induction STORES; intro LOAD; [left; exact LOAD|].
  destruct(@tensor_mint32_store_observation_choices before middle old word block0 offset0 block offset LOAD H)as [UNCHANGED|WRITTEN].
  - apply IHSTORES; exact UNCHANGED.
  - right; eapply constant_word_stores_preserve_observation; eassumption.
Qed.

Theorem tensor_constant_word_stores_permissions_forward word before after :
  constant_word_stores word before after -> forall chunk block offset permission,
    Mem.valid_access before chunk block offset permission -> Mem.valid_access after chunk block offset permission.
Proof.
  intro STORES; induction STORES; intros chunk target address permission ACCESS; [exact ACCESS|].
  apply IHSTORES; eapply Mem.store_valid_access_1; eassumption.
Qed.

Print Assumptions tensor_mint32_store_observation_choices.
Print Assumptions tensor_constant_word_stores_observation_choices.
Print Assumptions tensor_constant_word_stores_permissions_forward.
