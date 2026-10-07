From Stdlib Require Import List.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory.
From compcert.cfrontend Require Import Clight Ctypes.
From Guard Require Import ClightCondition ClightTempFootprint.
From GuardInterface Require Import ClightLoadedBoundSyntax ClightLoadedOffsetHeader
  ClightSignedIndexedOffsetHeader ClightAffineJointObservation.
Import ListNotations.
Set Implicit Arguments.

Definition nested_indexed_word_observers pointer index block offset raw child_raw :=
  [ClightWordObserver(signed_pointer_temp pointer) block offset(Vint raw);
   ClightWordObserver(signed_indexed_pointer pointer index) block(signed_indexed_address offset index)(Vint child_raw)].

(** These evaluations are produced by the ordered capture service only when
    the outer source actually enters. No child load is licensed for an empty
    outer source, and raw observations remain distinct from computed bounds. *)
Theorem nested_indexed_observer_receipts ge locals temps memory pointer index delta child_delta upper child_upper :
  eval_expr ge locals temps memory(signed_load_offset pointer delta)(Vint upper) ->
  eval_expr ge locals temps memory(signed_indexed_offset pointer index child_delta)(Vint child_upper) ->
  exists block offset raw child_raw,
    temps!pointer=Some(Vptr block offset) /\ upper=Int.add raw delta /\ child_upper=Int.add child_raw child_delta /\
    Forall(word_observer_receipt ge locals temps memory)(nested_indexed_word_observers pointer index block offset raw child_raw) /\
    map word_observer_snapshot(nested_indexed_word_observers pointer index block offset raw child_raw)=
      loaded_offset_observations pointer(Entry ge locals temps memory)++
      indexed_offset_observations pointer index(Entry ge locals temps memory).
Proof.
  intros ROOT CHILD.
  destruct(signed_load_offset_inv ROOT) as [block [offset [raw [POINTER [READ UPPER]]]]].
  destruct(signed_indexed_offset_inv CHILD) as [other [base [child_raw [CHILD_POINTER [CHILD_READ CHILD_UPPER]]]]].
  assert (SAME : Vptr block offset=Vptr other base) by congruence; inversion SAME; subst other base.
  exists block,offset,raw,child_raw; split; [exact POINTER|split; [exact UPPER|split; [exact CHILD_UPPER|split]]].
  - constructor.
    + split; [reflexivity|split; [constructor; exact POINTER|exact READ]].
    + constructor; [|constructor].
      split; [reflexivity|split; [apply signed_indexed_pointer_eval; exact POINTER|exact CHILD_READ]].
  - unfold loaded_offset_observations,indexed_offset_observations; cbn [entry_temps entry_memory].
    rewrite POINTER,READ,CHILD_READ; reflexivity.
Qed.

Lemma nested_indexed_observers_scope pointer index block offset raw child_raw live :
  In pointer live ->
  Forall(fun observer=>expression_scope live(word_observer_address observer))
    (nested_indexed_word_observers pointer index block offset raw child_raw).
Proof.
  intro MEMBER; constructor; [|constructor; [|constructor]];
    unfold expression_scope; cbn [nested_indexed_word_observers word_observer_address signed_pointer_temp
      signed_indexed_pointer expression_temps app]; intros identifier [SAME|[]]; subst identifier; exact MEMBER.
Qed.

Print Assumptions nested_indexed_observer_receipts.
Print Assumptions nested_indexed_observers_scope.
