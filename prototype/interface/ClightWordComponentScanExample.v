From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightNoWrap ClightTempFrame ClightTempFootprint
  ClightCountedLoop ClightLoopExecution CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightWordArithmeticTransport ClightWordCoordinateRename
  ClightRenamedWordObservation ClightDirectWordObservation ClightWordComponentScan
  ClightTensorHeaderPointExample ClightAffineJointObservation ClightObservedHeaderPrefix
  ClightExpressionBodyPrefix ClightDualLoadedUnitSyntax ClightExpressionHeaderCapture
  ClightStrictLoopProgress ClightSignedExpressionProgress.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** Five actual source stores use the wrapping product 2*MAX. The scan reads
    the same runtime words but keeps its component coordinate private. *)
Definition wcs_index := Ebinop Oadd
  (Ebinop Oadd(Ebinop Omul(Etempvar 1%positive type_int32s)
    (Etempvar 6%positive type_int32s)type_int32s)(Econst_int(Int.repr 7)type_int32s)type_int32s)
  (Etempvar 3%positive type_int32s)type_int32s.
Definition wcs_rhs := Econst_int(Int.repr 7)type_int32s.
Definition wcs_body := direct_word_store 10%positive wcs_index wcs_rhs.
Definition wcs_rename id := if Pos.eqb id 3%positive then 103%positive else id.
Definition wcs_stable := [1%positive;6%positive;10%positive;50%positive].
Definition wcs_live := 3%positive::11%positive::wcs_stable.
Definition wcs_temps base := PTree.set 3%positive(Vint Int.zero)
  (PTree.set 50%positive(Vint(Int.repr 5))(PTree.set 10%positive(Vptr 1%positive base)thp_temps)).
Definition wcs_offset base k := word_pointer_offset base(Int.repr(5+k)).
Definition wcs_source := strict_frontend_loop 3%positive
  (signed_expression_test 3%positive(Econst_int(Int.repr 5)type_int32s))wcs_body.
Definition wcs_scan := word_component_scan_code 10%positive 103%positive 104%positive 108%positive
  wcs_index wcs_rename thp_observers 5.
Definition wcs_flag base := @word_component_result 10%positive 103%positive wcs_index wcs_rename
  (wcs_temps base)thp_observers 5.

Lemma wcs_word : word_arithmetic wcs_index.
Proof. apply word_arithmetic_check_sound; reflexivity. Qed.
Lemma wcs_index_value temps k : 0<=k<=5 ->
  temps!1%positive=Some(Vint(Int.repr 2)) ->
  temps!6%positive=Some(Vint(Int.repr Int.max_signed)) ->
  temps!3%positive=Some(Vint(Int.repr k)) ->
  word_evaluate temps wcs_index=Some(Int.repr(5+k)).
Proof.
  intros RANGE ROW STRIDE COMPONENT; cbn [wcs_index word_evaluate]; rewrite ROW,STRIDE,COMPONENT.
  change(Some(Int.add(Int.repr 5)(Int.repr k))=Some(Int.repr(5+k))).
  rewrite Int.add_signed; change(Int.signed(Int.repr 5))with 5.
  rewrite Int.signed_repr; [reflexivity|change(-2147483648<=k<=2147483647); lia].
Qed.
Lemma wcs_address_value ge locals temps memory base k : 0<=k<=5 ->
  temps!1%positive=Some(Vint(Int.repr 2)) ->
  temps!6%positive=Some(Vint(Int.repr Int.max_signed)) ->
  temps!3%positive=Some(Vint(Int.repr k)) -> temps!10%positive=Some(Vptr 1%positive base) ->
  eval_expr ge locals temps memory(direct_word_address 10%positive wcs_index)(Vptr 1%positive(wcs_offset base k)).
Proof.
  intros RANGE ROW STRIDE COMPONENT POINTER; apply word_address_evaluate_sound; [exact wcs_word|].
  unfold word_address_evaluate; rewrite POINTER,(@wcs_index_value temps k RANGE ROW STRIDE COMPONENT); reflexivity.
Qed.
Lemma wcs_offset_limits base k : (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> 0<=k<5 ->
  Ptrofs.unsigned(wcs_offset base k)+4<=Ptrofs.modulus.
Proof.
  intros BASE RANGE; assert(POINT:k=0 \/ k=1 \/ k=2 \/ k=3 \/ k=4)by lia.
  destruct BASE as [->| ->]; destruct POINT as [->|[->|[->|[->| ->]]]]; vm_compute; congruence.
Qed.
Lemma wcs_store_execution fe ge locals temps memory final base k :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> 0<=k<5 ->
  temps!1%positive=Some(Vint(Int.repr 2)) ->
  temps!6%positive=Some(Vint(Int.repr Int.max_signed)) ->
  temps!3%positive=Some(Vint(Int.repr k)) -> temps!10%positive=Some(Vptr 1%positive base) ->
  Mem.store Mint32 memory 1%positive(Ptrofs.unsigned(wcs_offset base k))(Vint(Int.repr 7))=Some final ->
  exec_stmt fe ge locals temps memory wcs_body E0 temps final Out_normal.
Proof.
  intros BASE RANGE ROW STRIDE COMPONENT POINTER STORE.
  unfold wcs_body,direct_word_store; eapply exec_Sassign with(loc:=1%positive)(ofs:=wcs_offset base k)
    (bf:=Full)(v:=Vint(Int.repr 7))(v2:=Vint(Int.repr 7)).
  - apply eval_Ederef; eapply wcs_address_value; eauto; lia.
  - constructor.
  - reflexivity.
  - apply assign_loc_value with(chunk:=Mint32); [reflexivity|].
    cbn [Mem.storev]; destruct(zle _ _)as [END|END]; [exact STORE|].
    change(Ptrofs.unsigned(wcs_offset base k)+4>Ptrofs.modulus)in END.
    pose proof(wcs_offset_limits BASE RANGE); lia.
Qed.

Lemma wcs_original_tail count : forall fe ge locals temps memory base k,
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> 0<=k -> k+Z.of_nat count=5 ->
  temps!1%positive=Some(Vint(Int.repr 2)) ->
  temps!6%positive=Some(Vint(Int.repr Int.max_signed)) ->
  temps!3%positive=Some(Vint(Int.repr k)) -> temps!10%positive=Some(Vptr 1%positive base) ->
  (forall point,0<=point<5 -> Mem.valid_access memory Mint32 1%positive(Ptrofs.unsigned(wcs_offset base point))Writable) ->
  exists after final,exec_stmt fe ge locals temps memory wcs_source E0 after final Out_normal.
Proof.
  induction count as [|count IH]; intros fe ge locals temps memory base k BASE NONNEG COUNT ROW STRIDE COMPONENT POINTER ACCESS.
  - cbn in COUNT; replace k with 5 in * by lia; exists temps,memory; unfold wcs_source.
    apply signed_expression_zero_trip_execution; change false with(Int.lt(Int.repr 5)(Int.repr 5)).
    apply signed_expression_test_eval; [reflexivity|exact COMPONENT|constructor].
  - assert(RANGE:0<=k<5)by(rewrite Nat2Z.inj_succ in COUNT; lia).
    assert(SIGNED:signed_range k)by(change(-2147483648<=k<=2147483647); lia).
    destruct(Mem.valid_access_store _ _ _ _ (Vint(Int.repr 7))(ACCESS k RANGE))as [middle STORE].
    destruct(IH fe ge locals(PTree.set 3%positive(Vint(Int.repr(k+1)))temps)middle base(k+1))as [after [final REST]].
    + exact BASE.
    + lia.
    + rewrite Nat2Z.inj_succ in COUNT; lia.
    + rewrite PTree.gso by discriminate; exact ROW.
    + rewrite PTree.gso by discriminate; exact STRIDE.
    + apply PTree.gss.
    + rewrite PTree.gso by discriminate; exact POINTER.
    + intros point POINT; eapply Mem.store_valid_access_1; [exact STORE|apply ACCESS; exact POINT].
    + exists after,final; unfold wcs_source; eapply strict_iteration_encode with(body_temps:=temps)(body_memory:=middle).
      * assert(FLAG:Int.lt(Int.repr k)(Int.repr 5)=true).
        { unfold Int.lt; rewrite Int.signed_repr by exact SIGNED; change(Int.signed(Int.repr 5))with 5;
            destruct(zlt k 5); [reflexivity|lia]. }
        rewrite <-FLAG; apply signed_expression_test_eval; [reflexivity|exact COMPONENT|constructor].
      * exists(Int.repr k); split; [exact COMPONENT|rewrite Int.signed_repr by exact SIGNED; change Int.max_signed with 2147483647; lia].
      * eapply wcs_store_execution; eassumption.
      * rewrite(@counter_increment_small 3%positive temps k COMPONENT); exact REST.
Qed.

Lemma wcs_access base : (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) ->
  forall point,0<=point<5 -> Mem.valid_access thp_memory Mint32 1%positive(Ptrofs.unsigned(wcs_offset base point))Writable.
Proof.
  intros BASE point RANGE.
  assert(POINT:point=0 \/ point=1 \/ point=2 \/ point=3 \/ point=4)by lia.
  destruct BASE as [->| ->]; destruct POINT as [->|[->|[->|[->| ->]]]].
  all: eapply Mem.store_valid_access_1; [exact(proj2_sig thp_data_state)|].
  all: eapply Mem.store_valid_access_1; [exact(proj2_sig thp_child_state)|].
  all: eapply Mem.store_valid_access_1; [exact(proj2_sig thp_root_state)|].
  all: apply thp_allocated_access; try(reflexivity || lia).
  all: try(vm_compute; congruence).
  all: match goal with |- (4|?offset)=>exists(offset/4); vm_compute; reflexivity end.
Qed.

Lemma wcs_observers ge locals base : Forall(word_observer_receipt ge locals(wcs_temps base)thp_memory)thp_observers.
Proof.
  pose proof(thp_observer_receipts ge locals)as READS; rewrite Forall_forall in READS|-*.
  intros observer MEMBER; eapply word_observer_receipt_frame with(live:=[11%positive]);
    [apply READS; exact MEMBER| |].
  - cbn [thp_observers]in MEMBER; destruct MEMBER as [SAME|[SAME|[]]]; subst observer;
      change(incl[11%positive][11%positive]); intros id KEY; exact KEY.
  - intros id KEY; cbn in KEY; destruct KEY as [SAME|[]]; subst id; reflexivity.
Qed.

Definition wcs_prefix fe ge locals base := @word_component_prefix fe ge locals thp_memory
  3%positive 50%positive 10%positive wcs_index wcs_rhs wcs_stable(wcs_temps base)thp_observers 5 0.
Theorem wcs_original_five_store_prefix fe ge locals base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> wcs_prefix fe ge locals base.
Proof.
  intro BASE; unfold wcs_prefix,word_component_prefix.
  destruct(@wcs_original_tail 5%nat fe ge locals(wcs_temps base)thp_memory base 0)
    as [after [final SOURCE]]; try(reflexivity || lia).
  - exact BASE.
  - apply wcs_access; exact BASE.
  - eapply expression_body_prefix_initial with(after:=after)(final:=final).
    + exact I.
    + exists(Int.repr 5); reflexivity.
    + change(0<=5); lia.
    + reflexivity.
    + unfold header_observations_match; rewrite Forall_map.
      eapply Forall_impl; [|exact(@wcs_observers ge locals base)].
      intros observer RECEIPT; exact(proj1(word_observer_receipt_load RECEIPT)).
    + exact SOURCE.
Qed.

Example wcs_five_points_accepted : wcs_flag(Ptrofs.repr 16)=true.
Proof. vm_compute; reflexivity. Qed.
Example wcs_first_alias_refused : wcs_flag(Ptrofs.repr(-20))=false.
Proof. vm_compute; reflexivity. Qed.

Theorem wcs_actual_scan fe ge locals base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) ->
  exists after,
    exec_stmt fe ge locals(PTree.set 108%positive(memory_boolean_word true)(wcs_temps base))thp_memory
      wcs_scan E0 after thp_memory Out_normal /\
    temp_agree wcs_live(PTree.set 108%positive(memory_boolean_word true)(wcs_temps base))after /\
    after!108%positive=Some(memory_boolean_word(wcs_flag base)).
Proof.
  intro BASE.
  destruct(@word_component_scan_execution fe ge locals thp_memory
    3%positive 50%positive 10%positive 103%positive 104%positive 108%positive wcs_index wcs_rhs wcs_rename
    wcs_stable wcs_live(wcs_temps base)(wcs_temps base)thp_observers 5 wcs_word
    ltac:(lia)ltac:(change(-2147483648<=5<=2147483647); lia)eq_refl
    ltac:(cbn [In app wcs_stable]; intuition discriminate)
    ltac:(cbn [In app wcs_stable]; intuition)
    ltac:(cbn [In app wcs_live wcs_stable]; intuition)eq_refl
    ltac:(change(incl[1%positive;6%positive;3%positive][3%positive;1%positive;6%positive;10%positive;50%positive]);
      intros id MEMBER; cbn [In]in MEMBER|-*; intuition)
    eq_refl ltac:(change(incl[1%positive;6%positive;10%positive;50%positive]
      [3%positive;11%positive;1%positive;6%positive;10%positive;50%positive]);
      intros id MEMBER; cbn [In]in MEMBER|-*; intuition)
    ltac:(intros id MEMBER; cbn [In app wcs_stable]in MEMBER;
      destruct MEMBER as [SAME|[SAME|[SAME|[SAME|[]]]]]; subst id; reflexivity)
    ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
    ltac:(cbn [In app wcs_live wcs_stable]; intuition discriminate)
    ltac:(cbn [In app wcs_live wcs_stable]; intuition discriminate)
    ltac:(cbn [In app wcs_live wcs_stable]; intuition discriminate)
    (@wcs_observers ge locals base)
    ltac:(intros observer MEMBER; cbn [In app thp_observers]in MEMBER;
      destruct MEMBER as [SAME|[SAME|[]]]; subst observer;
      change(incl[11%positive]wcs_live); intros id KEY; cbn [In wcs_live wcs_stable]in KEY|-*; intuition)
    (PTree.set 108%positive(memory_boolean_word true)(wcs_temps base))
    (@wcs_original_five_store_prefix fe ge locals base BASE)(PTree.gss _ _ _)
    ltac:(apply temp_agree_set; cbn [In app wcs_live wcs_stable]; intuition discriminate))
    as [after [RUN [FRAME [FLAG PRESERVE]]]].
  exists after; split; [exact RUN|split; assumption].
Qed.

Theorem wcs_actual_five_point_acceptance fe ge locals : exists after,
  exec_stmt fe ge locals(PTree.set 108%positive(memory_boolean_word true)(wcs_temps(Ptrofs.repr 16)))thp_memory
    wcs_scan E0 after thp_memory Out_normal /\
  after!108%positive=Some(memory_boolean_word true).
Proof.
  destruct(@wcs_actual_scan fe ge locals(Ptrofs.repr 16)ltac:(left; reflexivity))as [after [RUN [FRAME FLAG]]].
  exists after; split; [exact RUN|rewrite wcs_five_points_accepted in FLAG; exact FLAG].
Qed.
Theorem wcs_actual_first_alias_refusal fe ge locals : exists after,
  exec_stmt fe ge locals(PTree.set 108%positive(memory_boolean_word true)(wcs_temps(Ptrofs.repr(-20))))thp_memory
    wcs_scan E0 after thp_memory Out_normal /\
  after!108%positive=Some(memory_boolean_word false).
Proof.
  destruct(@wcs_actual_scan fe ge locals(Ptrofs.repr(-20))ltac:(right; reflexivity))as [after [RUN [FRAME FLAG]]].
  exists after; split; [exact RUN|rewrite wcs_first_alias_refused in FLAG; exact FLAG].
Qed.

Print Assumptions wcs_word.
Print Assumptions wcs_index_value.
Print Assumptions wcs_address_value.
Print Assumptions wcs_offset_limits.
Print Assumptions wcs_store_execution.
Print Assumptions wcs_original_tail.
Print Assumptions wcs_access.
Print Assumptions wcs_observers.
Print Assumptions wcs_original_five_store_prefix.
Print Assumptions wcs_five_points_accepted.
Print Assumptions wcs_first_alias_refused.
Print Assumptions wcs_actual_scan.
Print Assumptions wcs_actual_five_point_acceptance.
Print Assumptions wcs_actual_first_alias_refusal.
