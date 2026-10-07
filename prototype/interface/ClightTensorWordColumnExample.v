From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightTempFrame
  ClightTempFootprint ClightLoopExecution ClightLoopSyntax ClightRectangularLoops ClightRegionProgress
  ClightFrontendLoopProtocol.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions GuardMemoryBooleanScan.
From GuardInterface Require Import ClightTensorWordColumn ClightWordComponentScanExample
  ClightTensorHeaderPointExample ClightConstantBoundModel ClightDirectWordObservation
  ClightExpressionBodyPrefix ClightExpressionBodyTransport ClightAffineJointObservation ClightObservedHeaderPrefix
  ClightSignedIndexedOffsetHeader ClightSignedExpressionProgress ClightStrictLoopProgress
  ClightExpressionHeaderCapture ClightDualLoadedUnitSyntax CompCertWordObservation
  CompCertInvariantWordObservation CompCertTensorWordStoreChoices.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition twc_bound := signed_indexed_offset 11%positive Int.one(Int.repr 2).
Definition twc_component := constant_body_source 3%positive(Int.repr 5)wcs_body.
Definition twc_source := strict_frontend_loop 2%positive(signed_expression_test 2%positive twc_bound)twc_component.
Definition twc_temps base := PTree.set 2%positive(Vint Int.zero)(PTree.set 5%positive(Vint(Int.repr 2))(wcs_temps base)).
Definition twc_stable := [1%positive;5%positive;6%positive;10%positive;11%positive;50%positive].
Definition twc_live := 2%positive::3%positive::twc_stable.
Definition twc_rename id := if Pos.eqb id 2%positive then 102%positive else wcs_rename id.
Definition twc_code := tensor_word_column_scan_code 5%positive 102%positive 105%positive 108%positive
  (ClightWordComponentScan.word_component_scan_code 10%positive 103%positive 104%positive 108%positive
    wcs_index twc_rename thp_observers 5).

Lemma twc_component_stores fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory twc_component E0 after final Out_normal ->
  constant_word_stores(Int.repr 7)memory final.
Proof.
  intro SOURCE; exact(proj1(@checked_invariant_word_control_execution(MemorySourceConstant 7)
    fe ge locals temps memory twc_component E0 after final Out_normal SOURCE ltac:(vm_compute; reflexivity)
    (Int.repr 7)ltac:(constructor))).
Qed.

Lemma twc_component_execution fe ge locals temps memory base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) ->
  temps!1%positive=Some(Vint(Int.repr 2)) -> temps!6%positive=Some(Vint(Int.repr Int.max_signed)) ->
  temps!10%positive=Some(Vptr 1%positive base) ->
  (forall k,0<=k<5 -> Mem.valid_access memory Mint32 1%positive(Ptrofs.unsigned(wcs_offset base k))Writable) ->
  exists after final,exec_stmt fe ge locals temps memory twc_component E0 after final Out_normal.
Proof.
  intros BASE ROW STRIDE POINTER ACCESS.
  destruct(@wcs_original_tail 5%nat fe ge locals(PTree.set 3%positive(Vint Int.zero)temps)memory base 0
    BASE ltac:(lia)eq_refl ltac:(rewrite PTree.gso by discriminate; exact ROW)
    ltac:(rewrite PTree.gso by discriminate; exact STRIDE)(PTree.gss _ _ _)
    ltac:(rewrite PTree.gso by discriminate; exact POINTER)ACCESS)as [after [final SOURCE]].
  exists after,final; unfold twc_component,constant_body_source.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|exact SOURCE].
Qed.

Lemma twc_source_tail count : forall fe ge locals temps memory base j,
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> 0<=j -> j+Z.of_nat count=9 ->
  temps!1%positive=Some(Vint(Int.repr 2)) -> temps!6%positive=Some(Vint(Int.repr Int.max_signed)) ->
  temps!10%positive=Some(Vptr 1%positive base) -> temps!11%positive=Some(Vptr 1%positive Ptrofs.zero) ->
  temps!2%positive=Some(Vint(Int.repr j)) ->
  (Mem.load Mint32 memory 1%positive 4=Some(Vint Int.zero) \/ Mem.load Mint32 memory 1%positive 4=Some(Vint(Int.repr 7))) ->
  (forall k,0<=k<5 -> Mem.valid_access memory Mint32 1%positive(Ptrofs.unsigned(wcs_offset base k))Writable) ->
  exists after final,exec_stmt fe ge locals temps memory twc_source E0 after final Out_normal.
Proof.
  induction count as [|count IH]; intros fe ge locals temps memory base j BASE NONNEG LENGTH ROW STRIDE POINTER HEADER COLUMN CHILD ACCESS.
  all: assert(SIGNED:signed_range j)by(change(-2147483648<=j<=2147483647); rewrite Nat2Z.inj_succ in LENGTH || idtac; lia).
  - cbn in LENGTH; replace j with 9 in * by lia; exists temps,memory; unfold twc_source.
    apply signed_expression_zero_trip_execution.
    destruct CHILD as [CHILD|CHILD]; [change false with(Int.lt(Int.repr 9)(Int.repr 2))|change false with(Int.lt(Int.repr 9)(Int.repr 9))].
    all: apply signed_expression_test_eval; [reflexivity|exact COLUMN|].
    + change(eval_expr ge locals temps memory twc_bound(Vint(Int.add Int.zero(Int.repr 2)))).
      eapply signed_indexed_offset_eval; [exact HEADER|exact CHILD].
    + change(eval_expr ge locals temps memory twc_bound(Vint(Int.add(Int.repr 7)(Int.repr 2)))).
      eapply signed_indexed_offset_eval; [exact HEADER|exact CHILD].
  - assert(RANGE:0<=j<9)by(rewrite Nat2Z.inj_succ in LENGTH; lia).
    assert(BOUND:exists raw upper,
      (raw=Int.zero /\ upper=2 \/ raw=Int.repr 7 /\ upper=9) /\
      eval_expr ge locals temps memory twc_bound(Vint(Int.repr upper))).
    { destruct CHILD as [CHILD|CHILD]; [exists Int.zero,2|exists(Int.repr 7),9]; split;
        [left; split; reflexivity| |right; split; reflexivity|].
      - change(eval_expr ge locals temps memory twc_bound(Vint(Int.add Int.zero(Int.repr 2)))).
        eapply signed_indexed_offset_eval; [exact HEADER|exact CHILD].
      - change(eval_expr ge locals temps memory twc_bound(Vint(Int.add(Int.repr 7)(Int.repr 2)))).
        eapply signed_indexed_offset_eval; [exact HEADER|exact CHILD]. }
    destruct BOUND as [raw [upper [SHAPE EVAL]]].
    assert(UPPER:upper=2 \/ upper=9)by(destruct SHAPE as [[_ SAME]|[_ SAME]]; auto).
    destruct(Z_lt_ge_dec j upper)as [ACTIVE|STOP].
    + destruct(@twc_component_execution fe ge locals temps memory base BASE ROW STRIDE POINTER ACCESS)as [middle [next BODY]].
      pose proof(@twc_component_stores fe ge locals temps memory middle next BODY)as STORES.
      assert(FRAME:temp_agree(2%positive::twc_stable)temps middle).
      { eapply structured_temp_frame; [apply tensor_word_column_source_writes| |exact BODY].
        intros id MEMBER; cbn [In] ; intros [SAME|[]]; subst id; cbn [twc_live twc_stable In]in MEMBER; intuition discriminate. }
      assert(CHILD_NEXT:Mem.load Mint32 next 1%positive 4=Some(Vint Int.zero) \/ Mem.load Mint32 next 1%positive 4=Some(Vint(Int.repr 7))).
      { destruct CHILD as [ZERO|SEVEN].
        - eapply tensor_constant_word_stores_observation_choices; eassumption.
        - right; eapply constant_word_stores_preserve_observation; eassumption. }
      destruct(IH fe ge locals(PTree.set 2%positive(Vint(Int.repr(j+1)))middle)next base(j+1))as [after [final REST]].
      * exact BASE.
      * lia.
      * rewrite Nat2Z.inj_succ in LENGTH; lia.
      * rewrite PTree.gso by discriminate; rewrite FRAME by(cbn [twc_live twc_stable In]; intuition); exact ROW.
      * rewrite PTree.gso by discriminate; rewrite FRAME by(cbn [twc_live twc_stable In]; intuition); exact STRIDE.
      * rewrite PTree.gso by discriminate; rewrite FRAME by(cbn [twc_live twc_stable In]; intuition); exact POINTER.
      * rewrite PTree.gso by discriminate; rewrite FRAME by(cbn [twc_live twc_stable In]; intuition); exact HEADER.
      * apply PTree.gss.
      * exact CHILD_NEXT.
      * intros k INDEX; eapply tensor_constant_word_stores_permissions_forward; [exact STORES|apply ACCESS; exact INDEX].
      * exists after,final; unfold twc_source; eapply strict_iteration_encode with(body_temps:=middle)(body_memory:=next).
        -- assert(LT:Int.lt(Int.repr j)(Int.repr upper)=true).
           { unfold Int.lt; rewrite !Int.signed_repr; try(change(-2147483648<=j<=2147483647); lia);
               try(destruct UPPER as [->| ->]; change(-2147483648<=2<=2147483647) || change(-2147483648<=9<=2147483647); lia).
             destruct(zlt j upper); [reflexivity|lia]. }
           rewrite <-LT; apply signed_expression_test_eval; [reflexivity|exact COLUMN|exact EVAL].
        -- exists(Int.repr j); split; [rewrite FRAME by(cbn [twc_live In]; auto); exact COLUMN|
             rewrite Int.signed_repr by exact SIGNED; change Int.max_signed with 2147483647; lia].
        -- exact BODY.
        -- rewrite(@counter_increment_small 2%positive middle j ltac:(rewrite FRAME by(cbn [twc_live In]; auto); exact COLUMN)); exact REST.
    + exists temps,memory; unfold twc_source; apply signed_expression_zero_trip_execution.
      assert(LT:Int.lt(Int.repr j)(Int.repr upper)=false).
      { unfold Int.lt; rewrite !Int.signed_repr; try(change(-2147483648<=j<=2147483647); lia);
          try(destruct UPPER as [->| ->]; change(-2147483648<=2<=2147483647) || change(-2147483648<=9<=2147483647); lia).
        destruct(zlt j upper); [lia|reflexivity]. }
      rewrite <-LT; apply signed_expression_test_eval; [reflexivity|exact COLUMN|exact EVAL].
Qed.

Theorem twc_original_source_complete fe ge locals base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) ->
  exists after final,exec_stmt fe ge locals(twc_temps base)thp_memory twc_source E0 after final Out_normal.
Proof.
  intro BASE; eapply(@twc_source_tail 9%nat fe ge locals(twc_temps base)thp_memory base 0);
    try(reflexivity || lia).
  - exact BASE.
  - left; change(Mem.loadv Mint32 thp_memory(Vptr 1%positive(Ptrofs.repr 4))=Some(Vint Int.zero)); exact(proj2 thp_header_reads).
  - apply wcs_access; exact BASE.
Qed.

Print Assumptions twc_component_stores.
Print Assumptions twc_component_execution.
Print Assumptions twc_source_tail.
Print Assumptions twc_original_source_complete.

Definition twc_entry ge locals base := Entry ge locals(twc_temps base)thp_memory.
Definition twc_flag ge locals base := @tensor_word_column_result(twc_entry ge locals base)
  5%positive 10%positive 102%positive 105%positive 103%positive wcs_index 5 twc_rename(twc_temps base)thp_observers.
Definition twc_prefix fe ge locals base := @tensor_word_column_prefix fe(twc_entry ge locals base)
  3%positive 2%positive 5%positive 10%positive wcs_index wcs_rhs twc_bound 5 twc_stable thp_observers(fun _=>True)0.

Lemma twc_observers ge locals base : Forall(word_observer_receipt ge locals(twc_temps base)thp_memory)thp_observers.
Proof.
  pose proof(@wcs_observers ge locals base)as READS; rewrite Forall_forall in READS|-*.
  intros observer MEMBER; eapply word_observer_receipt_frame with(live:=[11%positive]);
    [apply READS; exact MEMBER| |].
  - cbn [thp_observers]in MEMBER; destruct MEMBER as [SAME|[SAME|[]]]; subst observer;
      change(incl[11%positive][11%positive]); intros id KEY; exact KEY.
  - intros id KEY; cbn in KEY; destruct KEY as [SAME|[]]; subst id; reflexivity.
Qed.

Lemma twc_header ge locals base j current memory :
  True -> 0<=j<=Int.signed(temp_word 5%positive(twc_temps base)) ->
  current!2%positive=Some(Vint(Int.repr j)) -> temp_agree twc_stable(twc_temps base)current ->
  header_observations_match(map word_observer_snapshot thp_observers)memory ->
  eval_expr ge locals current memory twc_bound(Vint(temp_word 5%positive(twc_temps base))).
Proof.
  intros _ RANGE COLUMN FRAME OBSERVED.
  change(eval_expr ge locals current memory twc_bound(Vint(Int.add Int.zero(Int.repr 2)))).
  eapply signed_indexed_offset_eval.
  - rewrite FRAME by(cbn [twc_stable In]; intuition); reflexivity.
  - inversion OBSERVED as [|first rest ROOT CHILDREN]; subst.
    inversion CHILDREN as [|child tail CHILD EMPTY]; subst.
    exact CHILD.
Qed.

Theorem twc_original_column_prefix fe ge locals base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> twc_prefix fe ge locals base.
Proof.
  intro BASE; destruct(@twc_original_source_complete fe ge locals base BASE)as [after [final SOURCE]].
  unfold twc_prefix,tensor_word_column_prefix,twc_entry.
  eapply expression_body_prefix_initial with(after:=after)(final:=final).
  - exact I.
  - exists(Int.repr 2); reflexivity.
  - change(0<=2); lia.
  - reflexivity.
  - unfold header_observations_match; rewrite Forall_map.
    eapply Forall_impl; [|exact(@twc_observers ge locals base)].
    intros observer RECEIPT; exact(proj1(word_observer_receipt_load RECEIPT)).
  - exact SOURCE.
Qed.

Example twc_two_columns_accept ge locals : twc_flag ge locals(Ptrofs.repr 16)=true.
Proof. vm_compute; reflexivity. Qed.
Example twc_first_column_refuses ge locals : twc_flag ge locals(Ptrofs.repr(-20))=false.
Proof. vm_compute; reflexivity. Qed.

Theorem twc_actual_scan fe ge locals base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> exists after,
    exec_stmt fe ge locals(PTree.set 108%positive(memory_boolean_word true)(twc_temps base))thp_memory
      twc_code E0 after thp_memory Out_normal /\
    temp_agree twc_live(PTree.set 108%positive(memory_boolean_word true)(twc_temps base))after /\
    after!108%positive=Some(memory_boolean_word(twc_flag ge locals base)) /\
    (twc_flag ge locals base=true -> forall j,0<=j<2 ->
      expression_body_preserved fe 2%positive twc_component twc_stable
        (fun _=>map word_observer_snapshot thp_observers)j(twc_entry ge locals base)).
Proof.
  intro BASE.
  assert(SCAN:exists after,
    exec_stmt fe ge locals(PTree.set 108%positive(memory_boolean_word true)(twc_temps base))thp_memory
      twc_code E0 after thp_memory Out_normal /\
    temp_agree twc_live(PTree.set 108%positive(memory_boolean_word true)(twc_temps base))after /\
    after!108%positive=Some(memory_boolean_word(twc_flag ge locals base)) /\
    (twc_flag ge locals base=true -> forall j,0<=j<2 ->
      expression_body_preserved fe 2%positive twc_component twc_stable
        (fun _=>map word_observer_snapshot thp_observers)j(twc_entry ge locals base))).
  { eapply(@tensor_word_column_scan_execution fe(twc_entry ge locals base)
      3%positive 50%positive 2%positive 5%positive 10%positive 102%positive 105%positive
      103%positive 104%positive 108%positive wcs_index wcs_rhs twc_bound 5 twc_rename
      twc_stable twc_live(twc_temps base)thp_observers(fun _=>True)).
    all: try(reflexivity || discriminate || exact wcs_word || lia).
    all: try solve[change(-2147483648<=5<=2147483647); lia].
    all: try solve[cbn [twc_stable twc_live In]; intuition discriminate].
    all: try solve[exact(@twc_header ge locals base)].
    all: try solve[exact(@twc_observers ge locals base)].
    all: try solve[exact(@twc_original_column_prefix fe ge locals base BASE)].
    all: try solve[apply temp_agree_set; cbn [twc_live twc_stable In]; intuition discriminate].
    all: try solve[intros id MEMBER; cbn [twc_stable In]in MEMBER;
      destruct MEMBER as [SAME|[SAME|[SAME|[SAME|[SAME|[SAME|[]]]]]]]; subst id; reflexivity].
    all: try solve[change(incl[1%positive;6%positive;3%positive](3%positive::2%positive::twc_stable));
      intros id MEMBER; cbn [twc_stable In]in MEMBER|-*; intuition].
    all: try solve[change(incl twc_stable twc_live); intros id MEMBER; right; right; exact MEMBER].
    all: try solve[intros observer MEMBER; cbn [thp_observers In]in MEMBER;
      destruct MEMBER as [SAME|[SAME|[]]]; subst observer; change(incl[11%positive]twc_live);
      intros id KEY; cbn [twc_live twc_stable In]in KEY|-*; intuition]. }
  exact SCAN.
Qed.

Theorem twc_actual_acceptance fe ge locals : exists after,
  exec_stmt fe ge locals(PTree.set 108%positive(memory_boolean_word true)(twc_temps(Ptrofs.repr 16)))thp_memory
    twc_code E0 after thp_memory Out_normal /\ after!108%positive=Some(memory_boolean_word true).
Proof.
  destruct(@twc_actual_scan fe ge locals(Ptrofs.repr 16)ltac:(left; reflexivity))as [after [RUN [FRAME [FLAG PRESERVE]]]].
  exists after; split; [exact RUN|rewrite twc_two_columns_accept in FLAG; exact FLAG].
Qed.
Theorem twc_actual_alias_refusal fe ge locals : exists after,
  exec_stmt fe ge locals(PTree.set 108%positive(memory_boolean_word true)(twc_temps(Ptrofs.repr(-20))))thp_memory
    twc_code E0 after thp_memory Out_normal /\ after!108%positive=Some(memory_boolean_word false).
Proof.
  destruct(@twc_actual_scan fe ge locals(Ptrofs.repr(-20))ltac:(right; reflexivity))as [after [RUN [FRAME [FLAG PRESERVE]]]].
  exists after; split; [exact RUN|rewrite twc_first_column_refuses in FLAG; exact FLAG].
Qed.

Print Assumptions twc_observers.
Print Assumptions twc_header.
Print Assumptions twc_original_column_prefix.
Print Assumptions twc_two_columns_accept.
Print Assumptions twc_first_column_refuses.
Print Assumptions twc_actual_scan.
Print Assumptions twc_actual_acceptance.
Print Assumptions twc_actual_alias_refusal.

(** Full scan acceptance produces the cached loop's actual execution with
    exactly the source exit temporaries and memory, including the component
    counter. The cached execution is a conclusion, not a permission premise. *)
Theorem twc_actual_cached_source fe ge locals : exists after final,
  exec_stmt fe ge locals(twc_temps(Ptrofs.repr 16))thp_memory twc_source E0 after final Out_normal /\
  exec_stmt fe ge locals(twc_temps(Ptrofs.repr 16))thp_memory
    (frontend_counted_loop 2%positive 5%positive twc_component)E0 after final Out_normal /\
  header_observations_match(map word_observer_snapshot thp_observers)final.
Proof.
  destruct(@twc_original_source_complete fe ge locals(Ptrofs.repr 16)ltac:(left; reflexivity))as [after [final SOURCE]].
  destruct(@twc_actual_scan fe ge locals(Ptrofs.repr 16)ltac:(left; reflexivity))
    as [checked [SCAN [PUBLIC [FLAG PRESERVE]]]].
  assert(INITIAL:header_observations_match(map word_observer_snapshot thp_observers)thp_memory).
  { unfold header_observations_match; rewrite Forall_map.
    eapply Forall_impl; [|exact(@twc_observers ge locals(Ptrofs.repr 16))].
    intros observer RECEIPT; exact(proj1(word_observer_receipt_load RECEIPT)). }
  assert(CACHED:
    exec_stmt fe ge locals(twc_temps(Ptrofs.repr 16))thp_memory
      (frontend_counted_loop 2%positive 5%positive twc_component)E0 after final Out_normal /\
    expression_body_snapshot 2%positive twc_stable(twc_temps(Ptrofs.repr 16))
      (map word_observer_snapshot thp_observers)2 after final).
  { eapply(@expression_body_bound_cached fe ge locals 2%positive 5%positive twc_bound twc_component
      twc_stable[3%positive](twc_temps(Ptrofs.repr 16))(map word_observer_snapshot thp_observers)(Int.repr 2)).
    - reflexivity.
    - reflexivity.
    - cbn [twc_stable In]; intuition.
    - cbn [twc_stable In]; intuition discriminate.
    - reflexivity.
    - reflexivity.
    - apply tensor_word_column_source_writes.
    - cbn; intuition discriminate.
    - intros id MEMBER; cbn; intros [SAME|[]]; subst id;
        cbn [twc_stable In]in MEMBER; intuition discriminate.
    - intros j current memory RANGE COUNTER FRAME OBSERVED;
        eapply twc_header; [exact I|exact RANGE|exact COUNTER|exact FRAME|exact OBSERVED].
    - intros j current memory exit last RANGE COUNTER FRAME OBSERVED BODY.
      exact(PRESERVE(@twc_two_columns_accept ge locals)j RANGE current memory exit last COUNTER FRAME OBSERVED BODY).
    - exists 0; split; [change(0<=0<=2); lia|split; [reflexivity|split; [apply temp_agree_refl|exact INITIAL]]].
    - exact SOURCE. }
  destruct CACHED as [MODEL [j [RANGE [COUNTER [FRAME OBSERVED]]]]].
  exists after,final; split; [exact SOURCE|split; assumption].
Qed.

Print Assumptions twc_actual_cached_source.

Definition twc_undefined_check := Sset 108%positive
  (Ederef(Etempvar 999%positive(Tpointer type_int32s noattr))type_int32s).
Theorem twc_empty_skips_undefined_check fe ge locals :
  let temps:=PTree.set 5%positive(Vint Int.zero)(PTree.empty val)in
  let after:=PTree.set 102%positive(Vint Int.zero)(PTree.set 105%positive(Vint Int.zero)temps)in
  exec_stmt fe ge locals temps thp_memory
    (tensor_word_column_scan_code 5%positive 102%positive 105%positive 108%positive twc_undefined_check)
    E0 after thp_memory Out_normal /\ after!999%positive=None /\ after!108%positive=None.
Proof.
  cbn zeta; split.
  - exact(proj1(@tensor_word_column_empty_execution fe ge locals thp_memory
      5%positive 102%positive 105%positive 108%positive twc_undefined_check
      (PTree.set 5%positive(Vint Int.zero)(PTree.empty val))[]
      ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(cbn; tauto)ltac:(cbn; tauto)eq_refl)).
  - split; reflexivity.
Qed.

Print Assumptions twc_empty_skips_undefined_check.
