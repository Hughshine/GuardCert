From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Cop Clight ClightBigstep.
From Guard Require Import ClightCondition ClightCountedLoop ClightNoWrap ClightTempFrame
  ClightTempFootprint ClightLoopExecution ClightLoopSyntax ClightRectangularLoops ClightRegionProgress
  ClightFrontendLoopProtocol ClightRedundantSet CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryBooleanScan.
From GuardInterface Require Import ClightTensorWordOuter ClightTensorWordOuterHeaders ClightTensorWordColumn ClightTensorWordColumnExample
  ClightWordComponentScanExample ClightTensorHeaderPointExample ClightConstantBoundModel
  ClightDirectWordObservation ClightAffineJointObservation ClightObservedHeaderPrefix
  ClightLoadedOffsetHeader ClightSignedIndexedOffsetHeader ClightSignedExpressionProgress ClightStrictLoopProgress
  ClightStrictIteration ClightDualLoadedUnitSyntax ClightNestedExpressionCapture ClightNestedExpressionTransport ClightWordObservationControl
  ClightExpressionHeaderCapture CompCertWordObservation CompCertTensorWordStoreChoices ClightCheckPlanFrame
  ClightNestedConstantSite ClightNestedConstantHeaders.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The source has two independently loaded bounds. Its addresses use the
    existing wrapping parameter product; this fixture keeps addresses equal
    across rows/columns to exercise header-alias changes in the original path. *)
Definition two_root := signed_load_offset 11%positive(Int.repr 2).
Definition two_body := nested_expression_body 2%positive twc_bound twc_component.
Definition two_source := nested_expression_source 12%positive two_root 2%positive twc_bound twc_component.
Definition two_temps base := PTree.set 12%positive(Vint Int.zero)
  (PTree.set 4%positive(Vint(Int.repr 2))(twc_temps base)).
Definition two_stable := 4%positive::twc_stable.
Definition two_live := 12%positive::2%positive::3%positive::two_stable.
Definition two_rename id := if Pos.eqb id 12%positive then 112%positive else twc_rename id.
Definition two_entry ge locals base := Entry ge locals(two_temps base)thp_memory.
Definition two_scan := tensor_word_outer_statement 4%positive 5%positive 10%positive
  112%positive 114%positive 102%positive 105%positive 103%positive 104%positive 108%positive
  wcs_index 5 two_rename thp_observers.
Definition two_flag ge locals base := @tensor_word_outer_result(two_entry ge locals base)
  12%positive 2%positive 4%positive 5%positive 10%positive 112%positive 114%positive
  102%positive 105%positive 103%positive wcs_index 5 two_rename thp_observers.

Lemma two_body_writes : writes_only[2%positive;3%positive]two_body.
Proof.
  unfold two_body,nested_expression_body,twc_component,constant_body_source,
    rectangle_reset,strict_frontend_loop,counter_increment,wcs_body,direct_word_store.
  repeat first [apply writes_sequence|apply writes_if|apply writes_loop|
    apply writes_set; cbn; intuition|constructor].
Qed.
Lemma two_body_stores fe ge locals temps memory after final :
  exec_stmt fe ge locals temps memory two_body E0 after final Out_normal -> constant_word_stores(Int.repr 7)memory final.
Proof.
  intro SOURCE; eapply checked_constant_word_control_execution; [exact SOURCE|vm_compute; reflexivity].
Qed.
Lemma two_body_execution fe ge locals temps memory base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) ->
  temps!1%positive=Some(Vint(Int.repr 2)) -> temps!6%positive=Some(Vint(Int.repr Int.max_signed)) ->
  temps!10%positive=Some(Vptr 1%positive base) -> temps!11%positive=Some(Vptr 1%positive Ptrofs.zero) ->
  (Mem.load Mint32 memory 1%positive 4=Some(Vint Int.zero) \/ Mem.load Mint32 memory 1%positive 4=Some(Vint(Int.repr 7))) ->
  (forall k,0<=k<5 -> Mem.valid_access memory Mint32 1%positive(Ptrofs.unsigned(wcs_offset base k))Writable) ->
  exists after final,exec_stmt fe ge locals temps memory two_body E0 after final Out_normal.
Proof.
  intros BASE PARAMETER STRIDE POINTER HEADER CHILD ACCESS.
  destruct(@twc_source_tail 9%nat fe ge locals(PTree.set 2%positive(Vint Int.zero)temps)memory base 0
    BASE ltac:(lia)eq_refl
    ltac:(rewrite PTree.gso by discriminate; exact PARAMETER)
    ltac:(rewrite PTree.gso by discriminate; exact STRIDE)
    ltac:(rewrite PTree.gso by discriminate; exact POINTER)
    ltac:(rewrite PTree.gso by discriminate; exact HEADER)(PTree.gss _ _ _)CHILD ACCESS)
    as [after [final SOURCE]].
  exists after,final; unfold two_body,nested_expression_body.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|exact SOURCE].
Qed.

Lemma two_original_tail count : forall fe ge locals temps memory base i,
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> 0<=i -> i+Z.of_nat count=9 ->
  temps!1%positive=Some(Vint(Int.repr 2)) -> temps!6%positive=Some(Vint(Int.repr Int.max_signed)) ->
  temps!10%positive=Some(Vptr 1%positive base) -> temps!11%positive=Some(Vptr 1%positive Ptrofs.zero) ->
  temps!12%positive=Some(Vint(Int.repr i)) ->
  (Mem.load Mint32 memory 1%positive 0=Some(Vint Int.zero) \/ Mem.load Mint32 memory 1%positive 0=Some(Vint(Int.repr 7))) ->
  (Mem.load Mint32 memory 1%positive 4=Some(Vint Int.zero) \/ Mem.load Mint32 memory 1%positive 4=Some(Vint(Int.repr 7))) ->
  (forall k,0<=k<5 -> Mem.valid_access memory Mint32 1%positive(Ptrofs.unsigned(wcs_offset base k))Writable) ->
  exists after final,exec_stmt fe ge locals temps memory two_source E0 after final Out_normal.
Proof.
  induction count as [|count IH]; intros fe ge locals temps memory base i BASE NONNEG LENGTH PARAMETER STRIDE POINTER HEADER ROW ROOT CHILD ACCESS.
  all: assert(SIGNED:signed_range i)by(change(-2147483648<=i<=2147483647); try rewrite Nat2Z.inj_succ in LENGTH; lia).
  - cbn in LENGTH; replace i with 9 in * by lia; exists temps,memory; unfold two_source,nested_expression_source.
    apply signed_expression_zero_trip_execution.
    destruct ROOT as [ROOT|ROOT]; [change false with(Int.lt(Int.repr 9)(Int.repr 2))|change false with(Int.lt(Int.repr 9)(Int.repr 9))].
    all: apply signed_expression_test_eval; [reflexivity|exact ROW|].
    + change(eval_expr ge locals temps memory two_root(Vint(Int.add Int.zero(Int.repr 2)))).
      eapply signed_load_offset_eval; [exact HEADER|exact ROOT].
    + change(eval_expr ge locals temps memory two_root(Vint(Int.add(Int.repr 7)(Int.repr 2)))).
      eapply signed_load_offset_eval; [exact HEADER|exact ROOT].
  - assert(RANGE:0<=i<9)by(rewrite Nat2Z.inj_succ in LENGTH; lia).
    assert(BOUND:exists upper,(upper=2 \/ upper=9) /\ eval_expr ge locals temps memory two_root(Vint(Int.repr upper))).
    { destruct ROOT as [ROOT|ROOT]; [exists 2|exists 9]; split; [left; reflexivity| |right; reflexivity|].
      - change(eval_expr ge locals temps memory two_root(Vint(Int.add Int.zero(Int.repr 2)))).
        eapply signed_load_offset_eval; [exact HEADER|exact ROOT].
      - change(eval_expr ge locals temps memory two_root(Vint(Int.add(Int.repr 7)(Int.repr 2)))).
        eapply signed_load_offset_eval; [exact HEADER|exact ROOT]. }
    destruct BOUND as [upper [SHAPE EVAL]]; destruct(Z_lt_ge_dec i upper)as [ACTIVE|STOP].
    + destruct(@two_body_execution fe ge locals temps memory base BASE PARAMETER STRIDE POINTER HEADER CHILD ACCESS)
        as [middle [next BODY]].
      pose proof(two_body_stores BODY)as STORES.
      assert(FRAME:temp_agree[12%positive;1%positive;6%positive;10%positive;11%positive]temps middle).
      { eapply structured_temp_frame; [exact two_body_writes| |exact BODY].
        intros id MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[SAME|[SAME|[SAME|[SAME|[]]]]]]; subst id;
          cbn; intuition discriminate. }
      assert(ROOT_NEXT:Mem.load Mint32 next 1%positive 0=Some(Vint Int.zero) \/ Mem.load Mint32 next 1%positive 0=Some(Vint(Int.repr 7))).
      { destruct ROOT as [ZERO|SEVEN].
        - eapply tensor_constant_word_stores_observation_choices; eassumption.
        - right; eapply constant_word_stores_preserve_observation; eassumption. }
      assert(CHILD_NEXT:Mem.load Mint32 next 1%positive 4=Some(Vint Int.zero) \/ Mem.load Mint32 next 1%positive 4=Some(Vint(Int.repr 7))).
      { destruct CHILD as [ZERO|SEVEN].
        - eapply tensor_constant_word_stores_observation_choices; eassumption.
        - right; eapply constant_word_stores_preserve_observation; eassumption. }
      destruct(IH fe ge locals(PTree.set 12%positive(Vint(Int.repr(i+1)))middle)next base(i+1))as [after [final REST]].
      * exact BASE.
      * lia.
      * rewrite Nat2Z.inj_succ in LENGTH; lia.
      * rewrite PTree.gso by discriminate; rewrite FRAME by(cbn; intuition); exact PARAMETER.
      * rewrite PTree.gso by discriminate; rewrite FRAME by(cbn; intuition); exact STRIDE.
      * rewrite PTree.gso by discriminate; rewrite FRAME by(cbn; intuition); exact POINTER.
      * rewrite PTree.gso by discriminate; rewrite FRAME by(cbn; intuition); exact HEADER.
      * apply PTree.gss.
      * exact ROOT_NEXT.
      * exact CHILD_NEXT.
      * intros k POINT; eapply tensor_constant_word_stores_permissions_forward; [exact STORES|apply ACCESS; exact POINT].
      * exists after,final; unfold two_source,nested_expression_source; eapply strict_iteration_encode with(body_temps:=middle)(body_memory:=next).
        -- assert(LT:Int.lt(Int.repr i)(Int.repr upper)=true).
           { unfold Int.lt; rewrite !Int.signed_repr; try exact SIGNED;
               try(destruct SHAPE as [->| ->]; change(-2147483648<=2<=2147483647) || change(-2147483648<=9<=2147483647); lia).
             destruct(zlt i upper); [reflexivity|lia]. }
           rewrite <-LT; apply signed_expression_test_eval; [reflexivity|exact ROW|exact EVAL].
        -- exists(Int.repr i); split; [rewrite FRAME by(cbn; intuition); exact ROW|
             rewrite Int.signed_repr by exact SIGNED; change Int.max_signed with 2147483647; lia].
        -- exact BODY.
        -- rewrite(@counter_increment_small 12%positive middle i ltac:(rewrite FRAME by(cbn; intuition); exact ROW)); exact REST.
    + exists temps,memory; unfold two_source,nested_expression_source; apply signed_expression_zero_trip_execution.
      assert(LT:Int.lt(Int.repr i)(Int.repr upper)=false).
      { unfold Int.lt; rewrite !Int.signed_repr; try exact SIGNED;
          try(destruct SHAPE as [->| ->]; change(-2147483648<=2<=2147483647) || change(-2147483648<=9<=2147483647); lia).
        destruct(zlt i upper); [lia|reflexivity]. }
      rewrite <-LT; apply signed_expression_test_eval; [reflexivity|exact ROW|exact EVAL].
Qed.

Theorem two_original_complete fe ge locals base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> exists after final,
    exec_stmt fe ge locals(two_temps base)thp_memory two_source E0 after final Out_normal.
Proof.
  intro BASE; eapply(@two_original_tail 9%nat fe ge locals(two_temps base)thp_memory base 0);
    try(reflexivity || lia).
  - exact BASE.
  - left; exact(proj1 thp_header_reads).
  - left; exact(proj2 thp_header_reads).
  - apply wcs_access; exact BASE.
Qed.

Lemma two_observers ge locals base : Forall(word_observer_receipt ge locals(two_temps base)thp_memory)thp_observers.
Proof.
  pose proof(@twc_observers ge locals base)as READS; rewrite Forall_forall in READS|-*.
  intros observer MEMBER; eapply word_observer_receipt_frame with(live:=[11%positive]);
    [apply READS; exact MEMBER| |].
  - cbn [thp_observers]in MEMBER; destruct MEMBER as [SAME|[SAME|[]]]; subst observer;
      change(incl[11%positive][11%positive]); intros id KEY; exact KEY.
  - intros id KEY; cbn in KEY; destruct KEY as [SAME|[]]; subst id; reflexivity.
Qed.

Lemma two_root_header ge locals base i current memory :
  True -> 0<=i<=2 -> current!12%positive=Some(Vint(Int.repr i)) ->
  temp_agree two_stable(two_temps base)current -> header_observations_match(map word_observer_snapshot thp_observers)memory ->
  eval_expr ge locals current memory two_root(Vint(Int.repr 2)).
Proof.
  intros _ RANGE ROW FRAME OBSERVED.
  change(eval_expr ge locals current memory two_root(Vint(Int.add Int.zero(Int.repr 2)))).
  eapply signed_load_offset_eval.
  - rewrite FRAME by(cbn [two_stable twc_stable In]; intuition); reflexivity.
  - exact(Forall_inv OBSERVED).
Qed.
Lemma two_child_header ge locals base i j current memory :
  0<=i<2 -> 0<=j<=2 -> current!12%positive=Some(Vint(Int.repr i)) -> current!2%positive=Some(Vint(Int.repr j)) ->
  temp_agree two_stable(two_temps base)current -> header_observations_match(map word_observer_snapshot thp_observers)memory ->
  eval_expr ge locals current memory twc_bound(Vint(Int.repr 2)).
Proof.
  intros ROWS COLUMNS ROW COLUMN FRAME OBSERVED.
  change(eval_expr ge locals current memory twc_bound(Vint(Int.add Int.zero(Int.repr 2)))).
  eapply signed_indexed_offset_eval.
  - rewrite FRAME by(cbn [two_stable twc_stable In]; intuition); reflexivity.
  - exact(Forall_inv(Forall_inv_tail OBSERVED)).
Qed.

Example two_twenty_points_accept ge locals : two_flag ge locals(Ptrofs.repr 16)=true.
Proof. vm_compute; reflexivity. Qed.
Example two_first_row_refuses ge locals : two_flag ge locals(Ptrofs.repr(-20))=false.
Proof. vm_compute; reflexivity. Qed.

Lemma two_initial (ge:genv)(locals:env)(base:Ptrofs.int) : header_observations_match(map word_observer_snapshot thp_observers)thp_memory.
Proof.
  unfold header_observations_match; rewrite Forall_map.
  eapply Forall_impl; [|exact(@two_observers ge locals base)].
  intros observer RECEIPT; exact(proj1(word_observer_receipt_load RECEIPT)).
Qed.

Definition two_shape := NestedConstantShape 12%positive 2%positive 3%positive
  4%positive 5%positive 51%positive 50%positive 5 wcs_body 11%positive Int.one(Int.repr 2)(Int.repr 2).
Lemma two_receipt ge locals base : ncs_observation_receipt two_shape(two_entry ge locals base)thp_observers.
Proof.
  constructor.
  - split.
    + exists 1%positive,Ptrofs.zero,Int.zero; split; [reflexivity|split; [exact(proj1 thp_header_reads)|reflexivity]].
    + exists 1%positive,Ptrofs.zero,Int.zero; split; [reflexivity|split; [exact(proj2 thp_header_reads)|reflexivity]].
  - exact(@two_observers ge locals base).
  - reflexivity.
  - unfold ncs_observations,loaded_offset_observations,indexed_offset_observations.
    change(map word_observer_snapshot thp_observers=
      (match Mem.loadv Mint32 thp_memory(Vptr 1%positive Ptrofs.zero)with
       | Some value=>[(MemoryLocation Mint32 1%positive 0,value)]|None=>[]end)++
      (match Mem.loadv Mint32 thp_memory(Vptr 1%positive(Ptrofs.repr 4))with
       | Some value=>[(MemoryLocation Mint32 1%positive 4,value)]|None=>[]end)).
    rewrite(proj1 thp_header_reads),(proj2 thp_header_reads); reflexivity.
  - exact(@two_initial ge locals base).
Qed.

Lemma two_scan_uses_templates : two_scan=tensor_word_header_scan two_shape 10%positive
  112%positive 114%positive 102%positive 105%positive 103%positive 104%positive 108%positive wcs_index two_rename.
Proof. reflexivity. Qed.

(** The scan is executed from the actual entry, and the accepted cached source
    is executed from the actual scan exit. Neither execution is a premise. *)
Theorem two_actual_source_scan fe ge locals base :
  (base=Ptrofs.repr 16 \/ base=Ptrofs.repr(-20)) -> exists source_after final checked,
    exec_stmt fe ge locals(two_temps base)thp_memory two_source E0 source_after final Out_normal /\
    exec_stmt fe ge locals(two_temps base)thp_memory two_scan E0 checked thp_memory Out_normal /\
    temp_agree two_live(two_temps base)checked /\
    checked!108%positive=Some(memory_boolean_word(two_flag ge locals base)) /\
    (two_flag ge locals base=true -> exists exit,
      exec_stmt fe ge locals checked thp_memory
        (nested_cached_source 12%positive 4%positive 2%positive 5%positive twc_component)E0 exit final Out_normal /\
      temp_agree two_live source_after exit /\ header_observations_match(map word_observer_snapshot thp_observers)final).
Proof.
  intro BASE; destruct(@two_original_complete fe ge locals base BASE)as [source_after [final SOURCE]].
  exists source_after,final.
  assert(SCAN:exists checked,
    exec_stmt fe ge locals(two_temps base)thp_memory two_scan E0 checked thp_memory Out_normal /\
    temp_agree two_live(two_temps base)checked /\
    checked!108%positive=Some(memory_boolean_word(two_flag ge locals base)) /\
    (two_flag ge locals base=true -> exists exit,
      exec_stmt fe ge locals checked thp_memory
        (nested_cached_source 12%positive 4%positive 2%positive 5%positive twc_component)E0 exit final Out_normal /\
      temp_agree two_live source_after exit /\ header_observations_match(map word_observer_snapshot thp_observers)final)).
  { eapply(@tensor_word_header_scan_at_exit fe two_shape(two_entry ge locals base)10%positive
      112%positive 114%positive 102%positive 105%positive 103%positive 104%positive 108%positive
      wcs_index wcs_rhs two_rename two_stable two_live thp_observers(@two_receipt ge locals base))
      with(current:=two_temps base)(after:=source_after)(final:=final).
    all: try(reflexivity || discriminate || exact wcs_word || lia || exact I || exact SOURCE).
    all: try solve[change(-2147483648<=5<=2147483647); lia].
    all: try solve[cbn [two_stable two_live twc_stable In]; intuition discriminate].
    all: try solve[exact(@two_root_header ge locals base)].
    all: try solve[exact(@two_child_header ge locals base)].
    all: try solve[intro ACTIVE; exact(@two_observers ge locals base)].
    all: try solve[intro ACTIVE; exists(Int.repr 2); reflexivity].
    all: try solve[exists(Int.repr 2); reflexivity].
    all: try solve[exact(@two_initial ge locals base)].
    all: try solve[apply temp_agree_refl].
    all: try solve[intros id MEMBER; cbn [two_stable twc_stable In]in MEMBER;
      destruct MEMBER as [SAME|[SAME|[SAME|[SAME|[SAME|[SAME|[SAME|[]]]]]]]]; subst id; reflexivity].
    all: try solve[change(incl[1%positive;6%positive;3%positive](3%positive::2%positive::12%positive::two_stable));
      intros id MEMBER; cbn [two_stable twc_stable In]in MEMBER|-*; intuition].
    all: try solve[change(incl two_stable two_live); intros id MEMBER; right; right; right; exact MEMBER].
    all: try solve[intros observer MEMBER; cbn [thp_observers In]in MEMBER;
      destruct MEMBER as [SAME|[SAME|[]]]; subst observer; change(incl[11%positive]two_live);
      intros id KEY; cbn [two_live two_stable twc_stable In]in KEY|-*; intuition].
    all: try solve[vm_compute; intuition discriminate]. }
  destruct SCAN as [checked [RUN [PUBLIC [FLAG CACHED]]]].
  exists checked; split; [exact SOURCE|split; [exact RUN|split; [exact PUBLIC|split; assumption]]].
Qed.

Theorem two_actual_accepted_cached fe ge locals : exists source_after final checked exit,
  exec_stmt fe ge locals(two_temps(Ptrofs.repr 16))thp_memory two_source E0 source_after final Out_normal /\
  exec_stmt fe ge locals(two_temps(Ptrofs.repr 16))thp_memory two_scan E0 checked thp_memory Out_normal /\
  checked!108%positive=Some(memory_boolean_word true) /\
  exec_stmt fe ge locals checked thp_memory
    (nested_cached_source 12%positive 4%positive 2%positive 5%positive twc_component)E0 exit final Out_normal /\
  temp_agree two_live source_after exit /\ header_observations_match(map word_observer_snapshot thp_observers)final.
Proof.
  destruct(@two_actual_source_scan fe ge locals(Ptrofs.repr 16)ltac:(left; reflexivity))
    as [source_after [final [checked [SOURCE [SCAN [PUBLIC [FLAG SOUND]]]]]]].
  destruct(SOUND(@two_twenty_points_accept ge locals))as [exit [CACHED [EXIT OBSERVED]]].
  rewrite two_twenty_points_accept in FLAG.
  exists source_after,final,checked,exit; split; [exact SOURCE|split; [exact SCAN|split; [exact FLAG|split; [exact CACHED|split; assumption]]]].
Qed.

Theorem two_actual_alias_refusal fe ge locals : exists source_after final checked,
  exec_stmt fe ge locals(two_temps(Ptrofs.repr(-20)))thp_memory two_source E0 source_after final Out_normal /\
  exec_stmt fe ge locals(two_temps(Ptrofs.repr(-20)))thp_memory two_scan E0 checked thp_memory Out_normal /\
  temp_agree two_live(two_temps(Ptrofs.repr(-20)))checked /\
  checked!108%positive=Some(memory_boolean_word false).
Proof.
  destruct(@two_actual_source_scan fe ge locals(Ptrofs.repr(-20))ltac:(right; reflexivity))
    as [source_after [final [checked [SOURCE [SCAN [PUBLIC [FLAG SOUND]]]]]]].
  rewrite two_first_row_refuses in FLAG.
  exists source_after,final,checked; split; [exact SOURCE|split; [exact SCAN|split; assumption]].
Qed.

Definition two_undefined_row := Sset 108%positive
  (Ederef(Etempvar 999%positive(Tpointer type_int32s noattr))type_int32s).
Theorem two_empty_skips_undefined_child fe ge locals :
  let temps:=PTree.set 4%positive(Vint Int.zero)(PTree.empty val)in
  let after:=PTree.set 112%positive(Vint Int.zero)
    (PTree.set 108%positive(memory_boolean_word true)(PTree.set 114%positive(Vint Int.zero)temps))in
  exec_stmt fe ge locals temps thp_memory
    (tensor_word_outer_scan_code 4%positive 112%positive 114%positive 108%positive two_undefined_row)
    E0 after thp_memory Out_normal /\ after!5%positive=None /\ after!999%positive=None /\
    after!108%positive=Some(memory_boolean_word true).
Proof.
  cbn zeta; split.
  - exact(proj1(@tensor_word_outer_empty_execution fe ge locals thp_memory
      4%positive 112%positive 114%positive 108%positive two_undefined_row
      (PTree.set 4%positive(Vint Int.zero)(PTree.empty val))[]
      ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
      ltac:(cbn; tauto)ltac:(cbn; tauto)ltac:(cbn; tauto)eq_refl)).
  - repeat split; reflexivity.
Qed.

Definition two_refusing_row := Sifthenelse
  (Ebinop Oeq(Etempvar 112%positive type_int32s)(Econst_int Int.zero type_int32s)type_int32s)
  (Sset 108%positive(Econst_int Int.zero type_int32s))two_undefined_row.
Theorem two_refusal_skips_unlicensed_future fe ge locals :
  let temps:=PTree.set 4%positive(Vint(Int.repr 2))(PTree.empty val)in
  let initialized:=PTree.set 112%positive(Vint Int.zero)
    (PTree.set 108%positive(memory_boolean_word true)(PTree.set 114%positive(Vint(Int.repr 2))temps))in
  let after:=PTree.set 108%positive(memory_boolean_word false)initialized in
  exec_stmt fe ge locals temps thp_memory
    (tensor_word_outer_scan_code 4%positive 112%positive 114%positive 108%positive two_refusing_row)
    E0 after thp_memory Out_normal /\ after!112%positive=Some(Vint Int.zero) /\ after!999%positive=None.
Proof.
  cbn zeta.
  set(temps:=PTree.set 4%positive(Vint(Int.repr 2))(PTree.empty val)).
  set(initialized:=PTree.set 112%positive(Vint Int.zero)
    (PTree.set 108%positive(memory_boolean_word true)(PTree.set 114%positive(Vint(Int.repr 2))temps))).
  set(after:=PTree.set 108%positive(memory_boolean_word false)initialized).
  assert(BODY:exec_stmt fe ge locals initialized thp_memory two_refusing_row E0 after thp_memory Out_normal).
  { unfold two_refusing_row; eapply exec_Sifthenelse with(v1:=Vint Int.one)(b:=true).
    - eapply eval_Ebinop; [constructor; reflexivity|constructor|reflexivity].
    - reflexivity.
    - constructor; constructor. }
  assert(REFUSAL:exec_stmt fe ge locals temps thp_memory
    (tensor_word_outer_scan_code 4%positive 112%positive 114%positive 108%positive two_refusing_row)
    E0 after thp_memory Out_normal /\ after!112%positive=Some(Vint Int.zero)).
  { eapply(@tensor_word_outer_first_refusal fe ge locals thp_memory
      4%positive 112%positive 114%positive 108%positive two_refusing_row temps(Int.repr 2)after).
    - discriminate.
    - discriminate.
    - discriminate.
    - reflexivity.
    - change(0<2); lia.
    - exact BODY.
    - apply temp_agree_set; cbn; intuition discriminate.
    - apply PTree.gss. }
  split; [exact(proj1 REFUSAL)|split; [exact(proj2 REFUSAL)|reflexivity]].
Qed.

Print Assumptions two_body_writes.
Print Assumptions two_body_stores.
Print Assumptions two_body_execution.
Print Assumptions two_original_tail.
Print Assumptions two_original_complete.
Print Assumptions two_observers.
Print Assumptions two_root_header.
Print Assumptions two_child_header.
Print Assumptions two_twenty_points_accept.
Print Assumptions two_first_row_refuses.
Print Assumptions two_initial.
Print Assumptions two_receipt.
Print Assumptions two_scan_uses_templates.
Print Assumptions two_actual_source_scan.
Print Assumptions two_actual_accepted_cached.
Print Assumptions two_actual_alias_refusal.
Print Assumptions two_empty_skips_undefined_child.
Print Assumptions two_refusal_skips_unlicensed_future.
