From Stdlib Require Import List Bool ZArith.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightSameAddress CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryPointerCellComparison GuardMemoryBooleanScan GuardMemoryFootprintCapabilities GuardMemoryFiniteAliasCondition.
From GuardAffineNest Require Import AffineNestScanAddress AffineNestScanAccesses AffineNestScanSyntax AffineNestScanWords.
From GuardInterface Require Import ClightObservedWordProbe ClightStableLoadBody.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** An indexed observation needs no extra pointer temporary. Its expression
    is tied to the actual captured address and raw word by a receipt. *)
Record clight_word_observer := ClightWordObserver {
  word_observer_address : expr;
  word_observer_block : block;
  word_observer_offset : ptrofs;
  word_observer_value : val
}.
Definition word_observer_location observer :=
  MemoryLocation Mint32 (word_observer_block observer) (Ptrofs.unsigned(word_observer_offset observer)).
Definition word_observer_snapshot observer := (word_observer_location observer,word_observer_value observer).
Definition word_observer_receipt ge locals temps memory observer :=
  typeof(word_observer_address observer)=Tpointer type_int32s noattr /\
  eval_expr ge locals temps memory(word_observer_address observer)
    (Vptr(word_observer_block observer)(word_observer_offset observer)) /\
  Mem.loadv Mint32 memory(Vptr(word_observer_block observer)(word_observer_offset observer))=
    Some(word_observer_value observer).

Lemma word_observer_receipt_frame ge locals temps memory observer live current :
  word_observer_receipt ge locals temps memory observer ->
  expression_scope live(word_observer_address observer) -> temp_agree live temps current ->
  word_observer_receipt ge locals current memory observer.
Proof.
  intros [TYPE [EVAL READ]] SCOPE FRAME; split; [exact TYPE|split; [|exact READ]].
  eapply expression_temp_transport; eassumption.
Qed.

Lemma word_observer_receipt_load ge locals temps memory observer :
  word_observer_receipt ge locals temps memory observer ->
  location_load(word_observer_location observer) memory=Some(word_observer_value observer) /\
  (4|location_offset(word_observer_location observer)).
Proof.
  intros [_ [_ READ]].
  cbn [Mem.loadv] in READ.
  destruct(zle(Ptrofs.unsigned(word_observer_offset observer)+size_chunk Mint32)Ptrofs.modulus);
    [|discriminate].
  split; [exact READ|exact(proj2(Mem.load_valid_access _ _ _ _ _ READ))].
Qed.

Theorem observed_word_expression_check_evaluation code locations cell ge locals temps memory observer :
  memory_cell_address_binding code locations(Entry ge locals temps memory) cell ->
  word_observer_receipt ge locals temps memory observer ->
  expression_test(memory_pointer_cells_test(code cell)(word_observer_address observer))
    (Entry ge locals temps memory)(observed_word_cell_check locations(word_observer_location observer) cell).
Proof.
  intros [write [address BINDING]] [OBS_TYPE [OBS_EVAL READ]].
  destruct BINDING as [RESOLVE [CHUNK [OFFSET [PURE [TYPE [EVAL [VALID ALIGN]]]]]]].
  unfold observed_word_cell_check; rewrite RESOLVE.
  unfold observed_word_location_check; cbn [word_observer_location location_block location_offset]; rewrite OFFSET.
  rewrite <-memory_pointer_eq_unsigned.
  eapply memory_pointer_cells_test_evaluation;
    [exact TYPE|exact OBS_TYPE|exact EVAL|exact OBS_EVAL|exact VALID|].
  eapply loaded_address_valid; exact READ.
Qed.

Definition affine_joint_comparisons (observers:list clight_word_observer) (operations:list memory_nary_compute) :=
  flat_map(fun observer=>map(fun operation=>(observer,operation)) operations) observers.
Definition affine_joint_comparison_test values comparison :=
  memory_pointer_cells_test
    (affine_scan_address(memory_nary_access_array(memory_nary_compute_write(snd comparison))) values
      (memory_nary_access_expression(memory_nary_compute_write(snd comparison))))
    (word_observer_address(fst comparison)).
Definition affine_joint_comparison_result locations point comparison :=
  observed_word_cell_check locations(word_observer_location(fst comparison))
    (affine_scan_access_cell point(memory_nary_compute_write(snd comparison))).
Fixpoint affine_joint_comparison_code values flag comparisons := match comparisons with
  | []=>Sskip
  | comparison::rest=>Ssequence(memory_boolean_test_body flag(affine_joint_comparison_test values comparison))
      (affine_joint_comparison_code values flag rest)
  end.
Definition affine_joint_observation_leaf observers operations values flag :=
  affine_joint_comparison_code values flag(affine_joint_comparisons observers operations).
Definition affine_joint_observation_result locations observers operations point :=
  forallb(affine_joint_comparison_result locations point)(affine_joint_comparisons observers operations).

Lemma affine_joint_comparisons_member observers operations observer operation :
  In(observer,operation)(affine_joint_comparisons observers operations) <->
  In observer observers /\ In operation operations.
Proof.
  unfold affine_joint_comparisons; rewrite in_flat_map; split.
  - intros [actual [MEMBER PAIR]]; apply in_map_iff in PAIR as [item [SAME ITEM]].
    inversion SAME; subst; auto.
  - intros [OBSERVER OPERATION]; exists observer; split; [exact OBSERVER|apply in_map; exact OPERATION].
Qed.

(** Each comparison writes only the private Boolean. All comparisons of the
    reached subbody remain licensed even after one result is false. The
    enclosing prefix service controls whether a later source body is scanned. *)
Theorem affine_joint_comparison_execution comparisons fe ge locals memory values flag
  layout point locations public base protected checked good :
  ~In flag protected -> ~In flag public -> ~In flag(map values layout) ->
  temp_agree public base checked -> affine_scan_word_view layout values point checked ->
  checked!flag=Some(memory_boolean_word good) ->
  (forall comparison current, In comparison comparisons -> temp_agree public base current ->
    affine_scan_word_view layout values point current ->
    expression_test(affine_joint_comparison_test values comparison)(Entry ge locals current memory)
      (affine_joint_comparison_result locations point comparison)) ->
  exists after,
    exec_stmt fe ge locals checked memory(affine_joint_comparison_code values flag comparisons) E0 after memory Out_normal /\
    temp_agree protected checked after /\
    after!flag=Some(memory_boolean_word(good&&forallb(affine_joint_comparison_result locations point) comparisons)).
Proof.
  revert checked good; induction comparisons as [|comparison rest IH];
    intros checked good PRIVATE PUBLIC_PRIVATE WORD_PRIVATE FRAME WORDS FLAG TESTS.
  - exists checked; split; [constructor|split; [apply temp_agree_refl|]].
    cbn [forallb]; rewrite andb_true_r; exact FLAG.
  - set(keep:=protected++public++map values layout).
    assert (KEEP_PRIVATE : ~In flag keep) by(unfold keep; repeat rewrite in_app_iff; tauto).
    destruct(@memory_boolean_test_body_execution fe ge locals checked memory flag
      (affine_joint_comparison_test values comparison) good
      (affine_joint_comparison_result locations point comparison) keep
      KEEP_PRIVATE FLAG (TESTS comparison checked (or_introl eq_refl) FRAME WORDS))
      as [middle [FIRST [MIDDLE MID_FLAG]]].
    assert (MID_PUBLIC : temp_agree public base middle).
    { eapply temp_agree_trans; [exact FRAME|eapply temp_agree_weaken; [|exact MIDDLE]].
      unfold keep; intros identifier MEMBER; apply in_or_app; right; apply in_or_app; left; exact MEMBER. }
    assert (MID_WORDS : affine_scan_word_view layout values point middle).
    { eapply affine_scan_word_view_frame; [apply incl_refl| |exact WORDS].
      eapply temp_agree_weaken; [|exact MIDDLE].
      unfold keep; intros identifier MEMBER; apply in_or_app; right; apply in_or_app; right; exact MEMBER. }
    destruct(@IH middle(good&&affine_joint_comparison_result locations point comparison)
      PRIVATE PUBLIC_PRIVATE WORD_PRIVATE MID_PUBLIC MID_WORDS MID_FLAG
      (fun next current MEMBER=>TESTS next current(or_intror MEMBER))) as [after [REST [AFTER RESULT]]].
    exists after; split.
    + cbn [affine_joint_comparison_code]; eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); eassumption.
    + split.
      * eapply temp_agree_trans; [eapply temp_agree_weaken; [|exact MIDDLE]|exact AFTER].
        unfold keep; intros identifier MEMBER; apply in_or_app; left; exact MEMBER.
      * cbn [forallb] in RESULT |- *; rewrite andb_assoc; exact RESULT.
Qed.

Print Assumptions word_observer_receipt_frame.
Print Assumptions word_observer_receipt_load.
Print Assumptions observed_word_expression_check_evaluation.
Print Assumptions affine_joint_comparisons_member.
Print Assumptions affine_joint_comparison_execution.
