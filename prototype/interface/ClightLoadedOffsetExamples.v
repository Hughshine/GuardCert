From Stdlib Require Import List ZArith Lia.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Ctypes Clight ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightTempFootprint ClightCountedLoop ClightLoopSyntax ClightNoWrap.
From GuardAffineNest Require Import AffineNestGuardPackage AffineNestPackageGuard AffineNestPackageExamples AffineNestDomainGuard.
From GuardInterface Require Import ClightSignedExpressionProgress ClightStrictLoopProgress ClightStrictIteration
  ClightExpressionHeaderCapture ClightExpressionAffineNumericSite ClightLoadedOffsetHeader
  ClightLoadedAffineNumericExamples ClightLoadedBodyPrefixExamples.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition lof_bound := signed_load_offset 11%positive Int.one.
Definition lof_source := expression_affine_numeric_source lof_bound lnf_proposal.
Definition lof_describe source live bound := check_expression_affine_numeric_site source
  affine_memory_example_parameters live lnf_proposal bound.

Example offset_three_level_numeric_site_selected : lnf_present(lof_describe lof_source lnf_live lof_bound)=true.
Proof. vm_compute; reflexivity. Qed.
Example offset_wrong_delta_refused :
  lnf_present(lof_describe lof_source lnf_live (signed_load_offset 11%positive Int.zero))=false.
Proof. vm_compute; reflexivity. Qed.
Example offset_wrong_pointer_refused :
  lnf_present(lof_describe lof_source lnf_live (signed_load_offset 12%positive Int.one))=false.
Proof. vm_compute; reflexivity. Qed.
Example offset_cache_cannot_be_public : lnf_present(lof_describe lof_source (4%positive::lnf_live) lof_bound)=false.
Proof. vm_compute; reflexivity. Qed.
Example unsigned_expression_header_refused :
  lnf_present(lof_describe lof_source lnf_live (Econst_int Int.one (Tint I32 Unsigned noattr)))=false.
Proof. vm_compute; reflexivity. Qed.
Example offset_source_progress_selected : signed_expression_region_progress_supported lof_source=true.
Proof. vm_compute; reflexivity. Qed.
Example load_plus_one_wraps_before_comparison : Int.add (Int.repr 2147483647) Int.one=Int.repr (-2147483648).
Proof. apply Int.same_if_eq; vm_compute; reflexivity. Qed.
Example load_minus_one_retains_machine_wrap : Int.add (Int.repr (-2147483648)) (Int.repr (-1))=Int.repr 2147483647.
Proof. apply Int.same_if_eq; vm_compute; reflexivity. Qed.

Definition lof_site : expression_affine_numeric_site lof_source affine_memory_example_parameters lnf_live lnf_proposal lof_bound.
Proof.
  destruct (lof_describe lof_source lnf_live lof_bound) as [site|] eqn:SELECT; [exact site|].
  pose proof offset_three_level_numeric_site_selected as PRESENT; rewrite SELECT in PRESENT; discriminate.
Defined.

(** A real loaded-plus-one source with no first body. Child parameters and
    data pointers are absent; capture must evaluate only the reached header. *)
Theorem offset_empty_capture_and_check_execute fe ge locals memory block offset raw :
  Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint raw) ->
  Int.signed(Int.add raw Int.one)<=0 ->
  exists checked,
    exec_stmt fe ge locals (lnf_empty_temps block offset) memory (expression_numeric_check_code lof_site)
      E0 checked memory Out_normal /\
    temp_agree lnf_live (lnf_empty_temps block offset) checked /\
    checked!4%positive=Some(Vint(Int.add raw Int.one)) /\ checked!107%positive=Some(Vint Int.zero) /\
    checked!7%positive=None /\ checked!8%positive=None /\ checked!9%positive=None /\ checked!10%positive=None.
Proof.
  intros READ NONPOSITIVE.
  assert (SOURCE : exec_stmt fe ge locals (lnf_empty_temps block offset) memory lof_source
    E0 (lnf_empty_temps block offset) memory Out_normal).
  { apply signed_expression_zero_trip_execution.
    assert (FLAG : Int.lt Int.zero (Int.add raw Int.one)=false).
    { unfold Int.lt; change (Int.signed Int.zero) with 0; destruct (zlt 0 (Int.signed(Int.add raw Int.one))); [lia|reflexivity]. }
    rewrite <-FLAG; apply signed_expression_test_eval; [reflexivity|reflexivity|].
    apply signed_load_offset_eval with (block:=block) (offset:=offset); [reflexivity|exact READ]. }
  destruct (@expression_numeric_site_execution _ _ _ _ _ lof_site fe ge locals (lnf_empty_temps block offset)
    memory _ _ SOURCE) as [word [checked [RUN [PUBLIC [CACHE [FLAG [MATH EVAL]]]]]]].
  assert (CAPTURED : word=Int.add raw Int.one).
  { destruct (signed_load_offset_inv EVAL) as [other [address [observed [POINTER [LOAD VALUE]]]]].
    change ((lnf_empty_temps block offset)!11%positive=Some(Vptr other address)) in POINTER.
    change (Some(Vptr block offset)=Some(Vptr other address)) in POINTER.
    injection POINTER as BLOCK OFFSET; subst other address; assert (RAW : observed=raw) by congruence; subst observed; exact VALUE. }
  subst word.
  change (checked!4%positive=Some(Vint(Int.add raw Int.one))) in CACHE.
  change (checked!107%positive=Some(Vint(if affine_package_guard_flag affine_memory_example_parameters lnf_proposal
    (Entry ge locals (PTree.set 4%positive(Vint(Int.add raw Int.one))(lnf_empty_temps block offset)) memory)
    then Int.one else Int.zero))) in FLAG.
  assert (REFUSES : affine_package_guard_flag affine_memory_example_parameters lnf_proposal
    (Entry ge locals (PTree.set 4%positive (Vint(Int.add raw Int.one)) (lnf_empty_temps block offset)) memory)=false).
  { assert (ROOT : Int.lt Int.zero (Int.add raw Int.one)=false).
    { unfold Int.lt; change (Int.signed Int.zero) with 0; destruct (zlt 0 (Int.signed(Int.add raw Int.one))); [lia|reflexivity]. }
    unfold affine_package_guard_flag,affine_domain_guard_flag.
    cbn -[Int.lt Int.add].
    assert (ROW_WORD : temp_word 1%positive (PTree.set 4%positive(Vint(Int.add raw Int.one))(lnf_empty_temps block offset))=Int.zero)
      by reflexivity.
    assert (CACHE_WORD : temp_word 4%positive (PTree.set 4%positive(Vint(Int.add raw Int.one))(lnf_empty_temps block offset))=Int.add raw Int.one)
      by reflexivity.
    rewrite ROW_WORD,CACHE_WORD,ROOT; reflexivity. }
  rewrite REFUSES in FLAG.
  exists checked; split; [exact RUN|split; [exact PUBLIC|split; [exact CACHE|split; [exact FLAG|]]]].
  repeat split; rewrite PUBLIC by (vm_compute; tauto); reflexivity.
Qed.

Theorem offset_negative_one_zero_trip_check fe ge locals memory block offset :
  Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint(Int.repr(-1))) -> exists checked,
  exec_stmt fe ge locals (lnf_empty_temps block offset) memory (expression_numeric_check_code lof_site)
    E0 checked memory Out_normal /\ checked!4%positive=Some(Vint Int.zero) /\ checked!107%positive=Some(Vint Int.zero).
Proof.
  intro READ; destruct (@offset_empty_capture_and_check_execute fe ge locals memory block offset (Int.repr(-1))
    READ ltac:(change (0<=0); lia)) as [checked [RUN [PUBLIC [CACHE [FLAG REST]]]]].
  assert (WORD : Int.add(Int.repr(-1)) Int.one=Int.zero) by (apply Int.same_if_eq; vm_compute; reflexivity).
  rewrite WORD in CACHE; exists checked; split; [exact RUN|split; [exact CACHE|exact FLAG]].
Qed.

Theorem offset_overflow_zero_trip_check fe ge locals memory block offset :
  Mem.loadv Mint32 memory (Vptr block offset)=Some(Vint(Int.repr 2147483647)) -> exists checked,
  exec_stmt fe ge locals (lnf_empty_temps block offset) memory (expression_numeric_check_code lof_site)
    E0 checked memory Out_normal /\
    checked!4%positive=Some(Vint(Int.repr(-2147483648))) /\ checked!107%positive=Some(Vint Int.zero).
Proof.
  intro READ; destruct (@offset_empty_capture_and_check_execute fe ge locals memory block offset (Int.repr 2147483647)
    READ ltac:(change (-2147483648<=0); lia)) as [checked [RUN [PUBLIC [CACHE [FLAG REST]]]]].
  rewrite load_plus_one_wraps_before_comparison in CACHE.
  exists checked; split; [exact RUN|split; [exact CACHE|exact FLAG]].
Qed.

Print Assumptions offset_three_level_numeric_site_selected.
Print Assumptions offset_wrong_delta_refused.
Print Assumptions offset_wrong_pointer_refused.
Print Assumptions offset_cache_cannot_be_public.
Print Assumptions unsigned_expression_header_refused.
Print Assumptions offset_source_progress_selected.
Print Assumptions load_plus_one_wraps_before_comparison.
Print Assumptions load_minus_one_retains_machine_wrap.
Print Assumptions offset_empty_capture_and_check_execute.
Print Assumptions offset_negative_one_zero_trip_check.
Print Assumptions offset_overflow_zero_trip_check.
