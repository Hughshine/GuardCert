From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightCountedLoop ClightCountedProtocol
  ClightLoopExecution ClightRectangularLoops ClightRectangularStore CompCertMemoryActions.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryWindowCells GuardMemoryNaryCompute GuardMemoryNaryAffineAccess
  GuardMemoryPointerCompute GuardMemoryPointerNaryAccess GuardMemoryPointerAccess GuardMemoryBufferOffsets
  GuardMemoryAffineSourceExpressions GuardMemoryAffineSourceValuation GuardMemoryBooleanScan GuardMemoryIntervalBox GuardMemoryLoops.
From GuardAffineNest Require Import AffineNestSyntax AffineNestLeafModel AffineNestScanModel AffineNestScanSyntax
  AffineNestMathDomain AffineNestValuation AffineNestLoopEncoding AffineNestLeafDecode AffineNestSourceDecode AffineNestExit.
From GuardInterface Require Import ClightConstantBoundModel ClightConstantBodyJointScan ClightAffineJointObservation
  ClightNestedIndexedObservers ClightSignedIndexedOffsetHeader ClightLoadedBoundSyntax ClightExpressionHeaderCapture
  ClightSignedExpressionProgress ClightStrictLoopProgress ClightDualLoadedUnitSyntax ClightLoadedAffineScanAcceptExample ClightStorePermissions.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** The actual Figure 2 adapted leaf: output[(row*16+column)*5+component]
    = row+column+component. This fixture covers one reached five-store BODY,
    not the enclosing loaded loops or a new whole-program compiler. *)
Definition cjs_address := MemorySourceAdd
  (MemorySourceScale 5(MemorySourceAdd(MemorySourceScale 16(MemorySourceTemp 1%positive))(MemorySourceTemp 2%positive)))
  (MemorySourceTemp 3%positive).
Definition cjs_value := MemorySourceAdd(MemorySourceAdd(MemorySourceTemp 1%positive)(MemorySourceTemp 2%positive))
  (MemorySourceTemp 3%positive).
Definition cjs_access := MemoryNaryAccess 10%positive(RectangleShape 5120 1 1 0) cjs_address([80;5;1],0).
Definition cjs_operation := MemoryNaryCompute cjs_access []
  (AddValue(AddValue(ParameterValue 0)(ParameterValue 1))(ParameterValue 2))(memory_source_affine_code cjs_value).
Definition cjs_leaf := memory_pointer_compute_statement cjs_operation.
Definition cjs_nest := AffineSourceAxis 3%positive 50%positive(MemorySourceConstant 5) cjs_leaf(AffineSourceLeaf cjs_leaf).
Definition cjs_bounds := [(0,1);(0,1);(0,5)].
Definition cjs_source := constant_body_source 3%positive(Int.repr 5) cjs_leaf.
Definition cjs_leaf_checked := match check_affine_leaf cjs_leaf cjs_bounds 0 5
  [1%positive;2%positive;3%positive] [] [10%positive] [cjs_operation] with Some _=>true|None=>false end.
Example figure2_five_store_leaf_checked : cjs_leaf_checked=true.
Proof. vm_compute; reflexivity. Qed.
Definition cjs_certificate : affine_leaf_certificate cjs_leaf cjs_bounds 0 5
  [1%positive;2%positive;3%positive] [] [10%positive] [cjs_operation].
Proof.
  pose proof figure2_five_store_leaf_checked as CHECK; unfold cjs_leaf_checked in CHECK.
  destruct(check_affine_leaf cjs_leaf cjs_bounds 0 5 [1%positive;2%positive;3%positive] [] [10%positive] [cjs_operation]);
    [assumption|discriminate].
Defined.
Definition cjs_valuation component identifier := if Pos.eqb identifier 3%positive then component else 0.

Lemma cjs_store_execution fe ge locals temps memory block base component final :
  0<=component<5 -> temps!1%positive=Some(Vint Int.zero) -> temps!2%positive=Some(Vint Int.zero) ->
  temps!3%positive=Some(Vint(Int.repr component)) -> temps!10%positive=Some(Vptr block base) ->
  Mem.store Mint32 memory block(memory_pointer_buffer_offset base component)(Vint(Int.repr component))=Some final ->
  exec_stmt fe ge locals temps memory cjs_leaf E0 temps final Out_normal.
Proof.
  intros RANGE ROW COLUMN COMPONENT POINTER STORE.
  assert (SIGNED : signed_range component) by(unfold signed_range; change(-2147483648<=component<=2147483647); lia).
  assert (WORDS : forall identifier,In identifier[1%positive;2%positive;3%positive] ->
    temps!identifier=Some(Vint(Int.repr(cjs_valuation component identifier)))).
  { intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[SAME|[SAME|[]]]];
      subst identifier; [exact ROW|exact COLUMN|exact COMPONENT]. }
  assert (INDEX : eval_expr ge locals temps memory(memory_source_affine_code cjs_address)(Vint(Int.repr component))).
  { replace component with(memory_source_affine_math(cjs_valuation component)cjs_address) by reflexivity.
    apply memory_source_affine_evaluation; intros identifier MEMBER; apply WORDS.
    cbn [cjs_address memory_source_affine_reads app] in MEMBER; exact MEMBER. }
  assert (VALUE : eval_expr ge locals temps memory(memory_source_affine_code cjs_value)(Vint(Int.repr component))).
  { replace component with(memory_source_affine_math(cjs_valuation component)cjs_value) by reflexivity.
    apply memory_source_affine_evaluation; intros identifier MEMBER; apply WORDS.
    cbn [cjs_value memory_source_affine_reads app] in MEMBER; exact MEMBER. }
  unfold cjs_leaf,memory_pointer_compute_statement; eapply exec_Sassign with(loc:=block)
    (ofs:=Ptrofs.add base(Ptrofs.repr(4*component)))(bf:=Full)(v:=Vint(Int.repr component))(v2:=Vint(Int.repr component)).
  - unfold memory_pointer_nary_code; apply memory_pointer_lvalue_evaluation;
      [exact POINTER|apply memory_source_affine_type|exact INDEX|exact SIGNED].
  - exact VALUE.
  - reflexivity.
  - apply assign_loc_value with(chunk:=Mint32); [reflexivity|].
    cbn [Mem.storev]; rewrite memory_pointer_buffer_address.
    pose proof(@memory_pointer_store_end memory final block base component(Vint(Int.repr component)) STORE) as END.
    destruct(zle _ _); [exact STORE|lia].
Qed.

Lemma cjs_original_tail_execution count : forall fe ge locals temps memory block base component,
  0<=component -> component+Z.of_nat count=5 ->
  temps!1%positive=Some(Vint Int.zero) -> temps!2%positive=Some(Vint Int.zero) ->
  temps!3%positive=Some(Vint(Int.repr component)) -> temps!10%positive=Some(Vptr block base) ->
  (forall point,0<=point<5 -> Mem.valid_access memory Mint32 block(memory_pointer_buffer_offset base point) Writable) ->
  exists after final,
    exec_stmt fe ge locals temps memory
      (strict_frontend_loop 3%positive(signed_expression_test 3%positive(Econst_int(Int.repr 5)type_int32s)) cjs_leaf)
      E0 after final Out_normal.
Proof.
  induction count as [|count IH]; intros fe ge locals temps memory block base component NONNEG COUNT ROW COLUMN COMPONENT POINTER ACCESS.
  - cbn in COUNT; replace component with 5 in * by lia; exists temps,memory.
    apply signed_expression_zero_trip_execution; change false with(Int.lt(Int.repr 5)(Int.repr 5)).
    apply signed_expression_test_eval; [reflexivity|exact COMPONENT|constructor].
  - assert (RANGE : 0<=component<5) by(rewrite Nat2Z.inj_succ in COUNT; lia).
    assert (SIGNED : signed_range component) by(unfold signed_range; change(-2147483648<=component<=2147483647); lia).
    destruct(Mem.valid_access_store _ _ _ _ (Vint(Int.repr component))(ACCESS component RANGE)) as [middle STORE].
    destruct(IH fe ge locals(PTree.set 3%positive(Vint(Int.repr(component+1))) temps) middle block base(component+1))
      as [after [final REST]].
    + lia.
    + rewrite Nat2Z.inj_succ in COUNT; lia.
    + rewrite PTree.gso by discriminate; exact ROW.
    + rewrite PTree.gso by discriminate; exact COLUMN.
    + apply PTree.gss.
    + rewrite PTree.gso by discriminate; exact POINTER.
    + intros point POINT; eapply Mem.store_valid_access_1; [exact STORE|apply ACCESS; exact POINT].
    + exists after,final; eapply strict_iteration_encode with(body_temps:=temps)(body_memory:=middle).
      * assert (FLAG : Int.lt(Int.repr component)(Int.repr 5)=true).
        { unfold Int.lt; rewrite Int.signed_repr by exact SIGNED.
          change(Int.signed(Int.repr 5)) with 5; destruct(zlt component 5); [reflexivity|lia]. }
        rewrite <-FLAG; apply signed_expression_test_eval; [reflexivity|exact COMPONENT|constructor].
      * exists(Int.repr component); split; [exact COMPONENT|rewrite Int.signed_repr by exact SIGNED; change Int.max_signed with 2147483647; lia].
      * eapply cjs_store_execution; eassumption.
      * rewrite(@counter_increment_small 3%positive temps component COMPONENT); exact REST.
Qed.

Theorem figure2_original_five_store_body fe ge locals temps memory block base :
  temps!1%positive=Some(Vint Int.zero) -> temps!2%positive=Some(Vint Int.zero) ->
  temps!10%positive=Some(Vptr block base) ->
  (forall point,0<=point<5 -> Mem.valid_access memory Mint32 block(memory_pointer_buffer_offset base point) Writable) ->
  exists after final,exec_stmt fe ge locals temps memory cjs_source E0 after final Out_normal.
Proof.
  intros ROW COLUMN POINTER ACCESS.
  destruct(@cjs_original_tail_execution 5%nat fe ge locals(PTree.set 3%positive(Vint Int.zero) temps) memory block base 0)
    as [after [final LOOP]]; try lia.
  - rewrite PTree.gso by discriminate; exact ROW.
  - rewrite PTree.gso by discriminate; exact COLUMN.
  - apply PTree.gss.
  - rewrite PTree.gso by discriminate; exact POINTER.
  - exact ACCESS.
  - exists after,final; unfold cjs_source,constant_body_source.
    eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|exact LOOP].
Qed.

Definition cjs_allocated := fst(Mem.alloc Mem.empty 0 40).
Lemma cjs_allocated_access offset : 0<=offset -> offset+4<=40 -> (4|offset) ->
  Mem.valid_access cjs_allocated Mint32 1%positive offset Writable.
Proof.
  intros LOW HIGH ALIGN; eapply Mem.valid_access_implies with(p1:=Freeable); [|constructor].
  eapply Mem.valid_access_alloc_same with(m1:=Mem.empty)(lo:=0)(hi:=40);
    [reflexivity|exact LOW|exact HIGH|exact ALIGN].
Qed.
Definition cjs_root_state : {memory | Mem.store Mint32 cjs_allocated 1%positive 0(Vint Int.zero)=Some memory}.
Proof. apply Mem.valid_access_store,cjs_allocated_access; [lia|lia|exists 0; reflexivity]. Defined.
Definition cjs_root := proj1_sig cjs_root_state.
Definition cjs_memory_state : {memory | Mem.store Mint32 cjs_root 1%positive 4(Vint Int.zero)=Some memory}.
Proof.
  apply Mem.valid_access_store; eapply Mem.store_valid_access_1; [exact(proj2_sig cjs_root_state)|].
  apply cjs_allocated_access; [lia|lia|exists 1; reflexivity].
Defined.
Definition cjs_memory := proj1_sig cjs_memory_state.
Definition cjs_temps base := PTree.set 203%positive(Vint Int.one)
  (PTree.set 50%positive(Vint(Int.repr 5))(PTree.set 10%positive(Vptr 1%positive(Ptrofs.repr base))
    (PTree.set 11%positive(Vptr 1%positive Ptrofs.zero)
      (PTree.set 1%positive(Vint Int.zero)(PTree.set 2%positive(Vint Int.zero)(PTree.empty val)))))).
Definition cjs_observers := nested_indexed_word_observers 11%positive Int.one 1%positive Ptrofs.zero Int.zero Int.zero.
Definition cjs_public := [1%positive;2%positive;10%positive;11%positive;50%positive].
Definition cjs_controls identifier := if Pos.eqb identifier 3%positive then 201%positive else 202%positive.
Definition cjs_values identifier := if Pos.eqb identifier 3%positive then 201%positive else identifier.
Definition cjs_code := match affine_lower_nest cjs_nest [1%positive;2%positive] [] (L.Constant 0)
  (affine_checked_leaf_code [1%positive;2%positive;3%positive] [] [] [cjs_operation]) with Some code=>code|None=>affine_checked_leaf_code [] [] [] [] end.
Definition cjs_result base := affine_scan_result cjs_nest(cjs_valuation 0) 0
  (affine_joint_observation_result(window_multi_pointer_locations(cjs_temps base) 0 5)cjs_observers[cjs_operation]).
Definition cjs_scan := affine_scan_statement cjs_nest cjs_controls cjs_values(Econst_int Int.zero type_int32s)
  (affine_joint_observation_leaf cjs_observers[cjs_operation]cjs_values 203%positive).

Lemma cjs_original_permissions base : base=0 \/ base=8 -> forall point,0<=point<5 ->
  Mem.valid_access cjs_memory Mint32 1%positive(memory_pointer_buffer_offset(Ptrofs.repr base) point) Writable.
Proof.
  intros BASE point RANGE; unfold memory_pointer_buffer_offset,memory_buffer_offset.
  assert (MODULUS : 40<Ptrofs.modulus) by(vm_compute; reflexivity).
  rewrite Ptrofs.unsigned_repr by(unfold Ptrofs.max_unsigned; lia).
  rewrite Z.mod_small by lia.
  eapply Mem.store_valid_access_1; [exact(proj2_sig cjs_memory_state)|].
  eapply Mem.store_valid_access_1; [exact(proj2_sig cjs_root_state)|].
  apply cjs_allocated_access; [lia|lia|].
  destruct BASE as [ZERO|EIGHT]; subst base; [exists point|exists(2+point)]; ring.
Qed.

Lemma cjs_raw_observation_reads :
  Mem.loadv Mint32 cjs_memory(Vptr 1%positive Ptrofs.zero)=Some(Vint Int.zero) /\
  Mem.loadv Mint32 cjs_memory(Vptr 1%positive(signed_indexed_address Ptrofs.zero Int.one))=Some(Vint Int.zero).
Proof.
  change(Mem.load Mint32 cjs_memory 1%positive 0=Some(Vint Int.zero) /\
    Mem.load Mint32 cjs_memory 1%positive 4=Some(Vint Int.zero)); split.
  - rewrite(@Mem.load_store_other Mint32 cjs_root 1%positive 4(Vint Int.zero)cjs_memory
      (proj2_sig cjs_memory_state) Mint32 1%positive 0) by(right; left; reflexivity).
    rewrite(@Mem.load_store_same Mint32 cjs_allocated 1%positive 0(Vint Int.zero)cjs_root(proj2_sig cjs_root_state)); reflexivity.
  - rewrite(@Mem.load_store_same Mint32 cjs_root 1%positive 4(Vint Int.zero)cjs_memory(proj2_sig cjs_memory_state)); reflexivity.
Qed.
Lemma cjs_observer_receipts ge locals base :
  Forall(word_observer_receipt ge locals(cjs_temps base)cjs_memory)cjs_observers.
Proof.
  destruct cjs_raw_observation_reads as [ROOT CHILD]; constructor.
  - split; [reflexivity|split; [constructor; reflexivity|exact ROOT]].
  - constructor; [|constructor]; split; [reflexivity|split; [apply signed_indexed_pointer_eval; reflexivity|exact CHILD]].
Qed.
Lemma cjs_numeric_domain : affine_math_domain cjs_bounds[1%positive;2%positive;3%positive] cjs_nest(cjs_valuation 0) 0.
Proof.
  split; [unfold signed_range; vm_compute; intuition discriminate|split].
  - unfold signed_range; vm_compute; intuition discriminate.
  - intros component RANGE; change(0<=component<5) in RANGE.
    change(interval_ranges cjs_bounds[0;0;component]); unfold interval_ranges,cjs_bounds.
    constructor; [cbn; lia|constructor; [cbn; lia|constructor; [cbn; lia|constructor]]].
Qed.
Example figure2_joint_scan_alias_refused : cjs_result 0=false.
Proof. vm_compute; reflexivity. Qed.
Example figure2_joint_scan_same_block_apart_accepted : cjs_result 8=true.
Proof. vm_compute; reflexivity. Qed.

Theorem figure2_joint_five_store_scan_execution fe ge locals base : base=0 \/ base=8 ->
  exists checked,
    exec_stmt fe ge locals(cjs_temps base)cjs_memory cjs_scan E0 checked cjs_memory Out_normal /\
    temp_agree cjs_public(cjs_temps base)checked /\
    checked!203%positive=Some(memory_boolean_word(cjs_result base)).
Proof.
  intro BASE.
  destruct(@figure2_original_five_store_body fe ge locals(cjs_temps base)cjs_memory 1%positive(Ptrofs.repr base)
    eq_refl eq_refl eq_refl(cjs_original_permissions BASE)) as [after [final SOURCE]].
  unfold cjs_scan,cjs_result; rewrite <-andb_true_l with(b:=affine_scan_result _ _ _ _).
  eapply constant_body_joint_scan_execution with(certificate:=cjs_certificate)(fe:=fe)(ge:=ge)(locals:=locals)
    (initial:=cjs_temps base)(temps:=cjs_temps base)(memory:=cjs_memory)(after:=after)(final:=final)
    (code:=cjs_code)(written:=[])(coordinates:=[1%positive;2%positive;3%positive])
    (prefix:=[1%positive;2%positive])(parameters:=[])(pointers:=[10%positive])
    (public:=cjs_public)(live:=cjs_public); try reflexivity.
  - split; [reflexivity|exact I].
  - repeat constructor; cbn; intuition congruence.
  - split; [cbn; tauto|exact I].
  - intros identifier MEMBER BAD; vm_compute in MEMBER,BAD; intuition congruence.
  - exact cjs_numeric_domain.
  - intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[SAME|[]]]; subst identifier; reflexivity.
  - apply temp_agree_refl.
  - constructor.
  - cbn; tauto.
  - apply memory_accesses_back_refl.
  - exact SOURCE.
  - intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[]]; subst identifier; cbn; auto.
  - intros observer MEMBER; pose proof(cjs_observer_receipts ge locals base) as RECEIPTS.
    apply Forall_forall with(x:=observer) in RECEIPTS; [exact RECEIPTS|exact MEMBER].
  - intros observer MEMBER; pose proof(@nested_indexed_observers_scope 11%positive Int.one 1%positive Ptrofs.zero
      Int.zero Int.zero cjs_public ltac:(cbn; auto)) as SCOPE.
    apply Forall_forall with(x:=observer) in SCOPE; [exact SCOPE|exact MEMBER].
  - repeat constructor; cbn; intuition congruence.
  - intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[]]; subst identifier; reflexivity.
  - intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[SAME|[]]]; subst identifier;
      split; vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
  - vm_compute; intuition congruence.
  - apply incl_refl.
  - vm_compute; intuition congruence.
  - intros identifier MEMBER; cbn in MEMBER; destruct MEMBER as [SAME|[SAME|[]]]; subst identifier; reflexivity.
  - apply temp_agree_refl.
Qed.

Print Assumptions figure2_five_store_leaf_checked.
Print Assumptions cjs_store_execution.
Print Assumptions cjs_original_tail_execution.
Print Assumptions figure2_original_five_store_body.
Print Assumptions cjs_original_permissions.
Print Assumptions cjs_raw_observation_reads.
Print Assumptions cjs_observer_receipts.
Print Assumptions cjs_numeric_domain.
Print Assumptions figure2_joint_scan_alias_refused.
Print Assumptions figure2_joint_scan_same_block_apart_accepted.
Print Assumptions figure2_joint_five_store_scan_execution.
