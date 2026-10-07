From Stdlib Require Import List Bool ZArith Lia.
From compcert.lib Require Import Maps Integers Coqlib.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight Ctypes ClightBigstep.
From Guard Require Import ClightCondition ClightTempFrame ClightCountedLoop ClightNoWrap
  ClightFrontendLoopProtocol ClightRectangularLoops ClightRegionProgress ClightTempFootprint.
From GuardMemory Require Import GuardMemoryAffineSourceExpressions.
From GuardAffineNest Require Import AffineNestSyntax AffineNestExit AffineNestShadowExit AffineNestProbe
  AffineNestFirstLeaf AffineNestPackageGuard AffineNestDomainGuard AffineNestPackageWords
  AffineNestGuardPackage AffineNestLeafModel AffineNestWords.
From GuardInterface Require Import ClightNestedConstantSite ClightNestedConstantModel
  ClightLoadedBoundSyntax ClightConstantBoundModel ClightFixedTempPatch
  ClightNestedConstantSiteFacts ClightQuietDeterminacy.
Import ListNotations.
Set Implicit Arguments.
Local Open Scope Z_scope.

Definition ncs_component_exit_patch shape :=
  [(ncs_component_helper shape,Vint(Int.repr(ncs_upper shape)));
   (ncs_iterator shape,Vint(Int.repr(ncs_upper shape)))].
Definition ncs_row_exit_patch shape child :=
  (ncs_child_helper shape,Vint child)::ncs_component_exit_patch shape++[(ncs_column shape,Vint child)].
Definition ncs_compact_exit_temps shape temps :=
  PTree.set(ncs_row shape)(Vint(temp_word(ncs_root_cache shape)temps))
    (fixed_temp_patch(ncs_row_exit_patch shape(temp_word(ncs_child_cache shape)temps))temps).
Definition ncs_compact_exit_code shape :=
  Ssequence(Sset(ncs_child_helper shape)(Etempvar(ncs_child_cache shape)type_int32s))
    (Ssequence(Sset(ncs_component_helper shape)(Econst_int(Int.repr(ncs_upper shape))type_int32s))
      (Ssequence(Sset(ncs_iterator shape)(Econst_int(Int.repr(ncs_upper shape))type_int32s))
        (Ssequence(Sset(ncs_column shape)(Etempvar(ncs_child_cache shape)type_int32s))
          (Sset(ncs_row shape)(Etempvar(ncs_root_cache shape)type_int32s))))).

Section CLIENT.
Variables source : statement.
Variables parameters live : list ident.
Variable proposal : GuardAffineNest.AffineNestGuardPackage.affine_guard_proposal.
Variable shape : nested_constant_shape.
Variable site : nested_constant_site source parameters live proposal shape.

Ltac names_fresh :=
  pose proof(ncs_original_unique site) as FRESH;
  cbv [ncs_names ncs_coordinates ncs_caches ncs_helpers app] in FRESH;
  repeat match goal with H:NoDup(_::_) |- _ => apply NoDup_cons_iff in H as [? H] end;
  cbn [List.In map fst ncs_component_exit_patch ncs_row_exit_patch app] in *;
  intuition congruence.

Lemma ncs_component_patch_private identifier :
  In identifier[ncs_column shape;ncs_child_helper shape;ncs_child_cache shape] ->
  ~In identifier(map fst(ncs_component_exit_patch shape)).
Proof. names_fresh. Qed.
Lemma ncs_row_patch_private child identifier :
  In identifier[ncs_row shape;ncs_root_cache shape;ncs_child_cache shape] ->
  ~In identifier(map fst(ncs_row_exit_patch shape child)).
Proof. names_fresh. Qed.

Theorem ncs_component_shadow_execution fe ge locals temps memory :
  exec_stmt fe ge locals temps memory
    (constant_affine_body_model(ncs_iterator shape)(ncs_component_helper shape)(ncs_upper shape)Sskip)
    E0(fixed_temp_patch(ncs_component_exit_patch shape)temps) memory Out_normal.
Proof.
  assert(DISTINCT:ncs_iterator shape<>ncs_component_helper shape) by names_fresh.
  set(word:=Int.repr(ncs_upper shape)); set(upper:=Int.signed word).
  assert(ACTIVE:0<upper).
  { unfold upper,word; pose proof(ncs_literal_positive site) as POS.
    unfold Int.lt in POS; destruct(zlt(Int.signed Int.zero)(Int.signed(Int.repr(ncs_upper shape))));
      [rewrite Int.signed_zero in l; exact l|discriminate]. }
  assert(RANGE:signed_range upper) by(unfold upper,signed_range; pose proof(Int.signed_range word); lia).
  set(prepared:=PTree.set(ncs_iterator shape)(Vint Int.zero)
    (PTree.set(ncs_component_helper shape)(Vint word)temps)).
  assert(LOOP:exec_stmt fe ge locals prepared memory
    (frontend_counted_loop(ncs_iterator shape)(ncs_component_helper shape)Sskip)
    E0(PTree.set(ncs_iterator shape)(Vint word)prepared) memory Out_normal).
  { replace word with(Int.repr upper) by(unfold upper; apply Int.repr_signed).
    apply(@patched_frontend_control_execution fe ge locals(ncs_iterator shape)(ncs_component_helper shape)Sskip
      [](fun _=>True) DISTINCT ltac:(cbn; tauto) ltac:(cbn; tauto)
      ltac:(intros; constructor) ltac:(intros; exact I) ltac:(intros; exact I)
      0 upper prepared memory ACTIVE ltac:(unfold signed_range; pose proof Int.min_signed_neg; pose proof Int.max_signed_pos; lia)
      RANGE I ltac:(apply PTree.gss) ltac:(unfold prepared; rewrite PTree.gso by congruence;
        unfold upper; rewrite Int.repr_signed; apply PTree.gss)). }
  unfold constant_affine_body_model,rectangle_reset,ncs_component_exit_patch; cbn [fixed_temp_patch].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)
    (le1:=PTree.set(ncs_component_helper shape)(Vint word)temps).
  - constructor; unfold word; apply memory_source_affine_evaluation with(valuation:=fun _=>0);
      intros identifier MEMBER; contradiction.
  -
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|].
  unfold prepared in LOOP; rewrite PTree.set2 in LOOP; exact LOOP.
Qed.

Theorem ncs_row_shadow_execution fe ge locals temps memory child :
  temps!(ncs_child_cache shape)=Some(Vint child) -> 0<Int.signed child ->
  exec_stmt fe ge locals temps memory
    (cached_child_model(ncs_column shape)(ncs_child_cache shape)(ncs_child_helper shape)
      (constant_affine_body_model(ncs_iterator shape)(ncs_component_helper shape)(ncs_upper shape)Sskip))
    E0(fixed_temp_patch(ncs_row_exit_patch shape child)temps) memory Out_normal.
Proof.
  intros CACHE ACTIVE.
  assert(DISTINCT:ncs_column shape<>ncs_child_helper shape) by names_fresh.
  set(prepared:=PTree.set(ncs_column shape)(Vint Int.zero)(PTree.set(ncs_child_helper shape)(Vint child)temps)).
  assert(RANGE:signed_range(Int.signed child)) by(unfold signed_range; pose proof(Int.signed_range child); lia).
  assert(LOOP:exec_stmt fe ge locals prepared memory
    (frontend_counted_loop(ncs_column shape)(ncs_child_helper shape)
      (constant_affine_body_model(ncs_iterator shape)(ncs_component_helper shape)(ncs_upper shape)Sskip))
    E0(PTree.set(ncs_column shape)(Vint child)(fixed_temp_patch(ncs_component_exit_patch shape)prepared)) memory Out_normal).
  { replace child with(Int.repr(Int.signed child)) by(apply Int.repr_signed).
    eapply patched_frontend_control_execution with(invariant:=fun _=>True)(x:=0).
    - exact DISTINCT.
    - apply ncs_component_patch_private; left; reflexivity.
    - apply ncs_component_patch_private; right; left; reflexivity.
    - intros; apply ncs_component_shadow_execution.
    - intros; exact I.
    - intros; exact I.
    - exact ACTIVE.
    - unfold signed_range; pose proof Int.min_signed_neg; pose proof Int.max_signed_pos; lia.
    - exact RANGE.
    - exact I.
    - apply PTree.gss.
    - unfold prepared; rewrite PTree.gso by congruence; rewrite Int.repr_signed; apply PTree.gss. }
  unfold cached_child_model,rectangle_reset.
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor; exact CACHE|].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|].
  unfold prepared in LOOP; rewrite fixed_temp_patch_commute in LOOP.
  - rewrite PTree.set2 in LOOP; exact LOOP.
  - apply ncs_component_patch_private; left; reflexivity.
Qed.

Theorem ncs_uniform_shadow_execution fe ge locals temps memory row root child :
  temps!(ncs_row shape)=Some(Vint row) -> temps!(ncs_root_cache shape)=Some(Vint root) ->
  temps!(ncs_child_cache shape)=Some(Vint child) ->
  Int.signed row<Int.signed root -> 0<Int.signed child ->
  exec_stmt fe ge locals temps memory(affine_shadow_source(ncs_nest shape))
    E0(ncs_compact_exit_temps shape temps) memory Out_normal.
Proof.
  intros ROW ROOT CHILD ACTIVE CHILD_ACTIVE.
  assert(DISTINCT:ncs_row shape<>ncs_root_cache shape) by names_fresh.
  assert(ROW_CHILD:ncs_row shape<>ncs_child_cache shape) by names_fresh.
  assert(PATCH_FRAME:forall current,(fixed_temp_patch(ncs_row_exit_patch shape child)current)!(ncs_child_cache shape)=
    current!(ncs_child_cache shape)).
  { intro current; rewrite fixed_temp_patch_lookup,fixed_patch_value_absent; [reflexivity|].
    apply ncs_row_patch_private; right; right; left; reflexivity. }
  unfold ncs_compact_exit_temps,temp_word; rewrite ROOT,CHILD.
  change(exec_stmt fe ge locals temps memory(frontend_counted_loop(ncs_row shape)(ncs_root_cache shape)
    (cached_child_model(ncs_column shape)(ncs_child_cache shape)(ncs_child_helper shape)
      (constant_affine_body_model(ncs_iterator shape)(ncs_component_helper shape)(ncs_upper shape)Sskip)))
    E0(PTree.set(ncs_row shape)(Vint root)(fixed_temp_patch(ncs_row_exit_patch shape child)temps))memory Out_normal).
  replace root with(Int.repr(Int.signed root)) by(apply Int.repr_signed).
  eapply patched_frontend_control_execution with(invariant:=fun current=>current!(ncs_child_cache shape)=Some(Vint child))
    (x:=Int.signed row).
  - exact DISTINCT.
  - apply ncs_row_patch_private; left; reflexivity.
  - apply ncs_row_patch_private; right; left; reflexivity.
  - intros current current_memory INV; apply ncs_row_shadow_execution; assumption.
  - intros current INV; rewrite PATCH_FRAME; exact INV.
  - intros current word INV; rewrite PTree.gso by congruence; exact INV.
  - exact ACTIVE.
  - unfold signed_range; pose proof(Int.signed_range row); lia.
  - unfold signed_range; pose proof(Int.signed_range root); lia.
  - exact CHILD.
  - rewrite Int.repr_signed; exact ROW.
  - rewrite Int.repr_signed; exact ROOT.
Qed.

Theorem ncs_compact_exit_execution fe ge locals temps memory root child :
  temps!(ncs_root_cache shape)=Some(Vint root) -> temps!(ncs_child_cache shape)=Some(Vint child) ->
  exec_stmt fe ge locals temps memory(ncs_compact_exit_code shape)
    E0(ncs_compact_exit_temps shape temps) memory Out_normal.
Proof.
  intros ROOT CHILD; unfold ncs_compact_exit_code,ncs_compact_exit_temps,temp_word;
    rewrite ROOT,CHILD; unfold ncs_row_exit_patch,ncs_component_exit_patch; cbn [fixed_temp_patch app].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor; exact CHILD|].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0); [constructor; constructor|].
  eapply exec_Sseq_1 with(t1:=E0)(t2:=E0).
  - constructor; constructor; rewrite !PTree.gso by names_fresh; exact CHILD.
  - constructor; constructor; rewrite !PTree.gso by names_fresh; exact ROOT.
Qed.

Lemma ncs_shadow_quiet : quiet_statement(affine_shadow_source(ncs_nest shape))=true.
Proof. reflexivity. Qed.

Theorem ncs_compact_source_exit fe ge locals temps memory after final row root child :
  temps!(ncs_row shape)=Some(Vint row) -> temps!(ncs_root_cache shape)=Some(Vint root) ->
  temps!(ncs_child_cache shape)=Some(Vint child) ->
  Int.signed row<Int.signed root -> 0<Int.signed child ->
  exec_stmt fe ge locals temps memory(ncs_model shape) E0 after final Out_normal ->
  ncs_compact_exit_temps shape temps=after.
Proof.
  intros ROW ROOT CHILD ACTIVE CHILD_ACTIVE MODEL.
  pose proof(affine_package_nest(ncs_package site)) as NEST.
  pose proof(described_affine_shapes(affine_package_description(ncs_package site))) as SHAPES.
  rewrite NEST,(ncs_model_exact site) in SHAPES.
  pose proof(@affine_nest_fresh_controls _ (described_affine_fresh(affine_package_description(ncs_package site)))) as FRESH.
  rewrite NEST,(ncs_model_exact site) in FRESH.
  assert(SHADOW:exec_stmt fe ge locals temps memory(affine_shadow_source(ncs_nest shape)) E0 after memory Out_normal).
  { apply affine_source_shadow_exit with(memory:=memory)(final:=final).
    - exact SHAPES.
    - exact FRESH.
    - rewrite <-(ncs_model_exact site); exact(affine_leaf_normal(affine_package_leaf(ncs_package site))).
    - rewrite <-(ncs_model_exact site); exact(affine_leaf_quiet(affine_package_leaf(ncs_package site))).
    - rewrite <-(ncs_model_exact site); exact(affine_leaf_writes(affine_package_leaf(ncs_package site))).
    - exact MODEL. }
  pose proof(@ncs_uniform_shadow_execution fe ge locals temps memory row root child ROW ROOT CHILD ACTIVE CHILD_ACTIVE) as COMPACT.
  exact(proj1(proj2(@quiet_execution_determinate fe ge locals temps memory _ _ _ _ _ COMPACT
    ncs_shadow_quiet _ _ _ _ SHADOW))).
Qed.

Theorem ncs_compact_accepted_inputs fe ge locals temps memory after final :
  affine_package_guard_flag parameters proposal(Entry ge locals temps memory)=true ->
  exec_stmt fe ge locals temps memory(ncs_model shape) E0 after final Out_normal ->
  exists row root child,
    temps!(ncs_row shape)=Some(Vint row) /\ temps!(ncs_root_cache shape)=Some(Vint root) /\
    temps!(ncs_child_cache shape)=Some(Vint child) /\
    Int.signed row<Int.signed root /\ 0<Int.signed child.
Proof.
  intros ACCEPT MODEL.
  destruct(@affine_package_root_words _ _ _ _ (ncs_package site) fe ge locals temps memory after final MODEL)
    as [[row ROW][root ROOT]].
  destruct(ncs_site_root_ids site) as [ROW_ID ROOT_ID]; rewrite ROW_ID in ROW; rewrite ROOT_ID in ROOT.
  pose proof(@affine_package_accepted_word_view _ _ _ _ (ncs_package site)
    fe ge locals temps memory after final ACCEPT MODEL) as WORDS.
  assert(CHILD:temps!(ncs_child_cache shape)=Some(Vint(Int.repr(affine_word_valuation temps(ncs_child_cache shape))))).
  { apply WORDS; apply(ncs_cache_parameters site); right; left; reflexivity. }
  exists row,root,(Int.repr(affine_word_valuation temps(ncs_child_cache shape))); repeat split; try assumption.
  all: unfold affine_package_guard_flag,affine_domain_guard_flag in ACCEPT;
    apply andb_true_iff in ACCEPT as [FIRST NUMERIC]; cbn [entry_temps] in FIRST;
    rewrite(ncs_model_exact site) in FIRST; apply affine_first_path_flag_exact in FIRST;
    unfold ncs_nest,nested_constant_model_nest in FIRST;
    cbn [affine_first_path_active affine_first_child_temps memory_source_affine_math] in FIRST.
  - destruct FIRST as [ACTIVE _]; unfold temp_word in ACTIVE; rewrite ROW,ROOT in ACTIVE; exact ACTIVE.
  - destruct FIRST as [_ [ACTIVE _]].
    unfold temp_word in ACTIVE; rewrite PTree.gss in ACTIVE; rewrite PTree.gso in ACTIVE by names_fresh;
      rewrite PTree.gss,Int.signed_zero in ACTIVE; exact ACTIVE.
Qed.

Theorem ncs_compact_exit_frame before after :
  temp_agree(ncs_ports source parameters live shape) before after ->
  temp_agree(ncs_ports source parameters live shape)
    (ncs_compact_exit_temps shape before)(ncs_compact_exit_temps shape after).
Proof.
  intro FRAME.
  assert(CACHES:forall cache,In cache(ncs_caches shape) -> after!cache=before!cache).
  { intros cache MEMBER; apply FRAME; unfold ncs_ports; apply in_or_app; left;
      apply(ncs_cache_parameters site); exact MEMBER. }
  unfold ncs_compact_exit_temps,temp_word;
    rewrite(CACHES _ ltac:(left; reflexivity)),(CACHES _ ltac:(right; left; reflexivity)).
  intros identifier MEMBER; rewrite !PTree.gsspec; destruct(peq identifier(ncs_row shape)); [reflexivity|].
  exact(@fixed_temp_patch_agree _ (ncs_ports source parameters live shape) before after FRAME identifier MEMBER).
Qed.
End CLIENT.

Print Assumptions ncs_component_shadow_execution.
Print Assumptions ncs_row_shadow_execution.
Print Assumptions ncs_uniform_shadow_execution.
Print Assumptions ncs_compact_exit_execution.
Print Assumptions ncs_compact_source_exit.
Print Assumptions ncs_compact_accepted_inputs.
Print Assumptions ncs_compact_exit_frame.
